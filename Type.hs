{-# LANGUAGE GADTs, DataKinds #-}
-- | Bidirectional typechecking for higher-rank polymorphism
--   Implementation of http://www.mpi-sws.org/~neelk/bidir.pdf
module Type where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as S

import AST
import NameGen
import Pretty

import Debug.Trace

trace' :: (Monad m, Pretty a) => Int -> String -> m a -> m a
trace' indent s x = trace (ind ++ s) $ do
  res <- x
  trace (ind ++ "= " ++ pretty res) (return res)
  where ind = replicate (indent * 3) ' '

-- | Is the type a Monotype?
monotype :: Type a -> Maybe Monotype
monotype typ = case typ of
  TUnit       -> Just TUnit
  TVar v      -> Just $ TVar v
  TForall _ _ -> Nothing
  TExists v   -> Just $ TExists v
  TFun t1 t2  -> TFun <$> monotype t1 <*> monotype t2

-- | Any type is a Polytype since Monotype is a subset of Polytype
polytype :: Type a -> Polytype
polytype typ = case typ of
  TUnit       -> TUnit
  TVar v      -> TVar v
  TForall v t -> TForall v t
  TExists v   -> TExists v
  TFun t1 t2  -> TFun (polytype t1) (polytype t2)

-- | typeSubst A α B = [A/α]B
typeSubst :: Type a -> TVar -> Type a -> Type a
typeSubst t' v typ = case typ of
  TUnit                    -> TUnit
  TVar v'      | v' == v   -> t'
               | otherwise -> TVar v'
  TForall v' t | v' == v   -> TForall v' t
               | otherwise -> TForall v' (typeSubst t' v t)
  TExists v'   | v' == v   -> t'
               | otherwise -> TExists v'
  TFun t1 t2               -> TFun (typeSubst t' v t1) (typeSubst t' v t2)

typeSubsts :: [(Type a, TVar)] -> Type a -> Type a
typeSubsts = flip (foldr (uncurry typeSubst))

-- | subst e' x e = [e'/x]e
subst :: Expr -> Var -> Expr -> Expr
subst e' x expr = case expr of
  EVar x'   | x' == x   -> e'
            | otherwise -> EVar x'
  EUnit                 -> EUnit
  EAbs x' e | x' == x   -> EAbs x' e
            | otherwise -> EAbs x' (subst e' x e)
  EApp e1 e2            -> EApp (subst e' x e1) (subst e' x e2)
  EAnno e t             -> EAnno (subst e' x e) t

-- | The free type variables in a type
freeTVars :: Type a -> Set TVar
freeTVars typ = case typ of
  TUnit       -> mempty
  TVar v      -> S.singleton v
  TForall v t -> S.delete v $ freeTVars t
  TExists v   -> S.singleton v
  TFun t1 t2  -> freeTVars t1 `mappend` freeTVars t2

contextExistentials :: Context -> [TVar]
contextExistentials (Context gamma) = aux =<< gamma
  where aux (CExists alpha)         = [alpha]
        aux (CExistsSolved alpha _) = [alpha]
        aux _                       = []

contextUnsolved :: Context -> [TVar]
contextUnsolved (Context gamma) = [alpha | CExists alpha <- gamma]

contextVars :: Context -> [Var]
contextVars (Context gamma) = [x | CVar x _ <- gamma]

contextForalls :: Context -> [TVar]
contextForalls (Context gamma) = [alpha | CForall alpha <- gamma]

contextMarkers :: Context -> [TVar]
contextMarkers (Context gamma) = [alpha | CMarker alpha <- gamma]

-- | Well-formedness of contexts
--   contextwf Γ <=> Γ ctx
contextwf :: Context -> Bool
contextwf (Context gamma) = case gamma of
  -- EmptyCtx
  [] -> True
  c:cs -> let gamma' = Context cs in contextwf gamma' && case c of
    -- UvarCtx
    CForall alpha -> notElem alpha (contextForalls gamma')
    -- VarCtx
    CVar x a -> notElem x (contextVars gamma') && typewf gamma' a
    -- EvarCtx
    CExists alpha -> notElem alpha (contextExistentials gamma')
    -- SolvedEvarCtx
    CExistsSolved alpha tau -> notElem alpha (contextExistentials gamma')
                            && typewf gamma' tau
    -- MarkerCtx
    CMarker alpha -> notElem alpha (contextMarkers gamma')
                  && notElem alpha (contextExistentials gamma')

-- | Well-formedness of types
--   typewf Γ A <=> Γ |- A
typewf :: Context -> Type a -> Bool
typewf gamma typ = case typ of
  -- UvarWF
  TVar alpha -> elem alpha (contextForalls gamma)
  -- UnitWF
  TUnit -> True
  -- ArrowWF
  TFun a b -> typewf gamma a && typewf gamma b
  -- ForallWF
  TForall alpha a -> typewf (gamma >: CForall alpha) a
  -- EvarWF and SolvedEvarWF
  TExists alpha -> elem alpha (contextExistentials gamma)

-- Assert-like functionality to make sure that contexts and types are
-- well-formed
checkwf :: Context -> x -> x
checkwf gamma x | contextwf gamma = x
                | otherwise       = error $ "Malformed context: "
                                  ++ pretty gamma

checkwftype :: Context -> Polytype -> x -> x
checkwftype gamma a x | typewf gamma a = checkwf gamma x
                      | otherwise      = error $ "Malformed type: "
                                       ++ pretty (a, gamma)

-- Some helpers for working with contexts

-- | findSolvedExists (ΓL,α^ = τ,ΓR) α = Just τ
findSolved :: Context -> TVar -> Maybe Monotype
findSolved (Context gamma) v = listToMaybe [t | CExistsSolved v' t <- gamma, v == v']

-- | findVarType (ΓL,x : A,ΓR) x = Just A
findVarType :: Context -> Var -> Maybe Polytype
findVarType (Context gamma) v = listToMaybe [t | CVar v' t <- gamma, v == v']

-- | solveContext (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
solveContext :: Context -> TVar -> Monotype -> Maybe Context
solveContext gamma alpha tau | typewf gammaL tau = Just gamma'
                             | otherwise         = Nothing
  where (gammaL, gammaR) = breakMarker (CExists alpha) gamma
        gamma' = gammaL >++ [CExistsSolved alpha tau] <> gammaR

-- | insertContext (ΓL,c,ΓR) c Θ = ΓL,Θ,ΓR
insertContext :: Context -> ContextElem Incomplete -> Context -> Context
insertContext gamma c theta = gammaL <> theta <> gammaR
  where (gammaL, gammaR) = breakMarker c gamma

-- | applyContext Γ A = [Γ]A
applyContext :: Context -> Polytype -> Polytype
applyContext gamma typ = case typ of
  TUnit       -> TUnit
  TVar v      -> TVar v
  TForall v t -> TForall v (applyContext gamma t)
  TExists v   -> maybe (TExists v) (applyContext gamma . polytype) $ findSolved gamma v
  TFun t1 t2  -> applyContext gamma t1 `TFun` applyContext gamma t2

-- | ordered Γ α β = True <=> Γ[α^][β^]
ordered :: Context -> TVar -> TVar -> Bool
ordered gamma alpha beta =
  let gammaL = dropMarker (CExists beta) gamma
   in elem alpha (contextExistentials gammaL)

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Int -> Context -> Polytype -> Polytype -> NameGen Context
subtype n gamma typ1 typ2 = trace' n ("subtype" ++ pretty (gamma, typ1, typ2)) $ checkwftype gamma typ1 $ checkwftype gamma typ2 $ case (typ1, typ2) of
  -- <:Var
  (TVar alpha, TVar alpha') | alpha == alpha' -> return gamma
  -- <:Unit
  (TUnit, TUnit) -> return gamma
  -- <:Exvar
  (TExists alpha, TExists alpha') | alpha == alpha'
                                  && elem alpha (contextExistentials gamma) ->
    return gamma
  -- <:->
  (TFun a1 a2, TFun b1 b2) -> do
    theta <- subtype (n + 1) gamma b1 a1
    subtype (n + 1) theta (applyContext theta a2) (applyContext theta b2)
  -- <:forallL
  (TForall alpha a, b) -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    dropMarker (CMarker alpha') <$>
      subtype (n + 1) (gamma >++ [CMarker alpha', CExists alpha'])
              (typeSubst (TExists alpha') alpha a)
              b
  -- <:forallR
  (a, TForall alpha b) -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    dropMarker (CForall alpha') <$>
      subtype (n + 1) (gamma >: CForall alpha') a (typeSubst (TVar alpha') alpha b)
  -- <:InstantiateL
  (TExists alpha, a) | elem alpha (contextExistentials gamma)
                    && S.notMember alpha (freeTVars a) ->
    instantiateL (n + 1) gamma alpha a
  -- <:InstantiateR
  (a, TExists alpha) | elem alpha (contextExistentials gamma)
                     && S.notMember alpha (freeTVars a) ->
    instantiateR (n + 1) gamma a alpha
  _ -> error $ "subtype, don't know what to do with: "
                         ++ pretty (gamma, typ1, typ2)

-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Int -> Context -> TVar -> Polytype -> NameGen Context
instantiateL n gamma alpha a = trace' n  ("instantiateL" ++ pretty (gamma, alpha, a)) $ checkwftype gamma a $ checkwftype gamma (TExists alpha) $ case solveContext gamma alpha =<< monotype a of
  -- InstLSolve
  Just gamma' -> return gamma'
  Nothing -> case a of
    -- InstLReach
    TExists beta | ordered gamma alpha beta -> return $ fromJust $ solveContext gamma beta (TExists alpha)
    -- InstLArr
    TFun a1 a2   -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      theta <- instantiateR (n + 1) (insertContext gamma (CExists alpha) $ context
                                  [ CExists alpha2
                                  , CExists alpha1
                                  , CExistsSolved alpha $ TFun (TExists alpha1)
                                                               (TExists alpha2)
                                  ])
                             a1 alpha1
      instantiateL (n + 1) theta alpha2 (applyContext theta a2)
    -- InstLAIIR
    TForall beta b -> do
      -- Do alpha conversion to avoid clashes
      beta' <- freshTVar
      dropMarker (CForall beta') <$>
        instantiateL (n + 1) (gamma >++ [CForall beta']) alpha (typeSubst (TVar beta') beta b)
    _ -> error $ "The impossible happened! instantiateL: "
              ++ pretty (gamma, alpha, a)

-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Int -> Context -> Polytype -> TVar -> NameGen Context
instantiateR n gamma a alpha = trace' n ("instantiateR" ++ pretty (gamma, a, alpha)) $ checkwftype gamma a $ checkwftype gamma (TExists alpha) $ case solveContext gamma alpha =<< monotype a of
  Just gamma' -> return gamma'
  Nothing -> case a of
    -- InstRReach
    TExists beta | ordered gamma alpha beta -> return $ fromJust $ solveContext gamma beta (TExists alpha)
    -- InstRArr
    TFun a1 a2   -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      theta <- instantiateL (n + 1) (insertContext gamma (CExists alpha) $ context
                                  [ CExists alpha2
                                  , CExists alpha1
                                  , CExistsSolved alpha $ TFun (TExists alpha1)
                                                               (TExists alpha2)
                                  ])
                             alpha1 a1
      instantiateR (n + 1) theta (applyContext theta a2) alpha2
    -- InstRAIIL
    TForall beta b -> do
      -- Do alpha conversion to avoid clashes
      beta' <- freshTVar
      dropMarker (CMarker beta') <$>
        instantiateR (n + 1) (gamma >++ [CMarker beta', CExists beta']) (typeSubst (TExists beta') beta b) alpha
    _ -> error $ "The impossible happened! instantiateR: "
              ++ pretty (gamma, a, alpha)

-- | Type checking:
--   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
typecheck :: Int -> Context -> Expr -> Polytype -> NameGen Context
typecheck n gamma expr typ = trace' n ("typecheck" ++ pretty (gamma, expr, typ)) $ checkwftype gamma typ $ case (expr, typ) of
  -- 1I
  (EUnit, TUnit) -> return gamma
  -- ForallI
  (e, TForall alpha a) -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    dropMarker (CForall alpha') <$>
      typecheck (n + 1) (gamma >: CForall alpha') e (typeSubst (TVar alpha') alpha a)
  -- ->I
  (EAbs x e, TFun a b) -> do
    x' <- freshVar
    dropMarker (CVar x' a) <$>
      typecheck (n + 1) (gamma >: CVar x' a) (subst (EVar x') x e) b
  -- Sub
  (e, b) -> do
    (a, theta) <- typesynth (n + 1) gamma e
    subtype (n + 1) theta (applyContext theta a) (applyContext theta b)

-- | Type synthesising:
--   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
typesynth :: Int -> Context -> Expr -> NameGen (Polytype, Context)
typesynth n gamma expr = trace' n ("typesynth" ++ pretty (gamma, expr)) $ checkwf gamma $ case expr of
  -- Var
  EVar x -> return
    ( fromMaybe (error $ "typesynth: not in scope " ++ pretty (expr, gamma))
                (findVarType gamma x)
    , gamma
    )
  -- Anno
  EAnno e a -> do
    delta <- typecheck (n + 1) gamma e a
    return (a, delta)
  -- 1I=>
  EUnit -> return (TUnit, gamma)
  {-
  -- ->I=> Original rule
  EAbs x e -> do
    x'    <- freshVar
    alpha <- freshTVar
    beta  <- freshTVar
    delta <- dropMarker (CVar x' (TExists alpha)) <$>
      typecheck (n + 1) (gamma >++ [CExists alpha, CExists beta, CVar x' (TExists alpha)])
                (subst (EVar x') x e)
                (TExists beta)
    return (TFun (TExists alpha) (TExists beta), delta)
  -- -}
  -- {-
  -- ->I=> Full Damas-Milner type inference
  EAbs x e -> do
    x'    <- freshVar
    alpha <- freshTVar
    beta  <- freshTVar
    (delta, delta')  <- breakMarker (CMarker alpha) <$>
      typecheck (n + 1) (gamma >++ [CMarker alpha, CExists alpha, CExists beta, CVar x' (TExists alpha)])
                (subst (EVar x') x e)
                (TExists beta)
    let tau = applyContext delta' (TFun (TExists alpha) (TExists beta))
    let evars = contextUnsolved delta'
    uvars <- replicateM (length evars) freshTVar
    return (tforalls uvars $ typeSubsts (zip (map TVar uvars) evars) tau, delta)
  -- -}
  -- ->E
  EApp e1 e2 -> do
    (a, theta) <- typesynth (n + 1) gamma e1
    typeapplysynth (n + 1) theta (applyContext theta a) e2

-- | Type application synthesising
--   typeapplysynth Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth :: Int -> Context -> Polytype -> Expr -> NameGen (Polytype, Context)
typeapplysynth n gamma typ e = trace' n ("typeapplysynth" ++ pretty (gamma, typ, e)) $ checkwftype gamma typ $ case typ of
  -- ForallApp
  TForall alpha a -> do
    -- Do alpha conversion to avoid clashes
    alpha' <- freshTVar
    typeapplysynth (n + 1) (gamma >: CExists alpha')
                   (typeSubst (TExists alpha') alpha a)
                   e
  -- alpha^App
  TExists alpha -> do
    alpha1 <- freshTVar
    alpha2 <- freshTVar
    delta <- typecheck (n + 1) (insertContext gamma (CExists alpha) $ context
                          [ CExists alpha2
                          , CExists alpha1
                          , CExistsSolved alpha $ TFun (TExists alpha1) (TExists alpha2)
                          ])
                       e
                       (TExists alpha1)
    return (TExists alpha2, delta)
  -- ->App
  TFun a c -> do
    delta <- typecheck (n + 1) gamma e a
    return (c, delta)

  _ -> error $ "typeapplysynth: don't know what to do with: "
            ++ pretty (gamma, typ, e)

typesynthClosed :: Expr -> (Polytype, Context)
typesynthClosed e = let (a, gamma) = evalNameGen $ typesynth 0 mempty e
                     in (applyContext gamma a, gamma)

-- Examples
eid :: Expr -- (λx. x) : ∀ t. t → t
eid = eabs "x" (var "x") -- -: tforall "t" (tvar "t" --> tvar "t")
-- Impredicative, so doesn't typecheck
ididunit :: Expr -- (λid. id id ()) ((λx. x) : ∀ t. t → t)
ididunit = eabs "id" (((var "id" -: tforall "t" (tvar "t" --> tvar "t"))  $$ var "id") $$ eunit) $$ eid
idunit :: Expr -- (λid. id ()) ((λx. x) : ∀ t. t → t)
idunit = eabs "id" (var "id" $$ eunit) $$ eid
idid :: Expr -- id id
idid = (eid $$ eid) -: tforall "t" (tvar "t" --> tvar "t")
