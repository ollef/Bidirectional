{-# LANGUAGE GADTs #-}
-- | Bidirectional typechecking for higher-rank polymorphism
--   Implementation of http://www.mpi-sws.org/~neelk/bidir.pdf
module Type where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S

import AST
import Context
import NameGen
import Pretty

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Context -> Polytype -> Polytype -> NameGen Context
subtype gamma typ1 typ2 =
  traceNS "subtype" (gamma, typ1, typ2) $
  checkwftype gamma typ1 $ checkwftype gamma typ2 $
    case (typ1, typ2) of
    -- <:Var
    (TVar alpha, TVar alpha') | alpha == alpha' -> return gamma
    -- <:Unit
    (TUnit, TUnit) -> return gamma
    -- <:Exvar
    (TExists alpha, TExists alpha')
      | alpha == alpha' && alpha `elem` existentials gamma -> return gamma
    -- <:->
    (TFun a1 a2, TFun b1 b2) -> do
      theta <- subtype gamma b1 a1
      subtype theta (apply theta a2) (apply theta b2)

    -- <:forallR
    (a, TForall alpha b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CForall alpha') <$>
        subtype (gamma >: CForall alpha') a (typeSubst (TVar alpha') alpha b)
      
    -- <:forallL
    (TForall alpha a, b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CMarker alpha') <$>
        subtype (gamma >++ [CMarker alpha', CExists alpha'])
                (typeSubst (TExists alpha') alpha a)
                b

    -- <:InstantiateL
    (TExists alpha, a) | alpha `elem` existentials gamma
                      && alpha `S.notMember` freeTVars a ->
      instantiateL gamma alpha a
    -- <:InstantiateR
    (a, TExists alpha) | alpha `elem` existentials gamma
                      && alpha `S.notMember` freeTVars a ->
      instantiateR gamma a alpha
    _ -> error $ "subtype, don't know what to do with: "
                           ++ pretty (gamma, typ1, typ2)

-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Context -> TVar -> Polytype -> NameGen Context
instantiateL gamma alpha a =
  traceNS "instantiateL" (gamma, alpha, a) $
  checkwftype gamma a $ checkwftype gamma (TExists alpha) $
  case solve gamma alpha =<< monotype a of
    -- InstLSolve
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstLReach
      TExists beta 
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TExists alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TExists beta)
      -- InstLArr
      TFun a1 a2   -> do
        alpha1 <- freshTVar
        alpha2 <- freshTVar
        theta <- instantiateR (insertAt gamma (CExists alpha) $ context
                                [ CExists alpha2
                                , CExists alpha1
                                , CExistsSolved alpha $ TFun (TExists alpha1)
                                                             (TExists alpha2)
                                ])
                              a1 alpha1
        instantiateL theta alpha2 (apply theta a2)
      -- InstLAIIR
      TForall beta b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        dropMarker (CForall beta') <$>
          instantiateL (gamma >++ [CForall beta'])
                       alpha
                       (typeSubst (TVar beta') beta b)
      _ -> error $ "The impossible happened! instantiateL: "
                ++ pretty (gamma, alpha, a)

-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Context -> Polytype -> TVar -> NameGen Context
instantiateR gamma a alpha =
  traceNS "instantiateR" (gamma, a, alpha) $
  checkwftype gamma a $ checkwftype gamma (TExists alpha) $
  case solve gamma alpha =<< monotype a of
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstRReach
      TExists beta 
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TExists alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TExists beta)
      -- InstRArr
      TFun a1 a2   -> do
        alpha1 <- freshTVar
        alpha2 <- freshTVar
        theta <- instantiateL (insertAt gamma (CExists alpha) $ context
                                 [ CExists alpha2
                                 , CExists alpha1
                                 , CExistsSolved alpha $ TFun (TExists alpha1)
                                                              (TExists alpha2)
                                 ])
                              alpha1
                              a1
        instantiateR theta (apply theta a2) alpha2
      -- InstRAIIL
      TForall beta b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        dropMarker (CMarker beta') <$>
          instantiateR (gamma >++ [CMarker beta', CExists beta'])
                       (typeSubst (TExists beta') beta b)
                       alpha
      _ -> error $ "The impossible happened! instantiateR: "
                ++ pretty (gamma, a, alpha)

-- | Type checking:
--   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
typecheck :: Context -> Expr -> Polytype -> NameGen Context
typecheck gamma expr typ =
  traceNS "typecheck" (gamma, expr, typ) $
  checkwftype gamma typ $ case (expr, typ) of
    -- 1I
    (EUnit, TUnit) -> return gamma
    -- ForallI
    (e, TForall alpha a) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CForall alpha') <$>
        typecheck (gamma >: CForall alpha') e (typeSubst (TVar alpha') alpha a)
    -- ->I
    (EAbs x e, TFun a b) -> do
      x' <- freshVar
      dropMarker (CVar x' a) <$>
        typecheck (gamma >: CVar x' a) (subst (EVar x') x e) b
    -- Sub
    (e, b) -> do
      (a, theta) <- typesynth gamma e
      subtype theta (apply theta a) (apply theta b)

-- | Type synthesising:
--   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
typesynth :: Context -> Expr -> NameGen (Polytype, Context)
typesynth gamma expr = traceNS "typesynth" (gamma, expr) $ checkwf gamma $
  case expr of
    -- Var
    EVar x -> return
      ( fromMaybe (error $ "typesynth: not in scope " ++ pretty (expr, gamma))
                  (findVarType gamma x)
      , gamma
      )
    -- Anno
    EAnno e a -> do
      delta <- typecheck gamma e a
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
        typecheck (gamma >++ [ CExists alpha
                             , CExists beta
                             , CVar x' (TExists alpha)
                             ])
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
        typecheck (gamma >++ [ CMarker alpha
                             , CExists alpha
                             , CExists beta
                             , CVar x' (TExists alpha)
                             ])
                  (subst (EVar x') x e)
                  (TExists beta)
      let tau = apply delta' (TFun (TExists alpha) (TExists beta))
      let evars = unsolved delta'
      uvars <- replicateM (length evars) freshTVar
      return ( tforalls uvars $ typeSubsts (zip (map TVar uvars) evars) tau
             , delta)
    -- -}
    -- ->E
    EApp e1 e2 -> do
      (a, theta) <- typesynth gamma e1
      typeapplysynth theta (apply theta a) e2

-- | Type application synthesising
--   typeapplysynth Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth :: Context -> Polytype -> Expr -> NameGen (Polytype, Context)
typeapplysynth gamma typ e = traceNS "typeapplysynth" (gamma, typ, e) $
  checkwftype gamma typ $
  case typ of
    -- ForallApp
    TForall alpha a -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      typeapplysynth (gamma >: CExists alpha')
                     (typeSubst (TExists alpha') alpha a)
                     e
    -- alpha^App
    TExists alpha -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      delta <- typecheck (insertAt gamma (CExists alpha) $ context
                            [ CExists alpha2
                            , CExists alpha1
                            , CExistsSolved alpha $ TFun (TExists alpha1)
                                                         (TExists alpha2)
                            ])
                         e
                         (TExists alpha1)
      return (TExists alpha2, delta)
    -- ->App
    TFun a c -> do
      delta <- typecheck gamma e a
      return (c, delta)

    _ -> error $ "typeapplysynth: don't know what to do with: "
              ++ pretty (gamma, typ, e)

typesynthClosed :: Expr -> (Polytype, Context)
typesynthClosed e = let (a, gamma) = evalNameGen $ typesynth mempty e
                     in (apply gamma a, gamma)

-- Examples
eid :: Expr -- (λx. x) : ∀ t. t → t
eid = eabs "x" (var "x") -: tforall "t" (tvar "t" --> tvar "t")
-- Impredicative, so doesn't typecheck
ididunit :: Expr -- (λid. id id ()) ((λx. x) : ∀ t. t → t)
ididunit = eabs "id" (((var "id" -: tforall "t" (tvar "t" --> tvar "t"))  $$ var "id") $$ eunit) $$ eid
idunit :: Expr -- (λid. id ()) ((λx. x) : ∀ t. t → t)
idunit = eabs "id" (var "id" $$ eunit) $$ eid
idid :: Expr -- id id
idid = (eid $$ eid) -: tforall "t" (tvar "t" --> tvar "t")
