{-# LANGUAGE GADTs #-}
-- | Pretty printing
module Pretty where
import AST

pretty :: Pretty a => a -> String
pretty x = bpretty 0 x ""

class Pretty a where
  bpretty :: Int -> a -> ShowS

instance Pretty a => Pretty [a] where
  bpretty _ list = showString "[" . go list
    where
      go []     = showString "]"
      go [x]    = bpretty 0 x . go []
      go (x:xs) = bpretty 0 x . showString ", " . go xs

instance (Pretty a, Pretty b) => Pretty (a, b) where
  bpretty _ (x, y) =
    showString "("  . bpretty 0 x .
    showString ", " . bpretty 0 y .
    showString ")"

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  bpretty _ (x, y, z) =
    showString "("  . bpretty 0 x .
    showString ", " . bpretty 0 y .
    showString ", " . bpretty 0 z .
    showString ")"

instance Pretty Var where
  bpretty _ (Var v) = showString v

instance Pretty TVar where
  bpretty _ (TypeVar v) = showString v

instance Pretty (Type a) where
  bpretty d typ = case typ of
    TUnit -> showString "()"
    TVar v -> bpretty d v
    TExists v -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec v
    TForall v t -> showParen (d > forall_prec) $
      showString "∀ " . bpretty (forall_prec + 1) v .
      showString ". "      . bpretty forall_prec t
    TFun t1 t2 -> showParen (d > fun_prec) $
      bpretty (fun_prec + 1) t1 . showString " → " .
      bpretty fun_prec t2
    where
      exists_prec = 10
      forall_prec :: Int
      forall_prec = 1
      fun_prec    = 1

instance Pretty Expr where
  bpretty d expr = case expr of
    EVar v       -> bpretty d v
    EUnit        -> showString "()"
    EAbs v e     -> showParen (d > abs_prec) $
      showString "λ" . bpretty (abs_prec + 1) v .
      showString ". " . bpretty abs_prec e
    EApp e1 e2   -> showParen (d > app_prec) $
      bpretty app_prec e1 . showString " " . bpretty (app_prec + 1) e2
    EAnno e t -> showParen (d > anno_prec) $
      bpretty (anno_prec + 1) e . showString " : " . bpretty anno_prec t
    where
      abs_prec  = 1
      app_prec  = 10
      anno_prec = 1

instance Pretty (GContext a) where
  bpretty d (Context xs) = bpretty d $ reverse xs

instance Pretty (ContextElem a) where
  bpretty d cxte = case cxte of
    CForall v  -> bpretty d v
    CVar v t -> showParen (d > hastype_prec) $
      bpretty (hastype_prec + 1) v . showString " : " . bpretty hastype_prec t
    CExists v -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec v
    CExistsSolved v t -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec v .
      showString " = " . bpretty exists_prec t
    CMarker v -> showParen (d > app_prec) $
      showString "▶ " . bpretty (app_prec + 1) v
    where
      exists_prec = 1
      hastype_prec = 1
      app_prec     = 10
