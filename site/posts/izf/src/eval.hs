data Term
    = Var Int
    | Lam Term
    | App Term Term

lift :: (Int, Term) -> Term
lift (i, Var v) | v < i = Var v
lift (i, Var v) | v >= i = Var (v+1)
lift (i, Lam b) =
    let c = lift (i+1, b) in Lam c
lift (i, App f a) =
    let g = lift (i, f)
        b = lift (i, a)
    in App g b

lower :: (Int, Term) -> Term
lower (i, Var v) | v < i = Var v
lower (i, Var v) | v >= i = Var (v-1)
lower (i, App f a) =
    let g = lower (i, f)
        b = lower (i, a)
    in App g b
lower (i, Lam b) =
    let c = lower (i+1, b)
    in Lam c

subst :: (Int, Term, Term) -> Term
subst (i, st, Var v) | i == v = st
subst (i, st, Var v) | i /= v = Var v
subst (i, st, App f a) =
    let g = subst (i, st, f)
        b = subst (i, st, a)
    in App g b
subst (i, st, Lam b) =
    let c = subst (i+1, lift (0, st), b)
    in Lam c

eval :: Term -> Term
eval (Lam b) = Lam b
eval (App f a) =
    let (Lam b) = eval f
        sb = subst (0, a, b)
        lb = lower (0, sb)
        vb = eval lb
    in vb