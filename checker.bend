# Elementary Affine Calculus
# ==========================

# Types
# -----

type Term
  = (Lam bod)
  | (App fun arg)
  | (Box val)
  | (Dup val bod)
  | (Var val)

# Utils
# -----

(concat String/Nil         ys) = ys
(concat (String/Cons x xs) ys) = (String/Cons x (concat xs ys))

(join List/Nil)         = String/Nil
(join (List/Cons x xs)) = (concat x (join xs))

(nth (List/Cons x xs) 0) = x
(nth (List/Cons x xs) n) = (nth xs (- n 1))
(nth List/Nil         n) = 0 # unreachable

# Stringification
# ---------------

(show (Term/Lam bod)     d) = (join ["λ" (show (bod (Term/Var d)) (+ d 1))])
(show (Term/App fun arg) d) = (join ["(" (show fun d) " " (show arg d) ")"])
(show (Term/Box val)     d) = (join ["!" (show val d)])
(show (Term/Dup val bod) d) = (join ["$" (show val d) " " (show (bod (Term/Var d)) (+ d 1))])
(show (Term/Var idx)     d) = (show_u24 idx "")

(show_u24 n) = switch (> n 9) {
  0: λx (String/Cons (+ 48 (% n 10)) x)
  _: λx (show_u24 (/ n 10) (String/Cons (+ 48 (% n 10)) x))
}

# Checker
# -------

# TODO

# Normalizer
# ----------

(normal (Term/Lam bod))     = (Term/Lam λx(normal (bod x)))
(normal (Term/App fun arg)) = (do_app (normal fun) (normal arg))
(normal (Term/Dup val bod)) = (do_dup (normal val) λx(normal (bod x)))
(normal (Term/Box val))     = (Term/Box (normal val))
(normal (Term/Var val))     = (Term/Var val)

(do_app (Term/Lam bod) arg) = (bod arg)
(do_app fun            arg) = (Term/App fun arg)

(do_dup (Term/Box val) bod) = (bod val)
(do_dup val            bod) = (Term/Dup val bod)

# Main
# ----

# cZ = λf $f=f ! λx x
cZ =
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Box
  (Term/Lam λx
  x))))

# cS = λn λf $f=f $N=(n f) ! λx (f (N x))
cS =
  (Term/Lam λn
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Dup (Term/App n f) λN
  (Term/Box
  (Term/Lam λx
  (Term/App f
  (Term/App N
  x))))))))

# cAdd = λa λb λf $F=f $A=(a !F) $B=(b !F) !λx(A (B x))
cAdd =
  (Term/Lam λa
  (Term/Lam λb
  (Term/Lam λf
  (Term/Dup f λF
  (Term/Dup (Term/App a (Term/Box F)) λA
  (Term/Dup (Term/App b (Term/Box F)) λB
  (Term/Box
  (Term/Lam λx
  (Term/App A
  (Term/App B
  x))))))))))

# cMul = λa λb λf $F=f (a (b !F))
cMul =
  (Term/Lam λa
  (Term/Lam λb
  (Term/Lam λf
  (Term/Dup f λF
  (Term/App a
  (Term/App b
  (Term/Box F)))))))

# c0 = λf $f=f ! λx x
c0 =
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Box
  (Term/Lam λx
  x))))

# c1 = λf $f=f ! λx (f x)
c1 =
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Box
  (Term/Lam λx
  (Term/App f
  x)))))

# c2 = λf $f=f ! λx (f (f x))
c2 =
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Box
  (Term/Lam λx
  (Term/App f
  (Term/App f
  x))))))

# c3 = λf $f=f ! λx (f (f (f x)))
c3 =
  (Term/Lam λf
  (Term/Dup f λf
  (Term/Box
  (Term/Lam λx
  (Term/App f
  (Term/App f
  (Term/App f
  x)))))))

# c4 = c2 * c2
c4 = (Term/App (Term/App cMul c2) c2)

# c8 = c4 * c2
c8 = (Term/App (Term/App cMul c4) c2)

# c16 = c8 * c2
c16 = (Term/App (Term/App cMul c8) c2)

# c32 = c16 * c2
c32 = (Term/App (Term/App cMul c16) c2)

# c64 = c32 * c2
c64 = (Term/App (Term/App cMul c32) c2)

# c128 = c64 * c2
c128 = (Term/App (Term/App cMul c64) c2)

# c256 = c128 * c2
c256 = (Term/App (Term/App cMul c128) c2)

# true = λt λf t
true =
  (Term/Lam λt
  (Term/Lam λf
  t))

# false = λt λf f
false =
  (Term/Lam λt
  (Term/Lam λf
  f))

# notf = λx λt λf (x f t)
notf =
  (Term/Lam λx
  (Term/Lam λt
  (Term/Lam λf
  (Term/App (Term/App x f) t))))

# not = λx (x false true)
not =
  (Term/Lam λx
  (Term/App (Term/App x false) true))

# main = $nots=(cN !not) !(not2 true)
term =
  (Term/Dup (Term/App c256 (Term/Box notf)) λnots
  (Term/Box (Term/App nots true)))

main = (show (normal term) 0)
