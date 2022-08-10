/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.ring.basic
import data.int.basic

/-!
# Recursors in functional programming

This file contains the examples from section 2 of "Computing with the universal properties of the
Clifford algebra and the even subalgebra".

While these are not related to GA at all, they are valuable for building intuition for how to think
about `clifford_algebra.lift` and `clifford_algebra.fold`, along with other more complex recursion
schemes.

Some quick remarks about Lean syntax from those coming from the paper:

* $f(a, b)$ or $f(a)(b)$ is written `f a b`
* `x ↦ f(x)` is written `λ x, f x`.
-/

variables {R : Type*} [semiring R]

namespace icagca

def sum : list R → R
| []       := 0
| (a :: l) := a + sum l

run_cmd guard $ sum [1, 2, 3] = 6

def accum_from : list R → R → list R
| []       := λ a, [a]
| (b :: l) := λ a, a :: accum_from l (a + b)

def accum : list R → list R
| l := accum_from l 0

run_cmd guard $ accum [1, 2, 3] = [0, 1, 3, 6]

def rev_accum_aux : list R → R × list R
| []       := (0, [])
| (a :: l) := let (b, l') := rev_accum_aux l in (a + b, b :: l')

def rev_accum : list R → list R
| l := let (b, l') := rev_accum_aux l in b :: l'

run_cmd guard $ rev_accum [1, 2, 3] = [6, 5, 3, 0]

end icagca
