/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import geometric_algebra.from_mathlib.fold
import linear_algebra.clifford_algebra.grading
import linear_algebra.clifford_algebra.conjugation
import linear_algebra.clifford_algebra.contraction
import linear_algebra.exterior_algebra.basic

/-!
# Contraction in Clifford Algebras

Most of the results are now
[upstream](https://leanprover-community.github.io/mathlib_docs/linear_algebra/clifford_algebra/contraction.html)
as of https://github.com/leanprover-community/mathlib/pull/11468.
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

namespace clifford_algebra

variables (d d' : module.dual R M)

local infix `⌋`:70 := contract_left

variables {Q}

variables {Q' Q'' : quadratic_form R M} {B B' : bilin_form R M}
variables (h : B.to_quadratic_form = Q' - Q) (h' : B'.to_quadratic_form = Q'' - Q')

/-- Theorem 24 -/
lemma change_form_reverse (d : module.dual R M) (x : clifford_algebra Q) :
  change_form h (reverse x) = reverse (change_form h x) :=
begin
  apply clifford_algebra.left_induction _ (λ r, _) (λ x y hx hy, _) (λ x m hx, _) x,
  { simp_rw [change_form_algebra_map, reverse.commutes, change_form_algebra_map] },
  { rw [map_add, map_add, map_add, map_add, hx, hy] },
  { simp_rw [reverse.map_mul, change_form_ι_mul, map_sub, reverse.map_mul, reverse_ι],
    rw ←hx,
    rw ←change_form_contract_left,
    sorry }
end

variables {Q}

/-- The wedge product of the clifford algebra. -/
def wedge [invertible (2 : R)] (x y : clifford_algebra Q) : clifford_algebra Q :=
(equiv_exterior Q).symm (equiv_exterior Q x * equiv_exterior Q y)

infix ` ⋏ `:70 := wedge

end clifford_algebra
