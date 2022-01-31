/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.grading
import linear_algebra.dfinsupp
import algebra.algebra.subalgebra
import algebra.direct_sum.internal
import data.zmod.basic

/-!
# Grading by ℤ / 2ℤ, using `direct_sum`

This file is an alternative to the `add_monoid_algebra` approach using `direct_sum`.

The main result is now in mathlib, as `clifford_algebra.graded_algebra`.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)

def _root_.submodule.to_subalgebra {A : Type*} [semiring A] [algebra R A] (p : submodule R A)
  (h_one : (1 : A) ∈ p)
  (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : subalgebra R A :=
{ mul_mem' := h_mul,
  algebra_map_mem' := λ r, begin
    rw algebra.algebra_map_eq_smul_one,
    apply p.smul_mem _ h_one,
  end,
  ..p}

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

end clifford_algebra
