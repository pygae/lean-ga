/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.grading
import linear_algebra.dfinsupp
import linear_algebra.quadratic_form.prod
import algebra.algebra.subalgebra.basic
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

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl


namespace equiv_even

@[reducible]
def Q' := (Q.prod $ -@quadratic_form.sq R _)

/-- The unit vector in the new dimension -/
def e0 := ι (Q' Q) (0, 1)

lemma e0_mul_e0 : e0 Q * e0 Q = -1 :=
(ι_sq_scalar _ _).trans begin
  simp,
end

lemma neg_e0_mul_ι (m : M) : -(e0 Q * ι _ (m, 0)) = ι _ (m, 0) * e0 Q :=
begin
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans _),
  dsimp [quadratic_form.polar],
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero, quadratic_form.map_zero,
    add_sub_cancel, sub_self, map_zero, zero_sub],
end

lemma neg_ι_mul_e0 (m : M) : -(ι _ (m, 0) * e0 Q) = e0 Q * ι _ (m, 0) :=
begin
  rw neg_eq_iff_neg_eq,
  exact neg_e0_mul_ι _ m
end

/-- The embedding from the smaller algebra into the new larger one. -/
def to_even : clifford_algebra Q →ₐ[R] clifford_algebra.even (Q' Q) :=
begin
  refine clifford_algebra.lift Q ⟨_, λ m, _⟩,
  { refine linear_map.cod_restrict _ _ (λ m, submodule.mem_supr_of_mem ⟨2, rfl⟩ _),
    exact (linear_map.mul_left R $ e0 Q).comp ((ι _).comp $ linear_map.inl R M R),
    rw [subtype.coe_mk, pow_two],
    exact submodule.mul_mem_mul (linear_map.mem_range_self _ _) (linear_map.mem_range_self _ _), },
  { ext1,
    dsimp only [subalgebra.coe_mul, linear_map.cod_restrict_apply, linear_map.comp_apply,
      linear_map.mul_left_apply, linear_map.inl_apply, subalgebra.coe_algebra_map],
    rw [←neg_ι_mul_e0] {occs := occurrences.pos [1]},
    rw [←mul_neg, mul_assoc, ←mul_assoc _ (e0 _), neg_mul, e0_mul_e0, neg_neg, one_mul,
      ι_sq_scalar],
    dsimp [Q'],
    rw [zero_mul, neg_zero, add_zero], }
end

@[simp]
lemma to_even_ι (m : M) : (to_even Q (ι Q m) : clifford_algebra (Q' Q)) = e0 Q * ι (Q' Q) (m, 0) :=
begin
  rw [to_even, clifford_algebra.lift_ι_apply, linear_map.cod_restrict_apply],
  refl,
end

end equiv_even

end clifford_algebra
