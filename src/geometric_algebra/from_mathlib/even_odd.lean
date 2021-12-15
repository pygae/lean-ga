/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.dfinsupp
import algebra.algebra.subalgebra
import algebra.direct_sum.internal

/-!
# Grading by ℤ / 2ℤ, using `direct_sum`

This file is an alternative to the `add_monoid_algebra` approach using `direct_sum`.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

instance nat_power_graded_monoid
  {R A ι} [add_monoid ι] [decidable_eq ι] [comm_semiring R] [semiring A] [algebra R A]
  (S : submodule R A) (f : ι →+ ℕ) :
  set_like.graded_monoid (λ i : ι, S ^ f i) :=
{ one_mem := by { rw [f.map_zero, ←submodule.one_le, pow_zero], exact le_rfl },
  mul_mem := λ i j p q hp hq, by { rw [f.map_add, pow_add], exact submodule.mul_mem_mul hp hq } }

variables (Q)

/-- The even and odd submodules. -/
def even_odd (i : zmod 2) : submodule R (clifford_algebra Q) :=
⨆ j : ℕ, (ι Q).range ^ (2 * j + i.val)

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
subalgebra.copy
  { algebra_map_mem' := λ r, begin
      refine ⟨direct_sum.of _ 0 _, _⟩,
      refine ⟨algebra_map R _ r, _⟩,
      { rw [add_monoid_hom.map_zero, pow_zero], exact submodule.algebra_map_mem r },
      exact direct_sum.to_semiring_of _ _ _ _ _,
    end,
    .. (direct_sum.to_semiring
      (λ i : ℕ, ((ι Q).range ^ (add_monoid_hom.mul 2 i)).subtype.to_add_monoid_hom) rfl (λ i j hi hj, rfl)).srange }
  (even_odd Q 0)
  begin
    simp_rw [even_odd, zmod.val_zero, add_zero],
    rw submodule.supr_eq_range_dfinsupp_lsum,
    refl,
  end

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

lemma even_odd_mul_le (i j : zmod 2) : even_odd Q i * even_odd Q j ≤ even_odd Q (i + j) :=
begin
  simp_rw [even_odd, submodule.supr_eq_span, submodule.span_mul_span],
  apply submodule.span_mono,
  intros z hz,
  obtain ⟨x, y, hx, hy, rfl⟩ := hz,
  obtain ⟨xi, hx⟩ := set.mem_Union.mp hx,
  obtain ⟨yi, hy⟩ := set.mem_Union.mp hy,
  refine set.mem_Union.mpr ⟨xi + yi + (i.val + j.val) / 2, _⟩,
  rw [set_like.mem_coe, zmod.val_add, mul_add, add_assoc, nat.div_add_mod, mul_add,
    add_add_add_comm, pow_add],
  exact submodule.mul_mem_mul hx hy,
end

lemma one_le_even_odd_zero : 1 ≤ even_odd Q 0 :=
begin
  simp_rw [even_odd, zmod.val_zero, add_zero],
  convert le_supr _ 0,
  rw [mul_zero, pow_zero],
end

lemma range_ι_le_even_odd_one : (ι Q).range ≤ even_odd Q 1 :=
begin
  haveI : fact (1 < 2) := ⟨one_lt_two⟩,
  simp_rw [even_odd, zmod.val_one],
  convert le_supr _ 0,
  rw [mul_zero, zero_add, pow_one],
end

instance even_odd.graded_monoid : set_like.graded_monoid (even_odd Q) :=
{ one_mem := submodule.one_le.mp (one_le_even_odd_zero Q),
  mul_mem := λ i j p q hp hq, submodule.mul_le.mp (even_odd_mul_le Q _ _) _ hp _ hq }

/-- `clifford_algebra.ι` restricted to the odd submodule -/
@[simps]
def to_odd : M →ₗ[R] even_odd Q 1 :=
(ι Q).cod_restrict _ $ λ m, range_ι_le_even_odd_one Q $ linear_map.mem_range_self _ _

/-- The canonical map from the clifford algebra into its even and odd parts. -/
def to_even_odd : clifford_algebra Q →ₐ[R] (⨁ i, even_odd Q i) :=
begin
  apply clifford_algebra.lift Q _,
  refine ⟨(direct_sum.lof R _ (λ i, even_odd Q i) (1 : zmod 2)).comp (to_odd Q), λ m, _⟩,
  dsimp,
  erw direct_sum.of_mul_of,
  apply dfinsupp.single_eq_of_sigma_eq,
  apply sigma.subtype_ext,
  refl,
  exact ι_sq_scalar Q _,
end

@[simp]
lemma to_even_odd_ι (m : M) :
  to_even_odd Q (ι Q m) = direct_sum.of (λ i, even_odd Q i) 1 (to_odd Q m) :=
lift_ι_apply _ _ _


/-- TODO: this is `sorry`d! -/
lemma to_even_odd_of_mem (c : clifford_algebra Q) {i} (h : c ∈ even_odd Q i) :
  to_even_odd Q c = direct_sum.of (λ i, even_odd Q i) i ⟨c, h⟩ :=
begin
  induction c using clifford_algebra.induction,
  { rw alg_hom.commutes,
    apply dfinsupp.single_eq_of_sigma_eq,
    sorry },
  { rw to_even_odd_ι,
    apply dfinsupp.single_eq_of_sigma_eq,
    -- refine congr_arg _ _,
    sorry,},
  case h_mul : x y hx hy {
    rw [alg_hom.map_mul],
    sorry },
  case h_add : x y hx hy {
    rw [alg_hom.map_add],
    sorry },
end

/-- The canonical map back from the even and odd parts into the clifford algebra. -/
def of_even_odd : (⨁ i, even_odd Q i) →ₐ[R] clifford_algebra Q :=
direct_sum.to_algebra R _ (λ i, (submodule.subtype _)) rfl (λ _ _ _ _, rfl) (λ _, rfl)

@[simp]
lemma of_even_odd_of (i) (xi : even_odd Q i) :
  of_even_odd Q (direct_sum.of _ i xi) = xi :=
direct_sum.to_semiring_of _ rfl (λ _ _ _ _, rfl) _ _

/- An alternative to `clifford_algebra.grades` -/
def equiv_even_odd : clifford_algebra Q ≃ₐ[R] (⨁ i, even_odd Q i) :=
alg_equiv.of_alg_hom
  (to_even_odd Q)
  (of_even_odd Q)
  begin
    ext i ⟨xi, hxi⟩ : 2,
    dsimp,
    erw of_even_odd_of,
    rw subtype.coe_mk,
    rw to_even_odd_of_mem Q xi hxi,
    refl,
  end
  begin
    ext m,
    dsimp,
    rw to_even_odd_ι,
    rw of_even_odd_of,
    refl,
  end

end clifford_algebra
