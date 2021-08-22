/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.dfinsupp
import algebra.algebra.subalgebra
import algebra.direct_sum
import algebra.direct_sum_graded
import linear_algebra.direct_sum_module


/-!
# Grading by ℤ / 2ℤ, using `direct_sum`

This file is an alternative to the `add_monoid_algebra` approach using `direct_sum`.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

instance nat_power_direct_sum_gmonoid
  {R A ι} [add_monoid ι][decidable_eq ι] [comm_semiring R] [semiring A] [algebra R A]
  (S : submodule R A) (f : ι →+ ℕ) :
  direct_sum.gmonoid (λ i : ι, ↥(S ^ f i)) :=
direct_sum.gmonoid.of_submodules _
  (by { rw [f.map_zero, ←submodule.one_le, pow_zero], exact le_rfl })
  (λ i j p q, by { rw [f.map_add, pow_add], exact submodule.mul_mem_mul p.prop q.prop })

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

instance even_odd.gmonoid : direct_sum.gmonoid (λ i, even_odd Q i) :=
direct_sum.gmonoid.of_submodules _
  (submodule.one_le.mp (one_le_even_odd_zero Q))
  (λ i j p q, submodule.mul_le.mp (even_odd_mul_le Q _ _) _ p.prop _ q.prop)

/-- The direct sum of even and odd components form an algebra. -/
instance : algebra R (⨁ i, even_odd Q i) :=
{ to_ring_hom := (direct_sum.of_zero_ring_hom (λ i, even_odd Q i)).comp
  (algebra_map R (even Q) : _),
  smul_def' := λ r x, begin
    dsimp only [ring_hom.to_fun_eq_coe, ring_hom.comp_apply, direct_sum.of_zero_ring_hom,
      ring_hom.coe_mk, add_monoid_hom.to_fun_eq_coe],
    change const_smul_hom _ r x = add_monoid_hom.mul (direct_sum.of _ _ _) x,
    apply add_monoid_hom.congr_fun _ x,
    ext i xi : 2,
    dsimp only [add_monoid_hom.comp_apply, const_smul_hom_apply, add_monoid_hom.mul_apply],
    rw direct_sum.of_mul_of,
    dsimp only [direct_sum.of, dfinsupp.single_add_hom_apply, ←direct_sum.single_eq_lof R],
    rw ←dfinsupp.single_smul,
    apply dfinsupp.single_eq_of_sigma_eq,
    apply sigma.subtype_ext,
    exact (zero_add i).symm,
    apply algebra.smul_def r,
  end,
  commutes' := λ r x, begin
    dsimp only [ring_hom.to_fun_eq_coe, ring_hom.comp_apply, direct_sum.of_zero_ring_hom,
      ring_hom.coe_mk, add_monoid_hom.to_fun_eq_coe],
    change add_monoid_hom.mul (direct_sum.of _ _ _) x =
      add_monoid_hom.mul.flip (direct_sum.of _ _ _) x,
    apply add_monoid_hom.congr_fun _ x,
    ext i xi : 2,
    dsimp only [add_monoid_hom.comp_apply, add_monoid_hom.mul_apply, add_monoid_hom.flip_apply],
    rw direct_sum.of_mul_of,
    rw direct_sum.of_mul_of,
    apply dfinsupp.single_eq_of_sigma_eq,
    apply sigma.subtype_ext,
    exact (add_comm i 0).symm,
    apply algebra.commutes r,
  end }

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
{ commutes' := λ r, begin
    refine (direct_sum.to_semiring_of _ _ _ _ _),
    refl,
    intros, refl,
  end,
  ..(direct_sum.to_semiring (λ i, (submodule.subtype _).to_add_monoid_hom) rfl (λ _ _ _ _, rfl) :
      (⨁ i, even_odd Q i) →+* clifford_algebra Q) }

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
    apply alg_hom.to_linear_map_injective,
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
