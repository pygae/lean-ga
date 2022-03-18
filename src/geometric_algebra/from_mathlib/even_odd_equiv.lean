/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.conjugation
import geometric_algebra.from_mathlib.even_odd
/-!
# The isomorphism with the even subalgebra

## Main definitions
* `clifford_algebra.equiv_even`
* `clifford_algebra.even_equiv_even_neg`
-/
lemma mul_mul_mul_assoc {α} [semigroup α] (a b c d : α) :
  (a * b) * (c * d) = a * (b * c) * d := by rw [mul_assoc, mul_assoc, mul_assoc]

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

namespace equiv_even

@[reducible]
def Q' : quadratic_form R (M × R) := (Q.prod $ -@quadratic_form.sq R _)

/-- The unit vector in the new dimension -/
def e0 : clifford_algebra (Q' Q) := ι (Q' Q) (0, 1)

lemma eq_smul_e0 (r : R) : ι (Q' Q) (0, r) = r • e0 Q :=
by rw [e0, ←linear_map.map_smul, prod.smul_mk, smul_zero, smul_eq_mul, mul_one]

lemma e0_mul_e0 : e0 Q * e0 Q = -1 :=
(ι_sq_scalar _ _).trans begin
  simp,
end

lemma neg_e0_mul_ι (m : M) : -(e0 Q * ι _ (m, 0)) = ι _ (m, 0) * e0 Q :=
begin
  refine neg_eq_of_add_eq_zero ((ι_mul_ι_add_swap _ _).trans _),
  dsimp [quadratic_form.polar],
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero, quadratic_form.map_zero,
    add_sub_cancel, sub_self, map_zero, zero_sub],
end

lemma neg_ι_mul_e0 (m : M) : -(ι _ (m, 0) * e0 Q) = e0 Q * ι _ (m, 0) :=
begin
  rw neg_eq_iff_neg_eq,
  exact neg_e0_mul_ι _ m
end

@[simp] lemma reverse_e0 : reverse (e0 Q) = e0 Q := reverse_ι _
@[simp] lemma involute_e0 : involute (e0 Q) = -e0 Q := involute_ι _

end equiv_even

open equiv_even

/-- The embedding from the smaller algebra into the new larger one. -/
def to_even : clifford_algebra Q →ₐ[R] clifford_algebra.even (Q' Q) :=
begin
  refine clifford_algebra.lift Q ⟨_, λ m, _⟩,
  { refine linear_map.cod_restrict _ _ (λ m, submodule.mem_supr_of_mem ⟨2, rfl⟩ _),
    exact (algebra.lmul_left R $ e0 Q).comp ((ι _).comp $ linear_map.inl R M R),
    rw [subtype.coe_mk, pow_two],
    exact submodule.mul_mem_mul (linear_map.mem_range_self _ _) (linear_map.mem_range_self _ _), },
  { ext1,
    dsimp only [subalgebra.coe_mul, linear_map.cod_restrict_apply, linear_map.comp_apply,
      algebra.lmul_left_apply, linear_map.inl_apply, subalgebra.coe_algebra_map],
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

/-- The embedding from the even subalgebra with an extra dimension into the original algebra. -/
def of_even : clifford_algebra.even (Q' Q) →ₐ[R] clifford_algebra Q :=
begin
  /-
  Recall that we need:
   * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
   * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
   * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
   * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
  -/
  let f : (M × R) →ₗ[R] (M × R) →ₗ[R] clifford_algebra Q :=
  ((algebra.lmul R (clifford_algebra Q)).to_linear_map.comp
    $ ((ι Q).comp (linear_map.fst _ _ _)) +
      (algebra.linear_map R _).comp (linear_map.snd _ _ _)).compl₂
    (((ι Q).comp (linear_map.fst _ _ _)) - (algebra.linear_map R _).comp (linear_map.snd _ _ _)),
  have f_apply :
    ∀ x y, f x y = (ι Q x.1 + algebra_map R _ x.2) * (ι Q y.1 - algebra_map R _ y.2) :=
    λ x y, rfl,
  have hc : ∀ (r : R) (x : clifford_algebra Q), commute (algebra_map _ _ r) x := algebra.commutes,
  have hm : ∀ m : M × R,
    ι Q m.1 * ι Q m.1 - algebra_map R _ m.2 * algebra_map R _ m.2 = algebra_map R _ (Q' Q m),
  { intro m,
    rw [ι_sq_scalar, ←ring_hom.map_mul, ←ring_hom.map_sub,
      sub_eq_add_neg, Q', quadratic_form.prod_to_fun, quadratic_form.neg_apply,
      quadratic_form.sq_to_fun] },
  refine even.lift (Q' Q) ⟨f, _, _⟩; simp_rw [f_apply],
  { intro m,
    rw [←(hc _ _).symm.mul_self_sub_mul_self_eq, hm] },
  { intros m₁ m₂ m₃,
    rw [←mul_smul_comm, ←mul_assoc, mul_assoc(_ + _), ←(hc _ _).symm.mul_self_sub_mul_self_eq',
      algebra.smul_def, ←mul_assoc, hm] },
end

lemma of_even_ι (x y : M × R) :
  of_even Q (even.ι _ x y) = (ι Q x.1 + algebra_map R _ x.2) * (ι Q y.1 - algebra_map R _ y.2) :=
even.lift_ι _ _ _ _

lemma to_even_comp_of_even :
  (to_even Q).comp (of_even Q) = alg_hom.id R _ :=
even.alg_hom_ext _ $ linear_map.ext $ λ m₁, linear_map.ext $ λ m₂, begin
  ext : 1,
  change ↑(to_even Q (of_even Q (even.ι (Q' Q) m₁ m₂))) = ι (Q' Q) m₁ * ι (Q' Q) m₂,
  rw [of_even_ι, alg_hom.map_mul, alg_hom.map_add, alg_hom.map_sub, alg_hom.commutes,
    alg_hom.commutes, subalgebra.coe_mul, subalgebra.coe_add, subalgebra.coe_sub,
    to_even_ι, to_even_ι, subalgebra.coe_algebra_map, subalgebra.coe_algebra_map],
  rw [mul_sub, add_mul, add_mul, ←mul_assoc (algebra_map _ _ _), ←algebra.smul_def,
      mul_assoc _ _ (algebra_map _ _ _), ←algebra.commutes, ←mul_assoc _ (algebra_map _ _ _),
      ←algebra.commutes, ←algebra.smul_def,
      ←neg_ι_mul_e0, neg_mul, mul_mul_mul_assoc, e0_mul_e0, mul_neg,
      mul_one, neg_mul, neg_neg, sub_eq_add_neg, neg_add],
  conv_rhs {
    rw [←prod.fst_add_snd m₁, ←prod.fst_add_snd m₂, linear_map.map_add, linear_map.map_add,
      eq_smul_e0, eq_smul_e0, mul_add, add_mul, add_mul, smul_mul_smul, e0_mul_e0, smul_neg,
      ←algebra.algebra_map_eq_smul_one, ring_hom.map_mul, mul_smul_comm, ←neg_e0_mul_ι, smul_neg,
      ←smul_mul_assoc],
  },
end

lemma of_even_comp_to_even :
  (of_even Q).comp (to_even Q) = alg_hom.id R _ :=
clifford_algebra.hom_ext $ linear_map.ext $ λ m, begin
  change of_even Q (to_even Q (ι Q m)) = ι Q m,
  rw ←subtype.coe_eta (to_even Q (ι Q m)) (to_even Q (ι Q m)).prop,
  simp_rw to_even_ι,
  refine (of_even_ι (Q) (0, 1) (m, 0)).trans _,
  dsimp only,
  rw [map_one, map_zero, map_zero, sub_zero, zero_add, one_mul],
end

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
@[simps]
def equiv_even : clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q' Q) :=
alg_equiv.of_alg_hom
  (to_even Q)
  (of_even Q)
  (to_even_comp_of_even Q)
  (of_even_comp_to_even Q)

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
lemma coe_to_even_reverse_involute (x : clifford_algebra Q) :
  ↑(to_even Q (reverse (involute x))) = reverse (to_even Q x : clifford_algebra (Q' Q)) :=
begin
  induction x using clifford_algebra.induction,
  case h_grade0 : r { simp only [alg_hom.commutes, subalgebra.coe_algebra_map, reverse.commutes] },
  case h_grade1 : m {
    simp only [involute_ι, subalgebra.coe_neg, to_even_ι, reverse.map_mul,
      reverse_ι, reverse_e0, neg_e0_mul_ι, map_neg] },
  case h_mul : x y hx hy { simp only [map_mul, subalgebra.coe_mul, reverse.map_mul, hx, hy] },
  case h_add : x y hx hy { simp only [map_add, subalgebra.coe_add, hx, hy] },
end

/-- The forward direction of `clifford_algebra.even_equiv_even_neg` -/
def even_to_neg : clifford_algebra.even Q →ₐ[R] clifford_algebra.even (-Q) :=
even.lift Q ⟨-(even.ι (-Q) : _),
  λ m, by simp_rw [linear_map.neg_apply, even.ι_same, quadratic_form.neg_apply, map_neg, neg_neg],
  λ m₁ m₂ m₃, by simp_rw [linear_map.neg_apply, neg_mul_neg, even.ι_contract, quadratic_form.neg_apply, smul_neg, neg_smul]⟩

@[simp] lemma even_to_neg_ι (m₁ m₂ : M) : even_to_neg Q (even.ι Q m₁ m₂) = -even.ι (-Q) m₁ m₂ :=
even.lift_ι Q _ m₁ m₂

/-- The reverse direction of `clifford_algebra.even_equiv_even_neg` -/
def even_of_neg : clifford_algebra.even (-Q) →ₐ[R] clifford_algebra.even Q :=
even.lift (-Q) ⟨-(even.ι Q : _),
  λ m, by simp_rw [linear_map.neg_apply, even.ι_same, quadratic_form.neg_apply, map_neg],
  λ m₁ m₂ m₃, by simp_rw [linear_map.neg_apply, neg_mul_neg, even.ι_contract, quadratic_form.neg_apply, neg_smul_neg]⟩

@[simp] lemma even_of_neg_ι (m₁ m₂ : M) : even_of_neg Q (even.ι (-Q) m₁ m₂) = -even.ι Q m₁ m₂ :=
even.lift_ι (-Q) _ m₁ m₂

/-- The even subalgebra of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps?]
def even_equiv_even_neg : clifford_algebra.even Q ≃ₐ[R] clifford_algebra.even (-Q) :=
alg_equiv.of_alg_hom
  (even_to_neg Q)
  (even_of_neg Q)
  (by {
    ext m₁ m₂ : 3,
    dsimp only [linear_map.compr₂_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply, alg_hom.id_apply],
    rw [even_of_neg_ι, map_neg, even_to_neg_ι, neg_neg] })
  (by {
    ext m₁ m₂ : 3,
    dsimp only [linear_map.compr₂_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply, alg_hom.id_apply],
    rw [even_to_neg_ι, map_neg, even_of_neg_ι, neg_neg] })

end clifford_algebra
