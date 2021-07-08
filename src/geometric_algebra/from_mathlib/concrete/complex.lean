/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic

/-!
# The complex numbers are isomorphic to a clifford algebra
-/

namespace clifford_algebra_complex

/-- The quadratic form sending elements to the negation of their square. -/
def Q : quadratic_form ℝ ℝ :=
-quadratic_form.lin_mul_lin linear_map.id linear_map.id

@[simp]
lemma Q_apply (r : ℝ) : Q r = - (r * r) := rfl

/-- Intermediate result of `clifford_algebra_complex.equiv_complex`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def to_complex : clifford_algebra Q →ₐ[ℝ] ℂ :=
clifford_algebra.lift Q ⟨linear_map.to_span_singleton _ _ complex.I, λ r, begin
  dsimp [linear_map.to_span_singleton, linear_map.id],
  rw smul_mul_smul,
  simp,
end⟩

@[simp]
lemma to_complex_ι (r : ℝ) : to_complex (clifford_algebra.ι Q r) = r • complex.I :=
clifford_algebra.lift_ι_apply _ _ r

/-- The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to `ℂ`. -/
@[simps]
def equiv_complex : clifford_algebra Q ≃ₐ[ℝ] ℂ :=
alg_equiv.of_alg_hom to_complex
  (complex.lift ⟨clifford_algebra.ι Q 1, begin
    rw [clifford_algebra.ι_sq_scalar, Q_apply, one_mul, ring_hom.map_neg, ring_hom.map_one],
  end⟩)
  (begin
    ext1,
    dsimp only [alg_hom.comp_apply, subtype.coe_mk, alg_hom.id_apply, complex.lift_apply],
    rw [complex.lift_aux_apply_I, to_complex_ι, one_smul],
  end)
  (begin
    ext,
    dsimp only [linear_map.comp_apply, complex.lift_apply, subtype.coe_mk, alg_hom.id_apply,
      alg_hom.to_linear_map_apply, alg_hom.comp_apply],
    rw [to_complex_ι, one_smul, complex.lift_aux_apply_I],
  end)

end clifford_algebra_complex
