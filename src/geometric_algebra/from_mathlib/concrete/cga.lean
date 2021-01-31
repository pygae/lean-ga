import linear_algebra.clifford_algebra
import data.matrix.notation
import data.real.basic
import analysis.normed_space.inner_product

noncomputable theory

variables (V : Type*) [inner_product_space ℝ V]

/-- A conformalized vector has additional e0 and einf components -/
@[derive [add_comm_group, vector_space ℝ]]
def conformalize : Type* := V × ℝ × ℝ

namespace conformalize

variables {V}
/-! Define linear maps to extract the new components -/
def v : conformalize V →ₗ[ℝ] V := ⟨λ v, v.1, λ _ _, rfl, λ _ _, rfl⟩
def n0 : conformalize V →ₗ[ℝ] ℝ := ⟨λ v, v.2.1, λ _ _, rfl, λ _ _, rfl⟩
def ni : conformalize V →ₗ[ℝ] ℝ := ⟨λ v, v.2.2, λ _ _, rfl, λ _ _, rfl⟩

/-! The metric is the metric of V plus an extra term about n0 and ni. -/
def Q : quadratic_form ℝ (conformalize V) :=
(bilin_form_of_real_inner.comp v v).to_quadratic_form - (2 : ℝ) • quadratic_form.lin_mul_lin n0 ni

/-- Show the definition is what we expect. -/
@[simp] lemma Q_apply (x : conformalize V) : Q x = ∥x.v∥^2 - 2 * (x.n0 * x.ni) :=
begin
  dunfold Q,
  obtain ⟨xc, xo, xi⟩ := x,
  simp [Q, bilin_form_of_real_inner, sub_eq_add_neg, inner_self_eq_norm_sq_to_K],
end

variables (V)
/-- Define the Conformal Geometric Algebra over V. -/
abbreviation CGA := clifford_algebra (Q : quadratic_form ℝ $ conformalize V)

/-- And the embedding of the vector space into it. -/
def up (x : V) : CGA V :=
clifford_algebra.ι _ (x, 1, (1 / 2 : ℝ) * ∥x∥^2)

end conformalize
