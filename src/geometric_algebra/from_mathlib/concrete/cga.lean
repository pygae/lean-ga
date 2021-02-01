import linear_algebra.clifford_algebra
import analysis.normed_space.inner_product

noncomputable theory

variables (V : Type*) [inner_product_space ℝ V]

/-- A conformalized vector has additional e0 and einf components -/
@[derive [add_comm_group, vector_space ℝ]]
def conformalize : Type* := V × ℝ × ℝ

namespace conformalize

variables {V}
/-! Define linear maps to extract the new components -/
def v : conformalize V →ₗ[ℝ] V := linear_map.fst _ _ _
def n0 : conformalize V →ₗ[ℝ] ℝ := (linear_map.fst _ _ _).comp (linear_map.snd _ _ _)
def ni : conformalize V →ₗ[ℝ] ℝ := (linear_map.snd _ _ _).comp (linear_map.snd _ _ _)

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
/-- Define the Conformal Geometric Algebra over `V` . -/
abbreviation CGA := clifford_algebra (Q : quadratic_form ℝ $ conformalize V)
variables {V}

open clifford_algebra

/-- And the embedding of the vector space into it. -/
def up (x : V) : CGA V :=
ι _ (x, 1, (1 / 2 : ℝ) * ∥x∥^2)

end conformalize
