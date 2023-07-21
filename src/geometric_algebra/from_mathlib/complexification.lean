import linear_algebra.clifford_algebra.basic
import data.complex.module
import ring_theory.tensor_product
import for_mathlib.linear_algebra.bilinear_form.tensor_product

variables {V: Type*} [add_comm_group V] [module ℝ V]
.

open_locale tensor_product

noncomputable def quadratic_form.complexify (Q : quadratic_form ℝ V) :
  quadratic_form ℂ (ℂ ⊗[ℝ] V) :=
bilin_form.to_quadratic_form $
  (bilin_form.tmul' (linear_map.mul ℂ ℂ).to_bilin Q.associated)

lemma complexify_apply (Q : quadratic_form ℝ V) (c : ℂ) (v : V) :
  Q.complexify (c ⊗ₜ v) = (c*c) * algebra_map _ _ (Q v) :=
begin
  change (c*c) * algebra_map _ _ (Q.associated.to_quadratic_form v) = _,
  rw quadratic_form.to_quadratic_form_associated,
end
