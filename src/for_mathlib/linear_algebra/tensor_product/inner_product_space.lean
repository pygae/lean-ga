import for_mathlib.linear_algebra.bilinear_form.tensor_product

import analysis.inner_product_space.basic

variables {V W : Type*} [normed_add_comm_group V] [normed_add_comm_group W]
variables [inner_product_space ℝ V] [inner_product_space ℝ W]

open_locale tensor_product

noncomputable instance : inner_product_space.core ℝ (V ⊗[ℝ] W) :=
{ inner := λ x y, bilin_form_of_real_inner.tmul bilin_form_of_real_inner x y,
  conj_symm := λ x y,
    bilin_form.is_symm.tmul (λ x y, real_inner_comm _ _) (λ x y, real_inner_comm _ _) y x,
  nonneg_re := λ x, begin
    simp only [is_R_or_C.re_to_real],
    induction x using tensor_product.induction_on with v w x y hx hy,
    { simp only [bilin_form.zero_right] },
    { simp only [bilin_form.tmul.equations._eqn_1, bilin_form_of_real_inner_apply,
        bilin_form.tensor_distrib_tmul],
      exact mul_nonneg real_inner_self_nonneg real_inner_self_nonneg, },
    { simp only [bilin_form.add_left, bilin_form.add_right],
      sorry },
  end,
  definite := sorry,
  add_left := bilin_form.add_left,
  smul_left := λ _ _ _, bilin_form.bilin_smul_left _ _ _ _ }

noncomputable instance : normed_add_comm_group (V ⊗[ℝ] W) :=
@inner_product_space.core.to_normed_add_comm_group ℝ _ _ _ _ _

noncomputable instance : inner_product_space ℝ (V ⊗[ℝ] W) :=
inner_product_space.of_core _

@[simp] lemma tmul_inner_tmul (v₁ : V) (w₁ : W) (v₂ : V) (w₂ : W) :
  @inner ℝ _ _ (v₁ ⊗ₜ[ℝ] w₁) (v₂ ⊗ₜ[ℝ] w₂) = inner v₁ v₂ * inner w₁ w₂ :=
bilin_form.tensor_distrib_tmul _ _ _ _ _ _

@[simp] lemma norm_tmul (v : V) (w : W) : ‖v ⊗ₜ[ℝ] w‖ = ‖v‖ * ‖w‖ :=
begin
  have := congr_arg real.sqrt (tmul_inner_tmul v w v w),
  simp_rw real_inner_self_eq_norm_sq at this,
  rw [← mul_pow, real.sqrt_sq (norm_nonneg _),
    real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at this,
  exact this,
end

@[simp] lemma nnnorm_tmul (v : V) (w : W) : ‖v ⊗ₜ[ℝ] w‖₊ = ‖v‖₊ * ‖w‖₊ :=
nnreal.eq $ norm_tmul _ _
