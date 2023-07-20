/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.bilinear_form.tensor_product
import for_mathlib.ring_theory.tensor_product
import linear_algebra.quadratic_form.basic
import data.is_R_or_C.basic
import for_mathlib.linear_algebra.tensor_product
import for_mathlib.linear_algebra.bilinear_form.basic

universes u v w
variables {ι : Type*} {R A : Type*} {M₁ M₂ : Type*}

open_locale tensor_product

namespace bilin_form

section comm_semiring
variables [comm_semiring R] [comm_semiring A]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [algebra R A] [module R M₁] [module A M₁]
variables [smul_comm_class R A M₁] [smul_comm_class A R M₁] [smul_comm_class R A A] [is_scalar_tower R A M₁]
variables [module R M₂]

/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def tensor_distrib' : bilin_form A M₁ ⊗[R] bilin_form R M₂ →ₗ[A] bilin_form A (M₁ ⊗[R] M₂) :=
((tensor_product.algebra_tensor_module.tensor_tensor_tensor_comm R A M₁ M₂ M₁ M₂).dual_map
  ≪≫ₗ (tensor_product.lift.equiv A (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) A).symm
  ≪≫ₗ linear_map.to_bilin).to_linear_map
  ∘ₗ tensor_product.algebra_tensor_module.dual_distrib R _ _ _
  ∘ₗ (tensor_product.algebra_tensor_module.congr
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv A M₁ M₁ A)
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R M₂ M₂ R)).to_linear_map

@[simp] lemma tensor_distrib_tmul' (B₁ : bilin_form A M₁) (B₂ : bilin_form R M₂)
  (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
  tensor_distrib' (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * algebra_map R A (B₂ m₂ m₂') :=
begin
  -- will be refl once we fill the sorry in `tensor_product.algebra_tensor_module.tensor_tensor_tensor_comm`
  simp only [tensor_distrib', linear_map.comp_apply, linear_equiv.coe_to_linear_map,
    tensor_product.algebra_tensor_module.tensor_tensor_tensor_comm_apply, linear_equiv.trans_apply,
    linear_map.to_bilin_apply, tensor_product.algebra_tensor_module.dual_distrib_apply,
    tensor_product.algebra_tensor_module.congr_tmul,
    linear_equiv.dual_map_apply,
    tensor_product.lift.equiv_apply,
    bilin_form.to_lin_apply,
    tensor_product.algebra_tensor_module.tensor_tensor_tensor_comm_apply,
    tensor_product.algebra_tensor_module.dual_distrib_apply,
    tensor_product.lift.equiv_apply,
    tensor_product.lift.equiv_symm_apply,
    linear_equiv.dual_map_apply],
end

end comm_semiring

section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]

lemma is_symm.tmul {B₁ : bilin_form R M₁} {B₂ : bilin_form R M₂}
  (hB₁ : B₁.is_symm) (hB₂ : B₂.is_symm) : (B₁.tmul B₂).is_symm :=
suffices (B₁.tmul B₂).to_lin = (B₁.tmul B₂).to_lin.flip,
begin
  intros x y,
  have := fun_like.congr_fun (fun_like.congr_fun this x) y,
  exact this
end,
tensor_product.ext' $ λ x₁ x₂, tensor_product.ext' $ λ y₁ y₂,
  (congr_arg2 (*) (hB₁ x₁ y₁) (hB₂ x₂ y₂) : _)

end comm_semiring

end bilin_form

namespace quadratic_form
variables [add_comm_group M₁] [add_comm_group M₂]
variables [module ℝ M₁] [module ℝ M₂]

lemma _root_.quadratic_form.pos_def.tmul {B₁ : bilin_form ℝ M₁} {B₂ : bilin_form ℝ M₂}
  (hB₁ : B₁.to_quadratic_form.pos_def) (hB₂ : B₂.to_quadratic_form.pos_def) :
  (B₁.tmul B₂).to_quadratic_form.pos_def :=
sorry

end quadratic_form
