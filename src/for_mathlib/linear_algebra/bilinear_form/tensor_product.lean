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
variables {ι : Type*} {R S : Type*} {M₁ M₂ : Type*}

open_locale tensor_product

namespace bilin_form

section comm_semiring
variables [comm_semiring R] [comm_semiring S]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [algebra R S] [module R M₁] [module S M₁]
variables [smul_comm_class R S M₁] [smul_comm_class S R M₁] [smul_comm_class R S S] [is_scalar_tower R S M₁]
variables [module R M₂]

notation (name := tensor_product')
  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N

set_option pp.parens true

#check tensor_product.algebra_tensor_module.lift.equiv R S (M₁ ⊗ M₂) (M₁ ⊗ M₂) S

#check tensor_product.tensor_tensor_tensor_comm R M₁ M₂ M₁ M₂

instance : module R (M₁ ⊗[S] M₁) := tensor_product.left_module
instance : smul_comm_class R S (M₁ ⊗[S] M₁) := tensor_product.smul_comm_class_left
instance foo : module S ((M₁ ⊗[S] M₁) ⊗[R] (M₂ ⊗[R] M₂)) := tensor_product.left_module

instance : is_scalar_tower R S (M₁ ⊗[R] M₂) := tensor_product.is_scalar_tower_left

instance : smul_comm_class R S (bilin_form S M₁) := bilin_form.smul_comm_class
instance : module S (bilin_form S M₁ ⊗[R] bilin_form R M₂) := tensor_product.left_module

section
variables (R S M₁ M₂)

def tensor_tensor_tensor_comm' :
  ((M₁ ⊗[R] M₂) ⊗[S] (M₁ ⊗[R] M₂) ≃ₗ[S] (M₁ ⊗[S] M₁) ⊗[R] (M₂ ⊗[R] M₂)) := sorry

end

#check ((
  tensor_tensor_tensor_comm' _ _ _ _ : (((M₁ ⊗[R] M₂) ⊗[S] (M₁ ⊗[R] M₂)) ≃ₗ[S] ((M₁ ⊗[S] M₁) ⊗[R] (M₂ ⊗[R] M₂)))
  -- tensor_product.tensor_tensor_tensor_comm R M₁ M₂ M₁ M₂

).dual_map
  ≪≫ₗ (tensor_product.lift.equiv S (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) S).symm
  ≪≫ₗ linear_map.to_bilin).to_linear_map
-- #exit
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def tensor_distrib' : bilin_form S M₁ ⊗[R] bilin_form R M₂ →ₗ[S] bilin_form S (M₁ ⊗[R] M₂) :=
((tensor_tensor_tensor_comm' R S M₁ M₂).dual_map
  ≪≫ₗ (tensor_product.lift.equiv S (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) S).symm
  ≪≫ₗ linear_map.to_bilin).to_linear_map
  ∘ₗ _
  ∘ₗ (tensor_product.algebra_tensor_module.congr
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv S M₁ M₁ S)
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R M₂ M₂ R)).to_linear_map

@[simp] lemma tensor_distrib_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂)
  (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
  tensor_distrib (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) : bilin_form R (M₁ ⊗[R] M₂) :=
tensor_distrib (B₁ ⊗ₜ[R] B₂)

end comm_semiring


section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]

/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def tensor_distrib'' : bilin_form R M₁ ⊗[R] bilin_form R M₂ →ₗ[R] bilin_form R (M₁ ⊗[R] M₂) :=
((tensor_product.tensor_tensor_tensor_comm R M₁ M₂ M₁ M₂).dual_map
  ≪≫ₗ (tensor_product.lift.equiv R (M₁ ⊗ M₂) (M₁ ⊗ M₂) R).symm
  ≪≫ₗ linear_map.to_bilin).to_linear_map
  ∘ₗ tensor_product.dual_distrib R _ _
  ∘ₗ (tensor_product.congr
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)).to_linear_map

#print tensor_distrib''

@[simp] lemma tensor_distrib_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂)
  (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
  tensor_distrib (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) : bilin_form R (M₁ ⊗[R] M₂) :=
tensor_distrib (B₁ ⊗ₜ[R] B₂)

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
