/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.bilinear_form.tensor_product
import linear_algebra.quadratic_form.basic
import data.is_R_or_C.basic

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ : Type*}

open_locale tensor_product

namespace bilin_form

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
