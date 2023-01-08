/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.inner_product_space.basic
import linear_algebra.bilinear_form

/-- The real inner product as a bilinear form. -/
@[simps]
noncomputable def bilin_form_of_real_inner {F : Type*} [inner_product_space ℝ F] : bilin_form ℝ F :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }
