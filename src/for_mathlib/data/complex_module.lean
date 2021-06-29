/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.complex.module

/-! For `data/complex/module.lean`.

https://github.com/leanprover-community/mathlib/pull/8107 -/

noncomputable theory

namespace complex
section lift

variables {A : Type*} [ring A] [algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `complex.lift` for this as an equiv. -/
def lift_aux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
alg_hom.mk'
  { to_fun := ⇑((algebra.of_id ℝ A).to_linear_map.comp re_lm +
                (linear_map.to_span_singleton _ _ I').comp im_lm),
    map_zero' := linear_map.map_zero _,
    map_add' := linear_map.map_add _,
    map_mul' := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩, by {
      change algebra_map ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
             (algebra_map ℝ A x₁ + y₁ • I') * (algebra_map ℝ A x₂ + y₂ • I'),
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm],
      congr' 1, -- equate "real" and "imaginary" parts
      { rw [smul_mul_smul, hf, smul_neg, ←algebra.algebra_map_eq_smul_one, ←sub_eq_add_neg,
          ←ring_hom.map_mul, ←ring_hom.map_sub], },
      { rw [algebra.smul_def, algebra.smul_def, algebra.smul_def, ←algebra.right_comm _ x₂,
          ←mul_assoc, ←add_mul, ←ring_hom.map_mul, ←ring_hom.map_mul, ←ring_hom.map_add], } },
    map_one' := show algebra_map ℝ A 1 + (0 : ℝ) • I' = 1,
      by rw [ring_hom.map_one, zero_smul, add_zero], }
  (linear_map.map_smul _)

@[simp]
lemma lift_aux_apply (I' : A) (hI') (z : ℂ) :
 lift_aux I' hI' z = algebra_map ℝ A z.re + z.im • I' := rfl

lemma lift_aux_apply_I (I' : A) (hI') : lift_aux I' hI' I = I' := by simp

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps {simp_rhs := tt}]
noncomputable def lift : {I' : A // I' * I' = -1} ≃ (ℂ →ₐ[ℝ] A) :=
{ to_fun := λ I', lift_aux I' I'.prop,
  inv_fun := λ F, ⟨F I, by rw [←F.map_mul, I_mul_I, alg_hom.map_neg, alg_hom.map_one]⟩,
  left_inv := λ I', subtype.ext $ lift_aux_apply_I I' I'.prop,
  right_inv := λ F, alg_hom_ext $ lift_aux_apply_I _ _, }

/- When applied to `complex.I` itself, `lift` is the identity. -/
@[simp]
lemma lift_aux_I : lift_aux I I_mul_I = alg_hom.id ℝ ℂ :=
alg_hom_ext $ lift_aux_apply_I _ _

/- When applied to `-complex.I`, `lift` is conjugation, `conj`. -/
@[simp]
lemma lift_aux_neg_I : lift_aux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conj_ae :=
alg_hom_ext $ (lift_aux_apply_I _ _).trans conj_I.symm

end lift
end complex
