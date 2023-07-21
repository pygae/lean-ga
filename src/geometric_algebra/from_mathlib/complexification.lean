import linear_algebra.clifford_algebra.basic
import data.complex.module
import ring_theory.tensor_product
import for_mathlib.linear_algebra.bilinear_form.tensor_product
import for_mathlib.algebra.ring_quot
import geometric_algebra.from_mathlib.basic

/-! # Complexification of a clifford algebra

In this file we show the isomorphism

* `equiv_complexify Q : clifford_algebra Q.complexify ≃ₐ[ℂ] (ℂ ⊗[ℝ] clifford_algebra Q)`

where

* `quadratic_form.complexify Q : quadratic_form ℂ (ℂ ⊗[ℝ] V)`

-/

variables {V: Type*} [add_comm_group V] [module ℝ V]
.

open_locale tensor_product

namespace quadratic_form

noncomputable def complexify (Q : quadratic_form ℝ V) :
  quadratic_form ℂ (ℂ ⊗[ℝ] V) :=
bilin_form.to_quadratic_form $
  (bilin_form.tmul' (linear_map.mul ℂ ℂ).to_bilin Q.associated)

@[simp] lemma complexify_apply (Q : quadratic_form ℝ V) (c : ℂ) (v : V) :
  Q.complexify (c ⊗ₜ v) = (c*c) * algebra_map _ _ (Q v) :=
begin
  change (c*c) * algebra_map _ _ (Q.associated.to_quadratic_form v) = _,
  rw quadratic_form.to_quadratic_form_associated,
end

lemma complexify.polar_bilin (Q : quadratic_form ℝ V) :
  Q.complexify.polar_bilin = (linear_map.mul ℂ ℂ).to_bilin.tmul' Q.polar_bilin :=
begin
  apply bilin_form.to_lin.injective _,
  ext v w : 6,
  change polar (Q.complexify) (1 ⊗ₜ[ℝ] v) (1 ⊗ₜ[ℝ] w) = 1 * 1 * algebra_map _ _ (polar Q v w),
  simp_rw [polar, complexify_apply, ←tensor_product.tmul_add, complexify_apply, one_mul,
    _root_.map_sub],
end

@[simp] lemma complexify_polar_apply (Q : quadratic_form ℝ V)
  (c₁ : ℂ) (v₁ : V) (c₂ : ℂ) (v₂ : V):
  polar Q.complexify (c₁ ⊗ₜ[ℝ] v₁) (c₂ ⊗ₜ[ℝ] v₂) = (c₁ * c₂) * algebra_map _ _ (polar Q v₁ v₂) :=
bilin_form.congr_fun (complexify.polar_bilin Q) _ _



end quadratic_form


local attribute [-instance] module.complex_to_real

section algebra_tower_instances

instance free_algebra.algebra' : algebra ℝ (free_algebra ℂ (ℂ ⊗[ℝ] V)) :=
(restrict_scalars.algebra ℝ ℂ (free_algebra ℂ (ℂ ⊗[ℝ] V)) : _)

instance tensor_algebra.algebra' : algebra ℝ (tensor_algebra ℂ (ℂ ⊗[ℝ] V)) :=
ring_quot.algebra _

instance tensor_algebra.is_scalar_tower' : is_scalar_tower ℝ ℂ (tensor_algebra ℂ (ℂ ⊗[ℝ] V)) :=
ring_quot.is_scalar_tower _

local attribute [semireducible] clifford_algebra

instance clifford_algebra.algebra' (Q : quadratic_form ℝ V) :
  algebra ℝ (clifford_algebra Q.complexify) :=
ring_quot.algebra (clifford_algebra.rel Q.complexify)

instance clifford_algebra.is_scalar_tower (Q : quadratic_form ℝ V) :
  is_scalar_tower ℝ ℂ (clifford_algebra Q.complexify) :=
ring_quot.is_scalar_tower _

instance clifford_algebra.smul_comm_class (Q : quadratic_form ℝ V) :
  smul_comm_class ℝ ℂ (clifford_algebra Q.complexify) :=
ring_quot.smul_comm_class _

instance clifford_algebra.smul_comm_class' (Q : quadratic_form ℝ V) :
  smul_comm_class ℂ ℝ (clifford_algebra Q.complexify) :=
ring_quot.smul_comm_class _

end algebra_tower_instances

open clifford_algebra (ι)
open quadratic_form (complexify_apply)

local attribute [semireducible] clifford_algebra

noncomputable def of_complexify_aux (Q : quadratic_form ℝ V) :
  clifford_algebra Q →ₐ[ℝ] clifford_algebra Q.complexify :=
clifford_algebra.lift Q begin
  refine ⟨(ι Q.complexify).restrict_scalars ℝ ∘ₗ tensor_product.mk ℝ ℂ V 1, λ v, _⟩,
  refine (clifford_algebra.ι_sq_scalar Q.complexify (1 ⊗ₜ v)).trans _,
  rw [complexify_apply, one_mul, one_mul, ←is_scalar_tower.algebra_map_apply],
end

@[simp] lemma of_complexify_aux_ι (Q : quadratic_form ℝ V) (v : V) :
  of_complexify_aux Q (ι Q v) = ι Q.complexify (1 ⊗ₜ v) :=
clifford_algebra.lift_ι_apply _ _ _

noncomputable def of_complexify (Q : quadratic_form ℝ V) :
  ℂ ⊗[ℝ] clifford_algebra Q →ₐ[ℂ] clifford_algebra Q.complexify :=
algebra.tensor_product.alg_hom_of_linear_map_tensor_product'
  (tensor_product.algebra_tensor_module.lift $
    let f : ℂ →ₗ[ℂ] _ := (algebra.lsmul ℂ (clifford_algebra Q.complexify)).to_linear_map in
    linear_map.flip $ linear_map.flip (({
      to_fun := λ f : clifford_algebra Q.complexify →ₗ[ℂ] clifford_algebra Q.complexify,
        linear_map.restrict_scalars ℝ f,
      map_add' := λ f g, linear_map.ext $ λ x, rfl,
      map_smul' := λ (c : ℂ) g, linear_map.ext $ λ x, rfl,
    } : _ →ₗ[ℂ] _) ∘ₗ f) ∘ₗ (of_complexify_aux Q).to_linear_map)
  (λ z₁ z₂ b₁ b₂,
    show (z₁ * z₂) • of_complexify_aux Q (b₁ * b₂)
      = z₁ • of_complexify_aux Q b₁ * z₂ • of_complexify_aux Q b₂,
    by rw [map_mul, smul_mul_smul])
  (λ r,
    show r • of_complexify_aux Q 1 = algebra_map ℂ (clifford_algebra Q.complexify) r,
    by rw [map_one, algebra.algebra_map_eq_smul_one])

@[simp] lemma of_complexify_tmul_ι (Q : quadratic_form ℝ V) (z : ℂ) (v : V) :
  of_complexify Q (z ⊗ₜ ι Q v) = ι _ (z ⊗ₜ v) :=
begin
  show z • of_complexify_aux Q (ι Q v)
    = ι Q.complexify (z ⊗ₜ[ℝ] v),
  rw [of_complexify_aux_ι, ←map_smul, tensor_product.smul_tmul', smul_eq_mul, mul_one],
end

@[simp] lemma of_complexify_tmul_one (Q : quadratic_form ℝ V) (z : ℂ) :
  of_complexify Q (z ⊗ₜ 1) = algebra_map _ _ z :=
begin
  show z • of_complexify_aux Q 1 = _,
  rw [map_one, ←algebra.algebra_map_eq_smul_one],
end

localized "notation (name := tensor_product)
  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N" in tensor_product


noncomputable def to_complexify (Q : quadratic_form ℝ V) :
  clifford_algebra Q.complexify →ₐ[ℂ] ℂ ⊗[ℝ] clifford_algebra Q :=
clifford_algebra.lift _ $ begin
  let φ := tensor_product.algebra_tensor_module.map (linear_map.id : ℂ →ₗ[ℂ] ℂ) (ι Q),
  refine ⟨φ, _⟩,
  rw clifford_algebra.preserves_iff_bilin _ (is_unit.mk0 (2 : ℂ) two_ne_zero),
  ext v w,
  change (1 * 1) ⊗ₜ[ℝ] (ι Q v * ι Q w) + (1 * 1) ⊗ₜ[ℝ] (ι Q w * ι Q v) =
    quadratic_form.polar (Q.complexify) (1 ⊗ₜ[ℝ] v) (1 ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] 1,
  rw [← tensor_product.tmul_add, clifford_algebra.ι_mul_ι_add_swap,
    quadratic_form.complexify_polar_apply, one_mul, one_mul,
    algebra.tensor_product.algebra_map_tmul_one],
end

@[simp] lemma to_complexify_ι (Q : quadratic_form ℝ V) (z : ℂ) (v : V) :
  to_complexify Q (ι _ (z ⊗ₜ v)) = z ⊗ₜ ι Q v :=
clifford_algebra.lift_ι_apply _ _ _

local attribute [ext] tensor_product.ext

lemma to_complexify_comp_of_complexify (Q : quadratic_form ℝ V) :
  (to_complexify Q).comp (of_complexify Q) = alg_hom.id _ _ :=
begin
  ext z,
  { change to_complexify Q (of_complexify Q (z ⊗ₜ[ℝ] 1)) = z ⊗ₜ[ℝ] 1,
    rw [of_complexify_tmul_one, alg_hom.commutes, algebra.tensor_product.algebra_map_apply,
      algebra.id.map_eq_self] },
  { ext v,
    change to_complexify Q (of_complexify Q (1 ⊗ₜ[ℝ] ι Q v))
      = 1 ⊗ₜ[ℝ] ι Q v,
    rw [of_complexify_tmul_ι, to_complexify_ι] },
end

@[simp] lemma to_complexify_of_complexify (Q : quadratic_form ℝ V) (x : ℂ ⊗[ℝ] clifford_algebra Q) :
  to_complexify Q (of_complexify Q x) = x := 
alg_hom.congr_fun (to_complexify_comp_of_complexify Q : _) x

lemma of_complexify_comp_to_complexify (Q : quadratic_form ℝ V) :
  (of_complexify Q).comp (to_complexify Q) = alg_hom.id _ _ :=
begin
  ext,
  show of_complexify Q (to_complexify Q (ι Q.complexify (1 ⊗ₜ[ℝ] x)))
    = ι Q.complexify (1 ⊗ₜ[ℝ] x),
  rw [to_complexify_ι, of_complexify_tmul_ι],
end

@[simp] lemma of_complexify_to_complexify (Q : quadratic_form ℝ V) (x : clifford_algebra Q.complexify) :
  of_complexify Q (to_complexify Q x) = x := 
alg_hom.congr_fun (of_complexify_comp_to_complexify Q : _) x

noncomputable def equiv_complexify (Q : quadratic_form ℝ V) :
  clifford_algebra Q.complexify ≃ₐ[ℂ] ℂ ⊗[ℝ] clifford_algebra Q :=
alg_equiv.of_alg_hom (to_complexify Q) (of_complexify Q)
  (to_complexify_comp_of_complexify Q)
  (of_complexify_comp_to_complexify Q)