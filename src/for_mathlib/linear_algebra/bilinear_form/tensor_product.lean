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

open_locale tensor_product big_operators

namespace bilin_form

section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]


/-- The simple (aka pure) elements span the tensor product. -/
lemma _root_.tensor_product.closure_tmul_eq_top :
  add_submonoid.closure { t : M₁ ⊗[R] M₂ | ∃ m n, m ⊗ₜ n = t } = ⊤ :=
begin
  ext t, simp only [add_submonoid.mem_top, iff_true],
  apply t.induction_on,
  { exact zero_mem _, },
  { intros m n, apply add_submonoid.subset_closure, use [m, n], },
  { intros t₁ t₂ ht₁ ht₂, exact add_submonoid.add_mem _ ht₁ ht₂, },
end

attribute [elab_as_eliminator] add_submonoid.closure_induction_left

lemma _root_.tensor_product.list_induction (P : M₁ ⊗[R] M₂ → Prop)
  (h : ∀ s : list (M₁ × M₂), P (s.map (λ i : M₁ × M₂, i.1 ⊗ₜ[R] i.2)).sum) (x : M₁ ⊗[R] M₂) : P x :=
begin
  suffices : ∀ x : M₁ ⊗[R] M₂, ∃ s : list (M₁ × M₂), x = (s.map (λ i : M₁ × M₂, i.1 ⊗ₜ[R] i.2)).sum,
  { obtain ⟨s, rfl⟩ := this x,
    exact h s },
  clear h x P, intro x,
  have : x ∈ (⊤ : add_submonoid _) := add_submonoid.mem_top x,
  rw ←tensor_product.closure_tmul_eq_top at this,
  refine add_submonoid.closure_induction_left this _ _,
  { refine ⟨[], by simp⟩ },
  { rintros x ⟨m₁, m₂, rfl⟩ y ⟨l, rfl⟩,
    refine ⟨(m₁, m₂) :: l, _⟩,
    rw [list.map_cons, list.sum_cons] }
end

lemma _root_.tensor_product.finset_induction (P : M₁ ⊗[R] M₂ → Prop)
  (h : ∀ s : finset (M₁ × M₂), P (∑ i in s, i.1 ⊗ₜ[R] i.2)) (x : M₁ ⊗[R] M₂) : P x :=
begin
  suffices : ∀ x : M₁ ⊗[R] M₂, ∃ s : M₁ × M₂ →₀ ℕ, x = ∑ i in s.support.map, i.1 ⊗ₜ[R] i.2,
  { obtain ⟨s, rfl⟩ := this x,
    exact h s },
  clear h x P, intro x,
  have : x ∈ (⊤ : add_submonoid _) := add_submonoid.mem_top x,
  rw ←tensor_product.closure_tmul_eq_top at this,
  refine add_submonoid.closure_induction_left this _ _,
  { refine ⟨[], by simp⟩ },
  { rintros x ⟨m₁, m₂, rfl⟩ y ⟨l, rfl⟩,
    refine ⟨(m₁, m₂) :: l, _⟩,
    rw [finset.map_cons, finset.sum_cons] }
end



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

#print linear_map.sum_apply

theorem _root_.linear_map.list_sum_apply {R R₂ M M₂ : Type _} [semiring R]
  [semiring R₂] [add_comm_monoid M] [add_comm_monoid M₂] [module R M]
  [module R₂ M₂] {σ₁₂ : R →+* R₂} (l : list (M →ₛₗ[σ₁₂] M₂)) (b : M) :
  l.sum b = (l.map (λ f : M →ₛₗ[σ₁₂] M₂, f b)).sum :=
((add_monoid_hom.eval b).comp linear_map.to_add_monoid_hom').map_list_sum l

lemma _root_.quadratic_form.tmul_nonneg {B₁ : bilin_form ℝ M₁} {B₂ : bilin_form ℝ M₂}
  (hB₁ : ∀ x, 0 ≤ B₁.to_quadratic_form x) (hB₂ : ∀ x, 0 ≤ B₂.to_quadratic_form x) :
  ∀ x, 0 ≤ (B₁.tmul B₂).to_quadratic_form x :=
begin
  intros x,
  induction x using tensor_product.list_induction,
  simp_rw [bilin_form.to_quadratic_form_apply, ←bilin_form.to_lin_apply, map_list_sum,
    list.map_map, function.comp,
    linear_map.list_sum_apply, list.map_map, function.comp, bilin_form.to_lin_apply,
    bilin_form.tmul, bilin_form.tensor_distrib_tmul],
  dunfold quadratic_form.pos_def at hB₁,
    
  have : x ∈ (⊤ : add_submonoid _) := add_submonoid.mem_top x,
  rw ←tensor_product.closure_tmul_eq_top at this,
  revert hx,
  refine add_submonoid.closure_induction_left this _ _,
  { rintro h,
    cases h rfl },
  { rintro _ ⟨m, n, rfl⟩ y hy ha,
    simp_rw [bilin_form.to_quadratic_form_apply, bilin_form.add_right, bilin_form.add_left],
    erw bilin_form.tensor_distrib_tmul,
    }
end 


lemma _root_.quadratic_form.pos_def.tmul {B₁ : bilin_form ℝ M₁} {B₂ : bilin_form ℝ M₂}
  (hB₁ : B₁.to_quadratic_form.pos_def) (hB₂ : B₂.to_quadratic_form.pos_def) :
  (B₁.tmul B₂).to_quadratic_form.pos_def :=
begin
  intros x hx,
  induction x using tensor_product.list_induction,
  simp_rw [bilin_form.to_quadratic_form_apply, ←bilin_form.to_lin_apply, map_list_sum,
    list.map_map, function.comp,
    linear_map.list_sum_apply, list.map_map, function.comp, bilin_form.to_lin_apply,
    bilin_form.tmul, bilin_form.tensor_distrib_tmul],
  dunfold quadratic_form.pos_def at hB₁,
    
  have : x ∈ (⊤ : add_submonoid _) := add_submonoid.mem_top x,
  rw ←tensor_product.closure_tmul_eq_top at this,
  revert hx,
  refine add_submonoid.closure_induction_left this _ _,
  { rintro h,
    cases h rfl },
  { rintro _ ⟨m, n, rfl⟩ y hy ha,
    simp_rw [bilin_form.to_quadratic_form_apply, bilin_form.add_right, bilin_form.add_left],
    erw bilin_form.tensor_distrib_tmul,
    }
end 

end quadratic_form
