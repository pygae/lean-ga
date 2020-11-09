/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.finsupp.basic
import algebra.algebra.basic
import algebra.monoid_algebra

/-! Random theorems that belong in mathlib which are not related to GA

Upstream PRS:

* #4321

-/

namespace finsupp

variables {α : Type*} {M : Type*} [has_zero M]

lemma single_of_single_apply (a a' : α) (b : M) :
  single a ((single a' b) a) = single a' (single a' b) a :=
begin
  rw [single_apply, single_apply],
  ext,
  split_ifs,
  { rw h, },
  { rw [zero_apply, single_apply, if_t_t], },
end

end finsupp

namespace add_monoid_algebra

variables (k : Type*) {G : Type*}
/--
The `alg_hom` which maps from a grading of an algebra `A` back to that algebra.
-/
noncomputable def sum_id {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] :
  add_monoid_algebra A G →ₐ[k] A :=
lift_nc_alg_hom (alg_hom.id k A) ⟨λ g, 1, by simp, λ a b, by simp⟩ (by simp)

lemma sum_id_apply {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] (g : add_monoid_algebra A G) :
  sum_id k g = g.sum (λ _ gi, gi) :=
by simp [sum_id, lift_nc_alg_hom, lift_nc_ring_hom, lift_nc, alg_hom.id, ring_hom.id]

end add_monoid_algebra

namespace opposite

variables (R : Type*) {M : Type*} [comm_semiring R] [semiring M] [algebra R M]

@[simps apply]
def op_linear_equiv : M ≃ₗ[R] Mᵒᵖ :=
{ map_smul' := opposite.op_smul, .. op_add_equiv }

@[simp] lemma coe_op_linear_equiv : (op_linear_equiv R : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm :
  ((op_linear_equiv R).symm : Mᵒᵖ → M) = unop := rfl

@[simp] lemma coe_op_linear_equiv_to_linear_map : ((op_linear_equiv R).to_linear_map : M → Mᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm_to_linear_map :
  ((op_linear_equiv R).symm.to_linear_map : Mᵒᵖ → M) = unop := rfl

end opposite
