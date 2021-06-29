/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra

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

-- `monoid_algebra` is missing some of the `finsupp` API:

noncomputable def lsingle {k A : Type*} [semiring k] [semiring A] [module k A] (i : G) : A →ₗ[k] add_monoid_algebra A G :=
finsupp.lsingle i

@[simp] lemma lsingle_apply {k A : Type*} [semiring k] [semiring A] [module k A] (i : G) (a : A) :
  (lsingle i : _ →ₗ[k] _) a = finsupp.single i a := rfl

end add_monoid_algebra