/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.finsupp.basic
import algebra.algebra.basic
import algebra.monoid_algebra
import algebra.algebra.operations
import algebra.algebra.subalgebra
import group_theory.group_action.sub_mul_action

/-! Random theorems that belong in mathlib which are not related to GA

Upstream PRS:

* #4321

-/

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

namespace submodule

variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

def one_eq_algebra_of_id_range : (1 : submodule R A) = (algebra.of_id R A).range.to_submodule :=
begin
  dunfold has_one.one,
  ext,
  simp,
end

@[simp]
def algebra_map_mem (r : R) : algebra_map R A r ∈ (1 : submodule R A) :=
by simp [one_eq_algebra_of_id_range, algebra.of_id_apply]


end submodule

namespace algebra

section

set_option old_structure_cmd true

/-- A `center_submonoid` is a submonoid that includes the central ring of the algebra -/
structure center_submonoid (R : Type*) (A : Type*) [comm_semiring R] [semiring A] [algebra R A]
  extends submonoid A, sub_mul_action R A.

namespace center_submonoid

variables {R : Type*} {A : Type*}

section semiring

variables [comm_semiring R] [semiring A] [algebra R A] (S : center_submonoid R A)

instance : set_like (center_submonoid R A) A :=
{ coe := center_submonoid.carrier,
  coe_injective' := λ x y h, by { cases x, cases y, congr' } }

instance : nonempty S.to_sub_mul_action := ⟨⟨1, S.to_submonoid.one_mem⟩⟩

lemma smul_mem (r : R) {a : A} : a ∈ S → r • a ∈ S := S.to_sub_mul_action.smul_mem r
lemma mul_mem {a b : A} : a ∈ S → b ∈ S → a * b ∈ S := S.to_submonoid.mul_mem
lemma one_mem : (1 : A) ∈ S := S.to_submonoid.one_mem
lemma zero_mem : (0 : A) ∈ S := S.to_sub_mul_action.zero_mem ⟨1, S.one_mem⟩

@[simp] lemma algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
by { rw algebra_map_eq_smul_one r, exact S.smul_mem r S.one_mem, }

variables (R)
def closure (s : set A) : center_submonoid R A :=
let c := submonoid.closure (set.range (algebra_map R A) ∪ s) in
{ smul_mem' := λ r a h, begin
    rw algebra.smul_def r a, 
    exact c.mul_mem (submonoid.subset_closure $ or.inl $ set.mem_range_self r) h
  end, ..c}

@[simp] lemma subset_closure {s : set A} : s ⊆ closure R s :=
λ x hx, submonoid.subset_closure $ or.inr hx

@[simp] lemma closure_to_submonoid {s : set A} :
  (closure R s).to_submonoid = submonoid.closure (set.range (algebra_map R A) ∪ s) :=
rfl

variables {R}

instance : mul_action R S := S.to_sub_mul_action.mul_action
  
instance : monoid_with_zero S :=
{ zero_mul := λ v, subtype.eq $ zero_mul ↑v,
  mul_zero := λ v, subtype.eq $ mul_zero ↑v,
  ..S.to_sub_mul_action.has_zero,
  ..S.to_submonoid.to_monoid }

instance [nontrivial A] : nontrivial S :=
nontrivial_of_ne 0 1 (subtype.ne_of_val_ne zero_ne_one)

@[simp, norm_cast] lemma coe_zero : ((0 : S) : A) = 0 := rfl
@[simp, norm_cast] lemma coe_smul (k : R) (v : S) : (↑(k • v) : A) = k • v := rfl

end semiring

section ring

variables [comm_ring R] [ring A] [algebra R A] (S : center_submonoid R A)

@[simp] lemma neg_mem (S : center_submonoid R A) (v : A) : v ∈ S → -v ∈ S := S.to_sub_mul_action.neg_mem

instance : has_neg (S) := S.to_sub_mul_action.has_neg

@[simp, norm_cast] lemma coe_neg (v : S) : (↑-v : A) = -v := rfl

end ring

end center_submonoid

end



/-- A filtration is an indexed family of submodules such that `i ≤ j → S i ≤ S j` and `S i * S j = S (i + j)` -/
structure filtration (R : Type*) (A : Type*) (ι : Type*) [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A] :=
(to_fun : ι → submodule R A)
(mono' : monotone to_fun)
(complete' : ∀ x, ∃ i, x ∈ to_fun i)
(map_add' : ∀ n m, to_fun (n + m) = to_fun n * to_fun m)

namespace filtration

variables {R : Type*} {A : Type*} {ι : Type*} [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A]

instance : has_coe_to_fun (filtration R A ι) := ⟨_, λ f, f.to_fun⟩

variables (f : filtration R A ι)

-- the normal bundled function tricks, to hide the `to_fun`
@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl
@[simp] lemma mk_coe (f : ι → submodule R A) (h1 h2 h3) : ⇑(filtration.mk f h1 h2 h3) = f := rfl
lemma mono : monotone f := f.mono'
lemma map_add {n m} : f (n + m) = f n * f m := f.map_add' n m
lemma complete : ∀ x, ∃ i, x ∈ f i := f.complete'

lemma supr_eq_top (x : A) : supr f = ⊤ :=
begin
  rw submodule.supr_eq_span,
  suffices : (⋃ (i : ι), (f i : set A)) = ⊤,
  { simp [this] },
  refine set.eq_univ_of_forall (λ x, _),
  simp only [set.mem_Union, set_like.mem_coe],
  exact f.complete' x,
end

end filtration

end algebra
