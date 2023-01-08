/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.basic

/-! # Submonoids including the central ring -/

namespace algebra

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

instance : submonoid_class (center_submonoid R A) A :=
{ one_mem := λ S, S.to_submonoid.one_mem,
  mul_mem := λ S _ _, S.to_submonoid.mul_mem, }

instance : nonempty S.to_sub_mul_action := ⟨⟨1, S.to_submonoid.one_mem⟩⟩

instance : zero_mem_class (center_submonoid R A) A :=
{ zero_mem := λ S,  S.to_sub_mul_action.zero_mem ⟨1, S.to_submonoid.one_mem⟩, }

lemma smul_mem (r : R) {a : A} : a ∈ S → r • a ∈ S := S.to_sub_mul_action.smul_mem r
protected lemma mul_mem {a b : A} : a ∈ S → b ∈ S → a * b ∈ S := S.to_submonoid.mul_mem
protected lemma one_mem : (1 : A) ∈ S := S.to_submonoid.one_mem
protected lemma zero_mem : (0 : A) ∈ S := S.to_sub_mul_action.zero_mem ⟨1, S.one_mem⟩

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

@[simp, norm_cast] protected lemma coe_zero : ((0 : S) : A) = 0 := rfl
@[simp, norm_cast] protected lemma coe_smul (k : R) (v : S) : (↑(k • v) : A) = k • v := rfl

end semiring

section ring

variables [comm_ring R] [ring A] [algebra R A] (S : center_submonoid R A)

@[simp] lemma neg_mem (S : center_submonoid R A) (v : A) : v ∈ S → -v ∈ S := S.to_sub_mul_action.neg_mem

instance : has_neg (S) := S.to_sub_mul_action.has_neg

@[simp, norm_cast] lemma coe_neg (v : S) : (↑-v : A) = -v := rfl

end ring

end center_submonoid

end algebra
