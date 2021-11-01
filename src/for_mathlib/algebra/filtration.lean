/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.operations

/-! # Filtrations of an `algebra` -/

namespace algebra

/-- A filtration is an indexed family of submodules such that `i ≤ j → S i ≤ S j` and `S i * S j = S (i + j)` -/
structure filtration (R : Type*) (A : Type*) (ι : Type*) [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A] :=
(to_fun : ι → submodule R A)
(mono' : monotone to_fun)
(complete' : ∀ x, ∃ i, x ∈ to_fun i)
(map_add' : ∀ n m, to_fun (n + m) = to_fun n * to_fun m)

namespace filtration

variables {R : Type*} {A : Type*} {ι : Type*} [preorder ι] [has_add ι] [comm_semiring R] [semiring A] [algebra R A]

instance : has_coe_to_fun (filtration R A ι) (λ _, ι → submodule R A) := ⟨to_fun⟩

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
