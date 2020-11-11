/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import geometric_algebra.from_mathlib.basic
import geometric_algebra.from_mathlib.conjugation

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
/-!
# Versors, Rotors, Multivectors, and other subspaces

This file defines the `versors`, `rotors`, and `r_multivectors`.
-/

namespace clifford_algebra


variables (Q)
/-- The versors are the elements made up of products of vectors.

TODO: are scalars ≠1 considered versors? -/
def versors := submonoid.closure (set.range (algebra_map R _) ∪ set.range (ι Q) )

variables {Q}

namespace versors

  @[simp] lemma ι_mem (m : M) : ι Q m ∈ versors Q :=
  submonoid.subset_closure $ or.inr $ set.mem_range_self m

  @[simp] lemma algebra_map_mem (r : R) : ↑ₐr ∈ versors Q :=
  submonoid.subset_closure $ or.inl $ set.mem_range_self r

  /-- The versors are closed under scalar multiplication -/
  instance : mul_action R (versors Q) :=
  { smul := λ k v, ⟨k • v, by {
      rw algebra.smul_def,
      exact (versors Q).mul_mem (algebra_map_mem k) v.prop,
    }⟩,
    one_smul := λ v, subtype.eq $ one_smul _ v,
    mul_smul := λ k₁ k₂ v, subtype.eq $ mul_smul k₁ k₂ v, }

end versors

variables (Q)
/-- The rotors are the versors with an even number of factors -/
def rotors := submonoid.closure (set.range (algebra_map R _) ∪ set.range (ι Q) * set.range (ι Q) )
variables {Q}

namespace rotors

  /-- The rotors are versors -/
  lemma subset_versors : rotors Q ≤ versors Q :=
  begin
    unfold rotors versors,
    rw submonoid.closure_union,
    rw submonoid.closure_union,
    apply sup_le_sup_left _ _,
    rw submonoid.closure_le,
    exact submonoid.mul_subset_closure _,
  end

  @[simp] lemma ι_mul_mem (m n : M) : ι Q m * ι Q n ∈ rotors Q :=
  submonoid.subset_closure $ or.inr $ set.mul_mem_mul (set.mem_range_self m) (set.mem_range_self n)

  @[simp] lemma algebra_map_mem (r : R) : ↑ₐr ∈ rotors Q :=
  submonoid.subset_closure $ or.inl $ set.mem_range_self r

  /-- The rotors are closed under scalar multiplication -/
  instance : mul_action R (rotors Q) :=
  { smul := λ k v, ⟨k • v, by {
      rw algebra.smul_def,
      exact (rotors Q).mul_mem (algebra_map_mem k) v.prop,
    }⟩,
    one_smul := λ v, subtype.eq $ one_smul _ v,
    mul_smul := λ k₁ k₂ v, subtype.eq $ mul_smul k₁ k₂ v, }

end rotors

@[simp]
lemma involute_rotor (r : rotors Q) : involute (r : clifford_algebra Q) = r :=
submonoid.closure_induction r.prop
  (λ x hx, by {
    cases hx,
      { obtain ⟨a, rfl⟩ := set.mem_range.mpr hx,
        simp only [involute_algebra_map], },
      { obtain ⟨a, b, ha, hb, rfl⟩ := set.mem_mul.mpr hx,
        obtain ⟨av, rfl⟩ := ha,
        obtain ⟨bv, rfl⟩ := hb,
        rw involute.map_mul,
        simp only [involute_ι, neg_mul_neg], } })
  involute.map_one
  (λ x y hx hy, by rw [involute.map_mul, hx, hy])


variables (Q)
private def r_multivectors.def : ℕ → submodule R (clifford_algebra Q)
| 0 := 1
-- union needed here so that `r_multivectors Q 0 ≤ r_multivectors Q 1`
| (n + 1) := (r_multivectors.def n * (ι Q).range) ⊔ r_multivectors.def n

private lemma r_multivectors.map_add {ai bi : ℕ} :
  r_multivectors.def Q (ai + bi) = r_multivectors.def Q ai * r_multivectors.def Q bi :=
begin
  induction bi,
  { ext x,
    simp [r_multivectors.def, algebra.of_id_apply],
  },
  { simp [nat.succ_eq_add_one, ←nat.add_assoc, r_multivectors.def],
    rw submodule.mul_sup,
    rw [←submodule.mul_assoc, bi_ih], }
end

private lemma r_multivectors.mono : monotone (r_multivectors.def Q) :=
λ n n' h, nat.le_induction (le_of_eq rfl) (λ n hn ih, ih.trans le_sup_right) _ h

/-- The elements of at most grade `n` are a filtration -/
def r_multivectors : algebra.filtration R (clifford_algebra Q) ℕ :=
{ to_fun := r_multivectors.def Q,
  mono' := r_multivectors.mono Q,
  map_add' := λ i j, r_multivectors.map_add Q,
  complete' := λ x, begin
    induction x using clifford_algebra.induction,
    { use 0, simp [r_multivectors.def], },
    { use 1, simp [r_multivectors.def],
      refine submodule.mem_sup_left _,
      simp, },
    case h_mul : a b ha hb {
      obtain ⟨na, hna⟩ := ha,
      obtain ⟨nb, hnb⟩ := hb,
      use na + nb,
      rw r_multivectors.map_add,
      exact submodule.mul_mem_mul hna hnb,
    },
    case h_add : a b ha hb {
      obtain ⟨na, hna⟩ := ha,
      obtain ⟨nb, hnb⟩ := hb,
      use (na ⊔ nb),
      replace hna := submodule.le_def'.mpr (r_multivectors.mono Q le_sup_left) hna,
      replace hnb := submodule.le_def'.mpr (r_multivectors.mono Q le_sup_right) hnb,
      exact submodule.add_mem _ hna hnb,
    }
  end,
}
variables {Q}

namespace r_multivectors
  
  @[simp] lemma map_zero : r_multivectors Q 0 = 1 := rfl
  @[simp] lemma map_succ (n) : r_multivectors Q (n + 1) = (r_multivectors Q n * (ι Q).range) ⊔ r_multivectors Q n := rfl

  /-- Since the sets are monotonic, we can coerce up to a larger submodule -/
  instance (n r) : has_coe_t (r_multivectors Q n) (r_multivectors Q $ n + r) :=
  { coe := λ x, ⟨x, submodule.le_def'.mpr ((r_multivectors Q).mono (nat.le_add_right n r)) x.prop⟩ }

end r_multivectors
