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
# Versors, spinors, Multivectors, and other subspaces

This file defines the `versors`, `spinors`, and `r_multivectors`.
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

  @[simp] lemma smul_mem (k : R) {v : clifford_algebra Q} (h : v ∈ versors Q) : k • v ∈ versors Q :=
  begin
    rw algebra.smul_def,
    exact (versors Q).mul_mem (algebra_map_mem k) h,
  end

  @[simp] lemma neg_mem {v : clifford_algebra Q} (h : v ∈ versors Q) : -v ∈ versors Q :=
  begin
    rw neg_eq_neg_one_mul,
    rw [←(algebra_map R _).map_one, ←(algebra_map R _).map_neg, ←algebra.smul_def],
    exact versors.smul_mem (-1) h,
  end

  instance : mul_action R (versors Q) :=
  { smul := λ k v, ⟨k • v, smul_mem k v.prop⟩,
    one_smul := λ v, subtype.eq $ one_smul _ v,
    mul_smul := λ k₁ k₂ v, subtype.eq $ mul_smul k₁ k₂ v, }
  
  instance : has_neg (versors Q) :=
  { neg := λ v, ⟨-v, neg_mem v.prop⟩ }

  instance : has_zero (versors Q) :=
  { zero := ⟨0, algebra_map_mem 0⟩ }

  @[simp] lemma zero_mul (v : versors Q) : 0 * v = 0 := subtype.eq $ zero_mul ↑v
  
  @[simp] lemma mul_zero (v : versors Q) : v * 0 = 0 := subtype.eq $ mul_zero ↑v

  lemma induction_on {C : versors Q → Prop}
    (v : versors Q)
    (h_grade0 : ∀ (r : R), C ⟨↑ₐr, algebra_map_mem r⟩)
    (h_grade1 : ∀ m, C ⟨ι Q m, ι_mem m⟩)
    (h_mul : ∀ (a b : versors Q), C a → C b → C (a * b)) :
    C v :=
  submonoid.closure_induction' _ _
    (λ x hx, by {
      cases hx,
        { obtain ⟨a, rfl⟩ := set.mem_range.mpr hx,
          exact h_grade0 a, },
        { obtain ⟨a, rfl⟩ := set.mem_range.mpr hx,
          exact h_grade1 a, } })
    (h_grade0 (1 : R))
    h_mul v

  /-- Involute of a versor is a versor -/
  @[simp] lemma involute_mem (v : versors Q) : involute (v : clifford_algebra Q) ∈ versors Q :=
  begin
    apply induction_on v,
    { intro r, simp, },
    { intro m, simp, },
    { intros a b ha hb, simp [(versors Q).mul_mem ha hb] }
  end

  /-- Reverse of a versor is a versor -/
  @[simp] lemma reverse_mem (v : versors Q) : reverse (v : clifford_algebra Q) ∈ versors Q :=
  begin
    apply induction_on v,
    { intro r, simp, },
    { intro m, simp, },
    { intros a b ha hb, simp [(versors Q).mul_mem hb ha] }
  end

  /-- A versor times its reverse is a scalar
  
  TODO: Can we compute `r` constructively? -/
  lemma mul_self_reverse (v : versors Q) :
    ∃ r : R, (v : clifford_algebra Q) * reverse (v : clifford_algebra Q) = ↑ₐr :=
  begin
    refine submonoid.closure_induction' _ _ (λ x hx, _) _ (λ x y hx hy, _) v,
    { cases hx,
      { obtain ⟨r, rfl⟩ := set.mem_range.mpr hx,
        refine ⟨r * r, _⟩,
        simp, },
      { obtain ⟨m, rfl⟩ := set.mem_range.mpr hx,
        refine ⟨Q m, _⟩,
        simp, }, },
    { refine ⟨1, _⟩, simp },
    { obtain ⟨qx, hx⟩ := hx,
      obtain ⟨qy, hy⟩ := hy,
      refine ⟨qx * qy, _⟩,
      simp only [reverse_mul, submonoid.coe_mul, ring_hom.map_mul],
      rw [mul_assoc ↑x, ←mul_assoc ↑y, hy, algebra.commutes, ←mul_assoc, hx],
    }
  end

  /-- A versor's reverse times itself is a scalar
  
  TODO: Can we compute `r` constructively? -/
  lemma reverse_mul_self (v : versors Q) :
    ∃ r : R, reverse (v : clifford_algebra Q) * (v : clifford_algebra Q) = ↑ₐr :=
  begin
    obtain ⟨r, hr⟩ := mul_self_reverse ⟨reverse (v : clifford_algebra Q), reverse_mem v⟩,
    refine ⟨r, _⟩,
    simpa [reverse_involutive ↑v] using hr,
  end

  /-- The magnitude of a versor.
  
  Note we can't put this in `R` unless we know `algebra_map` is injective.
  This is kind of annoying, because it means that even if we have `field R`, we can't invert the
  magnitude
  -/
  def magnitude : versors Q →* (algebra_map R $ clifford_algebra Q).range :=
  { to_fun := λ v, ⟨(v : clifford_algebra Q) * reverse (v : clifford_algebra Q),
      let ⟨r, hr⟩ := mul_self_reverse v in ring_hom.mem_range.mpr ⟨r, hr.symm⟩⟩,
    map_mul' := λ x y, by {
      ext,
      simp only [subring.coe_mul, reverse_mul, submonoid.coe_mul, subtype.coe_mk],
      obtain ⟨_, hx⟩ := mul_self_reverse x,
      obtain ⟨_, hy⟩ := mul_self_reverse y,
      rw [mul_assoc ↑x, ←mul_assoc ↑y, hy, algebra.commutes, ←mul_assoc, hx],
    },
    map_one' := by { ext, simp} }

  section field

  variables {R' : Type*} [field R'] {M' : Type*} [add_comm_group M'] [module R' M'] {Q' : quadratic_form R' M'}

  /-- When `R'` is a field, we can define the inverse as `~V / (V * ~V)`.
  
  Until we resolve the problems above about getting `r` constructively, we are forced to use the axiom of choice here -/
  @[simps inv]
  noncomputable instance : has_inv (versors Q') :=
  { inv := λ v, (classical.some (magnitude v).prop)⁻¹ • ⟨reverse (v : clifford_algebra Q'), reverse_mem v⟩ }

  noncomputable instance [fact (∀ m ≠ 0, Q' m ≠ 0)] : group_with_zero (versors Q') :=
  {
    zero_mul := zero_mul,
    mul_zero := mul_zero,
    exists_pair_ne := sorry,  -- trivial, but we need to work out appropriate assumptions
    inv_zero := begin
      rw has_inv_inv,
      ext,
      change _ • reverse 0 = 0,
      rw reverse.map_zero,
      rw smul_zero,
    end,
    mul_inv_cancel := λ a ha, begin
      let r := (magnitude a),
      rw has_inv_inv,
      ext,
      change ↑a * _ • reverse ↑a = 1,
      rw algebra.mul_smul_comm,
      rw inv_smul_eq_iff',
      { rw [algebra.smul_def, mul_one],
        obtain ⟨r', hr'⟩ := mul_self_reverse a,
        convert hr',
        sorry -- have to prove that `r' = classical.some ...`, which seems hard / false
        },
      { sorry -- have to prove that the divisor is not zero, which will come later.
        }
    end,
    ..(infer_instance : has_zero (versors Q')),
    ..(infer_instance : monoid (versors Q')),
    ..(infer_instance : has_inv (versors Q'))}

  end field

end versors

variables (Q)
/-- The spinors are the versors with an even number of factors -/
def spinors := submonoid.closure (set.range (algebra_map R _) ∪ set.range (ι Q) * set.range (ι Q) )
variables {Q}

namespace spinors

  /-- The spinors are versors -/
  lemma subset_versors : spinors Q ≤ versors Q :=
  begin
    unfold spinors versors,
    rw submonoid.closure_union,
    rw submonoid.closure_union,
    apply sup_le_sup_left _ _,
    rw submonoid.closure_le,
    exact submonoid.mul_subset_closure _,
  end

  @[simp] lemma ι_mul_mem (m n : M) : ι Q m * ι Q n ∈ spinors Q :=
  submonoid.subset_closure $ or.inr $ set.mul_mem_mul (set.mem_range_self m) (set.mem_range_self n)

  @[simp] lemma algebra_map_mem (r : R) : ↑ₐr ∈ spinors Q :=
  submonoid.subset_closure $ or.inl $ set.mem_range_self r

  @[simp] lemma smul_mem (k : R) {v : clifford_algebra Q} (h : v ∈ spinors Q) : k • v ∈ spinors Q :=
  begin
    rw algebra.smul_def,
    exact (spinors Q).mul_mem (algebra_map_mem k) h,
  end

  @[simp] lemma neg_mem {v : clifford_algebra Q} (h : v ∈ spinors Q) : -v ∈ spinors Q :=
  begin
    rw neg_eq_neg_one_mul,
    rw [←(algebra_map R _).map_one, ←(algebra_map R _).map_neg, ←algebra.smul_def],
    exact smul_mem (-1) h,
  end

  instance : mul_action R (spinors Q) :=
  { smul := λ k v, ⟨k • v, smul_mem k v.prop⟩,
    one_smul := λ v, subtype.eq $ one_smul _ v,
    mul_smul := λ k₁ k₂ v, subtype.eq $ mul_smul k₁ k₂ v, }

  instance : has_neg (spinors Q) :=
  { neg := λ v, ⟨-v, neg_mem v.prop⟩ }

  lemma induction_on {C : spinors Q → Prop}
    (v : spinors Q)
    (h_grade0 : ∀ (r : R), C ⟨↑ₐr, algebra_map_mem r⟩)
    (h_grade2 : ∀ m n, C ⟨ι Q m * ι Q n, ι_mul_mem m n⟩)
    (h_mul : ∀ (a b : spinors Q), C a → C b → C (a * b)) :
    C v :=
  submonoid.closure_induction' _ _
    (λ x hx, by {
      cases hx,
        { obtain ⟨a, rfl⟩ := set.mem_range.mpr hx,
          exact h_grade0 a, },
        { obtain ⟨_, _, ⟨a, rfl⟩, ⟨b, rfl⟩, rfl⟩ := set.mem_mul.mpr hx,
          exact h_grade2 a b, } })
    (h_grade0 (1 : R))
    h_mul v

  /-- Involute of a spinor is a spinor -/
  @[simp] lemma involute_mem (v : spinors Q) : involute (v : clifford_algebra Q) ∈ spinors Q :=
  begin
    apply induction_on v,
    { intro r, simp, },
    { intros m n, simp, },
    { intros a b ha hb, simp [(spinors Q).mul_mem ha hb] }
  end

  /-- Reverse of a spinor is a spinor -/
  @[simp] lemma reverse_mem (v : spinors Q) : reverse (v : clifford_algebra Q) ∈ spinors Q :=
  begin
    apply induction_on v,
    { intro r, simp, },
    { intro m, simp, },
    { intros a b ha hb, simp [(spinors Q).mul_mem hb ha] }
  end

end spinors

@[simp]
lemma involute_spinor (r : spinors Q) : involute (r : clifford_algebra Q) = r :=
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

end clifford_algebra
