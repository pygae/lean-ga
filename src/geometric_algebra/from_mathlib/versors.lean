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

  instance : monoid_with_zero (versors Q) :=
  { zero := ⟨0, algebra_map_mem 0⟩,
    zero_mul := λ v, subtype.eq $ zero_mul ↑v,
    mul_zero := λ v, subtype.eq $ mul_zero ↑v,
    ..(infer_instance : monoid (versors Q)) }

  @[simp, norm_cast] lemma coe_zero : ((0 : versors Q) : clifford_algebra Q) = 0 := rfl
  @[simp, norm_cast] lemma coe_neg (v : versors Q) : (↑-v : clifford_algebra Q) = -v := rfl
  @[simp, norm_cast] lemma coe_smul (k : R) (v : versors Q) : (↑(k • v) : clifford_algebra Q) = k • v := rfl


  /-- TODO: work out what the necessary conditions are here-/
  instance : nontrivial (versors Q) :=
  { exists_pair_ne := sorry }

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
    apply induction_on v,
    { intro r,
      refine ⟨r * r, _⟩,
      simp, },
    { intro m,
      refine ⟨Q m, _⟩,
      simp, },
    { rintros x y ⟨qx, hx⟩ ⟨qy, hy⟩,
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

  /-- The magnitude of a versor. -/
  @[simps apply]
  def magnitude_aux : versors Q →* clifford_algebra Q :=
  { to_fun := λ v, (v : clifford_algebra Q) * reverse (v : clifford_algebra Q),
    map_mul' := λ x y, by {
      simp only [reverse_mul, submonoid.coe_mul],
      obtain ⟨_, hx⟩ := mul_self_reverse x,
      obtain ⟨_, hy⟩ := mul_self_reverse y,
      rw [mul_assoc ↑x, ←mul_assoc ↑y, hy, algebra.commutes, ←mul_assoc, hx],
    },
    map_one' := by { simp } }

  def magnitude_aux_exists_scalar (v : versors Q) : ∃ r, magnitude_aux v = ↑ₐr :=
  mul_self_reverse v
  
  /--
  Only zero versors have zero magnitude, assuming:

   - The metric is not degenerate (`hqnz`)
   - `0` remains `0` when mapped from `R` into `clifford_algebra Q`
   - `R` has no zero divisors

  It's possible these last two requirements can be relaxed somehow.
  -/
  lemma magnitude_aux_zero (v : versors Q)
    [no_zero_divisors R]
    (hqnz : ∀ m, Q m = 0 → m = 0)
    (h0 : ∀ r, algebra_map R (clifford_algebra Q) r = 0 → r = 0) :
    magnitude_aux v = 0 ↔ v = 0 :=
  ⟨begin
    apply induction_on v,
    { intros r hr,
      simp only [subtype.coe_mk, magnitude_aux_apply, reverse_algebra_map] at hr,
      ext, simp only [coe_zero, subtype.coe_mk],
      rw [←ring_hom.map_mul] at hr,
      replace hr := h0 _ hr,
      rw mul_self_eq_zero at hr,
      rw [hr, ring_hom.map_zero], },
    { intros m hm,
      simp at hm,
      ext, simp,
      replace hm := hqnz _ (h0 _ hm),
      rw [hm, (ι Q).map_zero],
    },
    { intros a b ha hb hab,
      rw magnitude_aux.map_mul at hab,
      obtain ⟨ra, ha'⟩ := magnitude_aux_exists_scalar a,
      obtain ⟨rb, hb'⟩ := magnitude_aux_exists_scalar b,
      rw ha' at ha,
      rw hb' at hb,
      rw [ha', hb'] at hab,
      rw ←ring_hom.map_mul at hab,
      replace hab := h0 _ hab,
      obtain (ha'' | hb'') := mul_eq_zero.mp hab,
      { rw [ha'', ring_hom.map_zero] at ha, rw [ha rfl, zero_mul] },
      { rw [hb'', ring_hom.map_zero] at hb, rw [hb rfl, mul_zero] }
    },
  end, λ h, begin
    rw h,
    exact zero_mul (reverse 0),
  end⟩

  /-- The magnitude of a versor, as a member of the subalgebra of scalars
  
  Note we can't put this in `R` unless we know `algebra_map` is injective.
  This is kind of annoying, because it means that even if we have `field R`, we can't invert the
  magnitude
  -/
  @[simps apply]
  def magnitude : versors Q →* (⊥ : subalgebra R $ clifford_algebra Q) :=
  { to_fun := λ v, ⟨magnitude_aux v,
      let ⟨r, hr⟩ := mul_self_reverse v in algebra.mem_bot.mpr ⟨r, hr.symm⟩⟩,
    map_mul' := λ x y, subtype.ext $ magnitude_aux.map_mul x y,
    map_one' := subtype.ext $ magnitude_aux.map_one }

  noncomputable def magnitude_R (hi : function.injective $ algebra_map R (clifford_algebra Q)) : versors Q →* R :=
  { to_fun := λ v, classical.some (magnitude_aux_exists_scalar v),
    map_mul' := λ x y, hi begin
      rw ring_hom.map_mul,
      rw ←classical.some_spec (magnitude_aux_exists_scalar x),
      rw ←classical.some_spec (magnitude_aux_exists_scalar y),
      rw ←classical.some_spec (magnitude_aux_exists_scalar (x * y)),
      exact magnitude_aux.map_mul x y,
    end,
    map_one' := hi begin
      rw ring_hom.map_one,
      rw ←classical.some_spec (magnitude_aux_exists_scalar 1),
      exact magnitude_aux.map_one,
    end }

  @[simp]
  lemma magnitude_R_eq (hi) (v : versors Q) : (↑ₐ(magnitude_R hi v) : clifford_algebra Q) = magnitude v := begin
    unfold magnitude_R,
    simp only [submodule.coe_mk, monoid_hom.coe_mk],
    have := classical.some_spec (magnitude_aux_exists_scalar v),
    rw ← this,
    simp,
  end

  section field

  variables {R' : Type*} [field R'] {M' : Type*} [add_comm_group M'] [module R' M'] {Q' : quadratic_form R' M'} [nontrivial (clifford_algebra Q')]

  /-- When `R'` is a field, we can define the inverse as `~V / (V * ~V)`.
  
  Until we resolve the problems above about getting `r` constructively, we are forced to use the axiom of choice here -/
  @[simps inv]
  noncomputable instance : has_inv (versors Q') :=
  { inv := λ v, (magnitude_R (algebra_map R' _).injective v)⁻¹ • ⟨reverse (v : clifford_algebra Q'), reverse_mem v⟩ }

  noncomputable instance [f : fact (∀ m, Q' m = 0 → m = 0)] : group_with_zero (versors Q') :=
  {
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
        simp only [magnitude_R_eq, ←magnitude_aux_apply, magnitude_apply, subtype.coe_mk], },
      { intro h, apply ha,
        -- TODO: the fact that we use `congr_arg` only to then use `injective` suggests that we can relax the constraints in
        -- magnitude_aux_zero.
        have := (algebra_map R' (clifford_algebra Q')).congr_arg h,
        rw [magnitude_R_eq, ring_hom.map_zero, magnitude_apply, submodule.coe_mk] at this,
        rw ← magnitude_aux_zero,
        exact this,
        exact f.elim,
        intros r h,
        exact (algebra_map R' (clifford_algebra Q')).injective h,
        }
    end,
    ..(infer_instance : nontrivial (versors Q')),
    ..(infer_instance : monoid_with_zero (versors Q')),
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
