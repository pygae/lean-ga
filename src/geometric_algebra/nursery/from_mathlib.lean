/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra
import data.zmod.basic
import data.nat.parity
import order.filter.basic
import algebra.algebra.subalgebra

import missing_from_mathlib

/-!
# Tools built on top of Mathlib's `linear_algebra.clifford_algebra`

Many things here may become "generalized out" as mathlib grows, or end up being PR'd upstream
-/


variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

namespace clifford_algebra

-- if this fails then you have the wrong branch of mathlib
example : ring (clifford_algebra Q) := infer_instance

/-- An induction principle for the `clifford_algebra` derived from `free_algebra.induction`.

If `C` holds for the `algebra_map` of `r : R` into `clifford_algebra Q`, the `ι` of `x : M`, and is
preserved under addition and muliplication, then it holds for all of `clifford_algebra Q`.
-/
@[elab_as_eliminator]
lemma induction {C : clifford_algebra Q → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (clifford_algebra Q) r))
  (h_grade1 : ∀ x, C (ι Q x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : clifford_algebra Q) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : subalgebra R (clifford_algebra Q) := {
    carrier := C,
    one_mem' := h_grade0 1,
    zero_mem' := h_grade0 0,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = algebra_map R s (Q m) } :=
  ⟨{
    to_fun := λ x, ⟨(ι Q) x, h_grade1 x⟩,
    map_add' := λ x y, by { simp_rw (ι Q).map_add x y, refl, },
    map_smul' := λ c x, by { simp_rw (ι Q).map_smul c x, refl, }, },
    λ m, begin
      change (⟨ι Q m * ι Q m, _⟩ : s) = ⟨algebra_map R (clifford_algebra Q) (Q m), _⟩,
      simp_rw ι_square_scalar,
    end ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of of.prop),
  { ext,
    simp [of, subtype.coind], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of.1 of.prop a),
  simp [alg_hom.ext_iff] at of_id,
  exact of_id a,
end

#check algebra.adjoin

variables (Q)
/-- The versors are the elements made up of products of vectors.begin

TODO: are scalars ≠1 considered versors? -/
def versors := submonoid.closure (set.range (algebra_map R _) ∪ set.range (ι Q) )

variables {Q}

namespace versors

  @[simp] lemma ι_mem (m : M) : ι Q m ∈ versors Q :=
  submonoid.subset_closure $ or.inr $ set.mem_range_self m

  @[simp] lemma algebra_map_mem (r : R) : algebra_map R _ r ∈ versors Q :=
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

  @[simp] lemma algebra_map_mem (r : R) : algebra_map R _ r ∈ rotors Q :=
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

  /-- Since the sets are monotonic, we can coerce up to a large set -/
  instance (n r) : has_coe_t (r_multivectors Q n) (r_multivectors Q $ n + r) :=
  { coe := λ x, ⟨x, submodule.le_def'.mpr ((r_multivectors Q).mono (nat.le_add_right n r)) x.prop⟩ }

end r_multivectors
  begin
    rw submodule.supr_eq_span,
    suffices : (⋃ (i : ℕ), (r_multivectors Q i : set (clifford_algebra Q))) = ⊤,
    { simp [this] },
    refine set.eq_univ_of_forall (λ x, _),
    simp only [set.mem_Union, submodule.mem_coe],
    exact exists_r x,
  end

end r_multivectors

section involute

  /-- Grade involution, inverting the sign of each basis vector -/
  def involute : clifford_algebra Q →ₐ[R] clifford_algebra Q :=
  clifford_algebra.lift Q (-(ι Q)) $ λ m, by simp

  @[simp]
  lemma involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  by simp [involute]

  @[simp]
  lemma involute_algebra_map (r : R) : involute (algebra_map R (clifford_algebra Q) r) = algebra_map R _ r :=
  by simp [involute]

  lemma involute_involutive : function.involutive (involute : clifford_algebra Q → clifford_algebra Q) :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

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

  lemma involute_prod_map_ι (l : list M) : involute (l.map $ ι Q).prod = ((-1 : R)^l.length) • (l.map $ ι Q).prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [pow_add, hxs],
  end

end involute

section reverse
  open opposite

  /-- Grade reversion, inverting the multiplication order of basis vectors -/
  def reverse : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
  (op_linear_equiv R).symm.to_linear_map.comp (
    clifford_algebra.lift Q ((opposite.op_linear_equiv R).to_linear_map.comp (ι Q))
      $ λ m, unop_injective $ by simp).to_linear_map

  @[simp]
  lemma reverse_ι (m : M) : reverse (ι Q m) = ι Q m :=
  by simp [reverse]

  @[simp]
  lemma reverse_algebra_map (r : R) : reverse (algebra_map R (clifford_algebra Q) r) = algebra_map R _ r :=
  by simp [reverse]

  @[simp]
  lemma reverse_one  : reverse (1 : clifford_algebra Q) = 1 :=
  reverse_algebra_map 1

  @[simp]
  lemma reverse_mul (a b : clifford_algebra Q) : reverse (a * b) = reverse b * reverse a :=
  by simp [reverse]

  lemma reverse_involutive : function.involutive (reverse : clifford_algebra Q → clifford_algebra Q) :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

  lemma reverse_prod_map_ι (l : list M) : reverse (l.map $ ι Q).prod = (l.map $ ι Q).reverse.prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [hxs],
  end

  lemma reverse_involute_commute : function.commute (reverse : clifford_algebra Q → clifford_algebra Q) involute :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

  /-- helper lemma for expanding the sign of reverse -/
  lemma reverse_prod_sign_aux (n : ℕ) :
    (-1 : R)^((n + 1)*(n + 1 + 1)/2) = (-1 : R)^(n*(n + 1)/2) * (-1 : R)^(n + 1) :=
  begin
    -- work with just the exponents
    rw ←pow_add,
    conv_rhs { rw neg_one_pow_eq_pow_mod_two },
    conv_lhs { rw neg_one_pow_eq_pow_mod_two },
    congr' 1,
    -- work through the ugly nat proof
    rw [add_mul, one_mul, mul_add _ (n + 1), mul_one, add_assoc, add_assoc n 1 1, ←add_assoc n n, ←mul_two, ←mul_two],
    have : 0 < 2 := by linarith,
    rw [nat.add_div_eq_of_add_mod_lt _, nat.add_div_eq_of_add_mod_lt _, nat.mul_div_cancel _ this, nat.mul_div_cancel _ this],
    -- extra goals created by `add_div_eq_of_add_mod_lt`
    { rw [nat.mul_mod_left, nat.mul_mod_left, zero_add],
      exact this },
    { rw [nat.add_mod (n * 2), nat.mul_mod_left, nat.mul_mod_left, add_zero, nat.zero_mod, add_zero],
      exact nat.mod_lt _ this },
  end
  
  /-- TODO: this needs an assumption that the vectors are othogonal -/
  lemma reverse_prod_map_sign (l : list M):
    reverse (l.map $ ι Q).prod = ((-1 : R)^(l.length*(l.length + 1)/2)) • (l.map $ ι Q).prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [hxs, reverse_prod_sign_aux, mul_smul],
    congr,
    sorry, -- this needs to be an assumption
  end

end reverse

section grades'

  abbreviation grade_type := zmod 2

  /--
  Separate an element of the clifford algebra into its `zmod 2`-graded components.

  This is defined as an `alg_hom` to `add_monoid_algebra` so that algebra operators can be moved
  before and after the mapping.

  This is _not_ the normal ℕ-graded definition that we usually use in GA. That definition is harder...
  -/
  noncomputable
  def grades' : (clifford_algebra Q) →ₐ[R] add_monoid_algebra (clifford_algebra Q) (grade_type) :=
  lift Q ((finsupp.lsingle 1).comp (ι Q)) $ λ x, begin
    rw [linear_map.comp_apply, finsupp.lsingle_apply, add_monoid_algebra.single_mul_single],
    simp,
    congr,
  end


  /-- Recombining the grades recovers the original element-/
  lemma sum_id_grades :
    (add_monoid_algebra.sum_id R).comp grades' = alg_hom.id R (clifford_algebra Q) :=
  begin
    ext,
    simp [grades', add_monoid_algebra.sum_id_apply, finsupp.sum_single_index],
  end

  noncomputable
  instance : has_coe (add_monoid_algebra (clifford_algebra Q) grade_type) (clifford_algebra Q) := ⟨
    (add_monoid_algebra.sum_id R : add_monoid_algebra (clifford_algebra Q) grade_type →ₐ[R] (clifford_algebra Q))
  ⟩

  @[simp, norm_cast]
  lemma coe_def (x : add_monoid_algebra (clifford_algebra Q) grade_type) : (x : clifford_algebra Q) = add_monoid_algebra.sum_id R x := rfl


  /-- An element of `R` lifted with `algebra_map` has a single grade 0 element -/
  lemma grades'.map_algebra_map (r : R) :
    grades' (algebra_map R (clifford_algebra Q) r) = finsupp.single 0 (algebra_map R _ r) :=
  by simp

  /-- An element of `X` lifted with the canonical `ι R` function has a single grade 1 element -/
  lemma grades'.map_ι (x : M) :
    grades' (ι Q x) = finsupp.single 1 (ι Q x) :=
  by simp [grades']

  -- note this is true for any `zero_hom`, not just `grades'`. Of course, then we need to repeat this
  -- for `add_monoid_hom`, `add_equiv`, `linear_map`, `ring_hom`, `ring_equiv`, `alg_hom`, ...
  private lemma map_single_apply (x : clifford_algebra Q) (i j : grade_type) :
    grades' (finsupp.single i x j) = finsupp.single i (grades' x) j :=
  by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades', grades'.map_zero]

  -- The grade-`i` part consists only of itself -/
  @[simp]
  lemma grades'.map_grades' (x : clifford_algebra Q) (i : grade_type) :
    grades' (grades' x i) = finsupp.single i (grades' x i) :=
  begin
    induction x using clifford_algebra.induction generalizing i,
    case h_grade0 : {
      rw [grades'.map_algebra_map, map_single_apply, grades'.map_algebra_map,
        finsupp.single_of_single_apply],
    },
    case h_grade1 : {
      rw [grades'.map_ι, map_single_apply, grades'.map_ι,
        finsupp.single_of_single_apply],
    },
    case h_add : x y hx hy {
      rw [grades'.map_add, finsupp.add_apply, grades'.map_add, finsupp.single_add, hx, hy],
    },
    case h_mul : f g hx hy {
      rw grades'.map_mul,
      rw add_monoid_algebra.mul_def,
      simp_rw [finsupp.sum_apply],

      -- pull the sums to the outside
      have : finsupp.single i = finsupp.single_add_hom i := rfl,
      rw this,
      simp_rw alg_hom.map_finsupp_sum,
      simp_rw add_monoid_hom.map_finsupp_sum,
      simp_rw finsupp.sum,
      congr, ext1 fi,
      congr, ext1 gi,
      rw ←this,

      -- this proof now resembles the other three
      rw [map_single_apply, grades'.map_mul,
        finsupp.single_of_single_apply],
      rw [hx, hy, add_monoid_algebra.single_mul_single],
    },
  end

end grades'

end clifford_algebra
