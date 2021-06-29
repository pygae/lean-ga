/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.zmod.basic
import for_mathlib.algebra.monoid_algebra
import geometric_algebra.from_mathlib.basic

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
/-!
# Grading by ℤ / 2ℤ

This file defines the grading by `zmod 2`, as the function `clifford_algebra.grades'`.

## Main results

* `clifford_algebra.grades'_left_inverse`, `grades'` has a left-inverse, `add_monoid_algebra.sum_id`.
* `clifford_algebra.grades'.map_grades'`, `grades'` is idempotent
-/

namespace clifford_algebra

/--
Separate an element of the clifford algebra into its `zmod 2`-graded components.

This is defined as an `alg_hom` to `add_monoid_algebra` so that algebra operators can be moved
before and after the mapping.

This is _not_ the normal ℕ-graded definition that we usually use in GA. That definition is harder...
-/
noncomputable def grades' :
  (clifford_algebra Q) →ₐ[R] add_monoid_algebra (clifford_algebra Q) (zmod 2) :=
(lift Q : _) ⟨
  -- vectors are grade 1
  (add_monoid_algebra.lsingle 1).comp (ι Q),
  -- this requires 1 + 1 = 0, which is why we use `zmod 2` as our grading
  λ x, by { simp [add_monoid_algebra.single_mul_single], congr }⟩

/-- Recombining the grades recovers the original element-/
lemma sum_id_comp_grades' :
  (add_monoid_algebra.sum_id R).comp grades' = alg_hom.id R (clifford_algebra Q) :=
begin
  ext,
  simp [grades', add_monoid_algebra.sum_id_apply, finsupp.sum_single_index],
end

/-- Stated another way, `grades'` has a left-inverse and is therefore injective (via `function.left_inverse.injective`). -/
lemma grades'_left_inverse :
  function.left_inverse (add_monoid_algebra.sum_id R) ⇑(grades' : clifford_algebra Q →ₐ[R] _) :=
alg_hom.congr_fun sum_id_comp_grades'

noncomputable
instance : has_coe (add_monoid_algebra (clifford_algebra Q) (zmod 2)) (clifford_algebra Q) := ⟨
  (add_monoid_algebra.sum_id R : add_monoid_algebra (clifford_algebra Q) (zmod 2) →ₐ[R] (clifford_algebra Q))
⟩

@[simp, norm_cast]
lemma coe_def (x : add_monoid_algebra (clifford_algebra Q) (zmod 2)) : (x : clifford_algebra Q) = add_monoid_algebra.sum_id R x := rfl


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
private lemma map_single_apply (x : clifford_algebra Q) (i j : zmod 2) :
  grades' (finsupp.single i x j) = finsupp.single i (grades' x) j :=
by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades', grades'.map_zero]

-- The grade-`i` part consists only of itself -/
@[simp]
lemma grades'.map_grades' (x : clifford_algebra Q) (i : zmod 2) :
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

end clifford_algebra
