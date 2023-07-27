/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

notation `↑ₐ`:max x:max := algebra_map _ _ x

namespace clifford_algebra

-- if this fails then you have the wrong branch of mathlib
example : ring (clifford_algebra Q) := infer_instance

variables (Q)
abbreviation clifford_hom (A : Type*) [semiring A] [algebra R A] :=
{ f : M →ₗ[R] A // ∀ m, f m * f m = ↑ₐ(Q m) }

instance {A : Type*} [ring A] [algebra R A] :
  has_zero (clifford_hom (0 : quadratic_form R M) A) :=
{ zero := ⟨0, λ m, by simp⟩ }

instance has_zero_of_subsingleton {A : Type*} [ring A] [algebra R A] [subsingleton A] :
  has_zero (clifford_hom Q A) :=
{ zero := ⟨0, λ m, subsingleton.elim _ _⟩ }

variables {Q}

/-- TODO: work out what the necessary conditions are here, then make this an instance -/
example : nontrivial (clifford_algebra Q) := sorry

/-- A wedge product of n vectors. Note this does not define the wedge product of arbitrary multivectors. -/
def ι_wedge (n : ℕ) [invertible (n.factorial : R)] : alternating_map R M (clifford_algebra Q) (fin n) :=
⅟(n.factorial : R) • ((multilinear_map.mk_pi_algebra_fin R n _).comp_linear_map (λ i, ι Q)).alternatization

end clifford_algebra
