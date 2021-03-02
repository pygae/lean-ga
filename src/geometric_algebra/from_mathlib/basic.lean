/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra
import missing_from_mathlib

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
variables {Q}

/-- TODO: work out what the necessary conditions are here, then make this an instance -/
example : nontrivial (clifford_algebra Q) := sorry

/-- symmetric product of vectors is a scalar -/
lemma vec_symm_prod (a b : M) : ι Q a * ι Q b + ι Q b * ι Q a = ↑ₐ(quadratic_form.polar Q a b) :=
calc ι Q a * ι Q b + ι Q b * ι Q a
      = ι Q (a + b) * ι Q (a + b) - ι Q a * ι Q a - ι Q b * ι Q b :
          by { rw [(ι Q).map_add, mul_add, add_mul, add_mul], abel, }
  ... = ↑ₐ(Q $ a + b) - ↑ₐ(Q a) - ↑ₐ(Q b) :
          by rw [ι_square_scalar, ι_square_scalar, ι_square_scalar]
  ... = ↑ₐ(Q (a + b) - Q a - Q b) :
          by rw [←ring_hom.map_sub, ←ring_hom.map_sub]
  ... = ↑ₐ(quadratic_form.polar Q a b) : rfl

/-- A wedge product of n vectors. Note this does not define the wedge product of arbitrary multivectors. -/
def ι_wedge (n : ℕ) [invertible (n.factorial : R)] : alternating_map R M (clifford_algebra Q) (fin n) :=
⅟(n.factorial : R) • ((multilinear_map.mk_pi_algebra_fin R n _).comp_linear_map (λ i, ι Q)).alternatization

end clifford_algebra
