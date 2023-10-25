/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.bilinear_map

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
variables {A : Type*}

notation `↑ₐ`:max x:max := algebra_map _ _ x

namespace clifford_algebra

-- if this fails then you have the wrong branch of mathlib
example : ring (clifford_algebra Q) := infer_instance

variables (Q A)
abbreviation clifford_hom [semiring A] [algebra R A] :=
{ f : M →ₗ[R] A // ∀ m, f m * f m = ↑ₐ(Q m) }

variables {A}

lemma preserves_iff_bilin [ring A] [algebra R A] (h2 : is_unit (2 : R))
  (f : M →ₗ[R] A) :
  (∀ x, f x * f x = algebra_map _ _ (Q x)) ↔
    ((linear_map.mul R A).compl₂ f) ∘ₗ f + ((linear_map.mul R A).flip.compl₂ f) ∘ₗ f =
      Q.polar_bilin.to_lin.compr₂ (algebra.linear_map R A) :=
begin
  simp_rw fun_like.ext_iff,
  dsimp only [linear_map.compr₂_apply, linear_map.compl₂_apply, linear_map.comp_apply,
    algebra.linear_map_apply, linear_map.mul_apply', bilin_form.to_lin_apply, linear_map.add_apply,
    linear_map.flip_apply],
  have h2a := h2.map (algebra_map R A),
  refine ⟨λ h x y, _, λ h x, _⟩,
  { rw [quadratic_form.polar_bilin_apply, quadratic_form.polar, sub_sub, map_sub, map_add,
      ←h x, ←h y, ←h (x + y), eq_sub_iff_add_eq, map_add,
      add_mul, mul_add, mul_add, add_comm (f x * f x) (f x * f y),
      add_add_add_comm] },
  { apply h2a.mul_left_cancel,
    simp_rw [←algebra.smul_def, two_smul],
    rw [h x x, quadratic_form.polar_bilin_apply, quadratic_form.polar_self, two_mul, map_add], },
end

instance [ring A] [algebra R A] :
  has_zero (clifford_hom (0 : quadratic_form R M) A) :=
{ zero := ⟨0, λ m, by simp⟩ }

instance has_zero_of_subsingleton [ring A] [algebra R A] [subsingleton A] :
  has_zero (clifford_hom Q A) :=
{ zero := ⟨0, λ m, subsingleton.elim _ _⟩ }

variables {Q}

/-- TODO: work out what the necessary conditions are here, then make this an instance -/
example : nontrivial (clifford_algebra Q) := sorry

/-- A wedge product of n vectors. Note this does not define the wedge product of arbitrary multivectors. -/
def ι_wedge (n : ℕ) [invertible (n.factorial : R)] : alternating_map R M (clifford_algebra Q) (fin n) :=
⅟(n.factorial : R) • ((multilinear_map.mk_pi_algebra_fin R n _).comp_linear_map (λ i, ι Q)).alternatization

end clifford_algebra
