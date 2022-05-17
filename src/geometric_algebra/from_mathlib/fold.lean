/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.prod
import linear_algebra.clifford_algebra.grading

/-!
# Recursive computation rules

## Main definitions

* `clifford_algebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra.
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables {N : Type u3} [add_comm_group N] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

/-- Fold a bilinear map along the generators of a term of the clifford algebra.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m, (f m).comp (f m) = (Q m) • linear_map.id) :
  N →ₗ[R] clifford_algebra Q →ₗ[R] N :=
(clifford_algebra.lift Q ⟨f, hf⟩).to_linear_map.flip

@[simp] lemma foldr_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) :
  foldr Q f hf n (ι Q m) = f m n :=
linear_map.congr_fun (lift_ι_apply _ _ _) n

@[simp] lemma foldr_algebra_map (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
  foldr Q f hf n (algebra_map R _ r) = r • n :=
linear_map.congr_fun (alg_hom.commutes _ r) n

@[simp] lemma foldr_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
  foldr Q f hf n 1 = n :=
linear_map.congr_fun (alg_hom.map_one _) n

@[simp] lemma foldr_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : clifford_algebra Q) :
  foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
linear_map.congr_fun (alg_hom.map_mul _ _ _) n

lemma foldr_induction {P : clifford_algebra Q → Prop}
  (hr : ∀ r : R, P (algebra_map _ _ r))
  (h_add : ∀ x y, P x → P y → P (x + y))
  (h_ι_mul : ∀ m x, P x → P (ι Q m * x)) : ∀ x, P x :=
-- begin
--   intro x,
--   let S : submodule R (clifford_algebra Q) :=
--   { carrier := set_of P, 
--     add_mem' := h_add,
--     smul_mem' := sorry,
--     zero_mem' := sorry },
--   let f : M →ₗ[R] S →ₗ[R] S :=
--   linear_map.mk₂ R (λ m s, ⟨ι Q m * s, h_ι_mul m s s.prop⟩) sorry sorry sorry sorry,
--   convert (foldr Q f sorry ⟨1, sorry⟩ x).prop,
--   rw foldr,
--   dsimp,
-- end
begin
  intro x,
  have : x ∈ ⊤ := submodule.mem_top, 
  rw ←supr_ι_range_eq_top at this,
  apply submodule.supr_induction _ this (λ i x hx, _) _ h_add,
  { refine submodule.pow_induction_on _ hr h_add (λ x, _) hx,
    rintro ⟨m, rfl⟩,
    exact h_ι_mul _ },
  { simpa only [map_zero] using hr 0}
end

end clifford_algebra
