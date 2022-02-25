/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.prod

/-!
# Contraction in Exterior Algebras

## Main definitions

* `clifford_algebra.fold`: a computation rule for building linear maps out of the exterior
  algebra.
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables {N : Type u3} [add_comm_group N] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

/-- Fold a bilinear map along the generators of a term of the exterior algebra.

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

end clifford_algebra
