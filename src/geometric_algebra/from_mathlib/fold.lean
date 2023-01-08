/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.fold
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.prod
import linear_algebra.clifford_algebra.grading

/-!
# Recursive computation rules

## Main definitions

* `clifford_algebra.foldr'`: a computation rule for building linear maps out of the clifford
  algebra.

-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables {N : Type u3} [add_comm_group N] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

-- lemma foldr'_mul_ι (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
--   (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
--   foldr' Q f hf n (x * ι Q m) = foldr' Q f hf (f m (1, n)) x :=
-- begin
--   dsimp [foldr'],
--   rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply],
--   dsimp only,
--   rw mul_one,
--   refine congr_arg (f m) (prod.mk.eta.symm.trans _),
--   congr' 1,
--   apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
--   { simp_rw [foldr_algebra_map, prod.smul_mk, algebra.algebra_map_eq_smul_one] },
--   { rw [map_add, prod.fst_add, hx, hy] },
--   { rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply, hx], },
-- end
-- lemma foldr'_add
--   (f g : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
--   (hfg : ∀ m x fgx, (f + g) m (ι Q m * x, (f + g) m (x, fgx)) = Q m • fgx)
--   (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
--   (hg : ∀ m x gx, g m (ι Q m * x, g m (x, gx)) = Q m • gx) :
--   foldr' Q (f + g) hfg 0 = foldr' Q f hf 0 + foldr' Q g hg 0 :=
-- begin
--   ext x,
--   rw linear_map.add_apply,
--   apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
--   { simp_rw [foldr'_algebra_map, smul_zero, zero_add] },
--   { rw [map_add, map_add, map_add, add_add_add_comm, hx, hy] },
--   { simp_rw [foldr'_ι_mul],
--     rw [hx],
--     rw hx,},
-- end

-- lemma foldr'_smul (c : R)
--   (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
--   (hfg : ∀ m x fcx, (c • f) m (ι Q m * x, (c • f) m (x, fcx)) = Q m • fcx)
--   (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) :
--   foldr' Q (c • f) hfg 0 = c • foldr' Q f hf 0 :=
-- begin
--   ext x,
--   rw linear_map.smul_apply,
--   apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
--   { simp_rw [foldr'_algebra_map, smul_zero] },
--   { rw [map_add, map_add,smul_add, hx, hy] },
--   { simp_rw [foldr'_ι_mul, line],
--     rw [hx],
--     rw hx,},
-- end

end clifford_algebra
