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
* `clifford_algebra.foldr'`: a computation rule for building linear maps out of the clifford
  algebra.
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables {N : Type u3} [add_comm_group N] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

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
  { refine submodule.pow_induction_on_left _ hr h_add (λ x, _) hx,
    rintro ⟨m, rfl⟩,
    exact h_ι_mul _ },
  { simpa only [map_zero] using hr 0}
end


/-- Auxiliary definition for `clifford_algebra.foldr'` -/
def foldr'_aux (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) :
  M →ₗ[R] module.End R (clifford_algebra Q × N) :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  have l := v_mul.compl₂ (linear_map.fst _ _ N),
  exact { to_fun := λ m, (l m).prod (f m),
          map_add' := λ v₂ v₂, linear_map.ext $ λ x, prod.ext
            (linear_map.congr_fun (l.map_add _ _) x) (linear_map.congr_fun (f.map_add _ _) x),
          map_smul' := λ c v, linear_map.ext $ λ x, prod.ext
            (linear_map.congr_fun (l.map_smul _ _) x) (linear_map.congr_fun (f.map_smul _ _) x), },
end

lemma foldr'_aux_apply_apply (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    foldr'_aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) := rfl

lemma foldr'_aux_foldr'_aux (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (v : M) (x_fx) :
  foldr'_aux Q f v (foldr'_aux Q f v x_fx) = Q v • x_fx :=
begin
  cases x_fx with x fx,
  simp only [foldr'_aux_apply_apply],
  rw [←mul_assoc, ι_sq_scalar, ← algebra.smul_def, hf, prod.smul_mk],
end

lemma foldr'_aux_comp_foldr'_aux (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (v : M) :
  foldr'_aux Q f v ∘ₗ foldr'_aux Q f v = algebra_map _ _ (Q v) :=
linear_map.ext $ foldr'_aux_foldr'_aux Q f hf v

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `clifford_algebra.foldr`, but with an extra `x` argument.

Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def foldr' (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (n : N) :
  clifford_algebra Q →ₗ[R] N :=
linear_map.snd _ _ _ ∘ₗ foldr Q (foldr'_aux Q f) (foldr'_aux_comp_foldr'_aux Q _ hf) (1, n)

lemma foldr'_algebra_map (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
  foldr' Q f hf n (algebra_map R _ r) = r • n :=
congr_arg prod.snd (foldr_algebra_map _ _ _ _ _)

lemma foldr'_ι (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
  foldr' Q f hf n (ι Q m) = f m (1, n) :=
congr_arg prod.snd (foldr_ι _ _ _ _ _)

lemma foldr'_ι_mul (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
  foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) :=
begin
  dsimp [foldr'],
  rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply],
  refine congr_arg (f m) (prod.mk.eta.symm.trans _),
  congr' 1,
  apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
  { simp_rw [foldr_algebra_map, prod.smul_mk, algebra.algebra_map_eq_smul_one] },
  { rw [map_add, prod.fst_add, hx, hy] },
  { rw [foldr_mul, foldr_ι, foldr'_aux_apply_apply, hx], },
end

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
