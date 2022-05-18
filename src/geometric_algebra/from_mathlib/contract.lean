/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import geometric_algebra.from_mathlib.fold
import linear_algebra.clifford_algebra.grading


/-!
# Contraction in Clifford Algebras
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

namespace clifford_algebra

section foldr'
variables {N : Type*} [add_comm_group N] [module R N]

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

-- lemma snd_foldr'_aux_add
--   (f g : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) :
--     foldr'_aux Q (f + g) = foldr'_aux Q f + foldr'_aux Q g :=
-- begin
--   apply linear_map.ext (λ m, linear_map.ext (λ x, _)),
--   simp_rw [foldr'_aux_apply_apply, linear_map.add_apply, foldr'_aux_apply_apply,
--     prod.mk_add_mk],
-- end

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

/-- Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
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
--   { simp_rw [foldr'_ι_mul],
--     rw [hx],
--     rw hx,},
-- end

end foldr'

section apply_dual

variables (B : module.dual R M)

/-- Auxiliary construction for `clifford_algebra.apply_dual` -/
@[simps]
def apply_dual_aux (B : module.dual R M) :
  M →ₗ[R] clifford_algebra Q × clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  exact B.smul_right (linear_map.fst _ (clifford_algebra Q) (clifford_algebra Q)) -
        v_mul.compl₂ (linear_map.snd _ (clifford_algebra Q) _),
end

lemma apply_dual_aux_apply_dual_aux (v : M) (x : clifford_algebra Q) (fx : clifford_algebra Q) :
  apply_dual_aux Q B v (ι Q v * x, apply_dual_aux Q B v (x, fx)) = Q v • fx :=
begin
  simp only [apply_dual_aux_apply_apply],
  rw [mul_sub, ←mul_assoc, ι_sq_scalar, ←algebra.smul_def, ←sub_add, mul_smul_comm, sub_self,
    zero_add],
end

lemma apply_dual_aux_one_zero (v : M) : apply_dual_aux Q B v (1, 0) = algebra_map R _ (B v) :=
by simp_rw [apply_dual_aux_apply_apply, mul_zero, sub_zero, algebra.algebra_map_eq_smul_one]

/-- Contract an element of the exterior algebra with an element `B : module.dual R M`. -/
def apply_dual : module.dual R M →ₗ[R] clifford_algebra Q →ₗ[R] clifford_algebra Q :=
{ to_fun := λ B, foldr' Q (apply_dual_aux Q B) (apply_dual_aux_apply_dual_aux Q B) 0,
  map_add' := λ B₁ B₂, linear_map.ext $ λ x, begin
    rw linear_map.add_apply,
    apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
    { simp_rw [foldr'_algebra_map, smul_zero, zero_add] },
    { rw [map_add, map_add, map_add, add_add_add_comm, hx, hy] },
    { rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx],
      dsimp only [apply_dual_aux_apply_apply],
      rw [sub_add_sub_comm, mul_add, linear_map.add_apply, add_smul] }
  end,
  map_smul' := λ c B, linear_map.ext $ λ x,  begin
    rw [linear_map.smul_apply, ring_hom.id_apply],
    apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
    { simp_rw [foldr'_algebra_map, smul_zero] },
    { rw [map_add, map_add, smul_add, hx, hy] },
    { rw [foldr'_ι_mul, foldr'_ι_mul, hx],
      dsimp only [apply_dual_aux_apply_apply],
      rw [linear_map.smul_apply, smul_assoc, mul_smul_comm, smul_sub], }
  end }

@[simp] lemma apply_dual_ι (x : M) : apply_dual Q B (ι Q x) = algebra_map R _ (B x) :=
(foldr'_ι _ _ _ _ _).trans $ apply_dual_aux_one_zero _ _ _

@[simp] lemma apply_dual_algebra_map (r : R) : apply_dual Q B (algebra_map R _ r) = 0 :=
(foldr'_algebra_map _ _ _ _ _).trans $ smul_zero _

@[simp] lemma apply_dual_one : apply_dual Q B 1 = 0 :=
by simpa only [map_one] using apply_dual_algebra_map Q B 1

lemma apply_dual_ι_mul (a : M) ( b : clifford_algebra Q) :
  apply_dual Q B (ι Q a * b) = B a • b - ι Q a * apply_dual Q B b :=
foldr'_ι_mul _ _ _ _ _ _

lemma apply_dual_apply_dual (x : clifford_algebra Q) :
  apply_dual Q B (apply_dual Q B x) = 0 :=
begin
  apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
  { simp_rw [apply_dual_algebra_map, map_zero] },
  { rw [map_add, map_add, hx, hy, add_zero] },
  { rw [apply_dual_ι_mul, map_sub, apply_dual_ι_mul, hx, linear_map.map_smul, mul_zero, sub_zero,
      sub_self], }
end

end apply_dual


/-- Auxiliary construction for `clifford_algebra.alpha` -/
@[simps]
def alpha_aux (B : bilin_form R M) : M →ₗ[R] clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ ι Q,
  exact v_mul - ((apply_dual Q) ∘ₗ B.to_lin) ,
end

lemma alpha_aux_alpha_aux (B : bilin_form R M) (v : M) (x : clifford_algebra Q) :
  alpha_aux Q B v (alpha_aux Q B v x) = (Q v - B v v) • x :=
begin
  simp only [alpha_aux_apply_apply],
  rw [mul_sub, ←mul_assoc, ι_sq_scalar, map_sub, apply_dual_ι_mul, ←sub_add, sub_sub_sub_comm,
    ←algebra.smul_def, bilin_form.to_lin_apply, sub_self, sub_zero, apply_dual_apply_dual, add_zero,
    sub_smul],
end

variables {Q}

variables {Q' Q'' : quadratic_form R M} {B B' : bilin_form R M}
variables (h : B.to_quadratic_form = Q' - Q) (h' : B'.to_quadratic_form = Q'' - Q')

/-- Convert between two algebras of different quadratic form -/
def alpha (h : B.to_quadratic_form = Q' - Q) :
  clifford_algebra Q →ₗ[R] clifford_algebra Q' :=
foldr Q (alpha_aux Q' B) (λ m, linear_map.ext $ λ x, (alpha_aux_alpha_aux Q' B m x).trans $
  begin
    dsimp [←bilin_form.to_quadratic_form_apply],
    rw [h, quadratic_form.sub_apply, sub_sub_cancel],
  end) 1

lemma alpha_algebra_map (r : R) : alpha h (algebra_map R _ r) = algebra_map R _ r :=
(foldr_algebra_map _ _ _ _ _).trans $ eq.symm $ algebra.algebra_map_eq_smul_one r

lemma alpha_ι (m : M) : alpha h (ι _ m) = ι _ m :=
(foldr_ι _ _ _ _ _).trans $ eq.symm $
  by rw [alpha_aux_apply_apply, mul_one, apply_dual_one, sub_zero]

lemma alpha_ι_mul (m : M) (x : clifford_algebra Q) :
  alpha h (ι _ m * x) = ι _ m * alpha h x - apply_dual Q' (bilin_form.to_lin B m) (alpha h x) :=
(foldr_mul _ _ _ _ _ _).trans $ begin rw foldr_ι, refl, end

lemma alpha_alpha (x : clifford_algebra Q) :
  alpha h' (alpha h x) = alpha (
    show (B + B').to_quadratic_form = _,
    from (congr_arg2 (+) h h').trans $ sub_add_sub_cancel' _ _ _) x :=
begin
  apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
  { simp_rw [alpha_algebra_map] },
  { rw [map_add, map_add, map_add, hx, hy] },
  { rw [alpha_ι_mul, map_sub, alpha_ι_mul, alpha_ι_mul, hx, sub_sub],
    rw [map_add, linear_map.add_apply, map_add, linear_map.add_apply],
    congr' 1,
    rw add_comm,
    congr' 1,
    rw ←hx,
    clear hx,
    generalize : alpha h x = y,
    apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) y,
    { simp_rw [alpha_algebra_map, apply_dual_algebra_map, map_zero] },
    { rw [map_add, map_add, map_add, map_add, hx, hy] },
    { simp_rw [alpha_ι_mul, apply_dual_ι_mul, map_sub, alpha_ι_mul, apply_dual_ι_mul],
        -- missing: theorem 23
      rw hx },
    sorry }

end

end clifford_algebra
