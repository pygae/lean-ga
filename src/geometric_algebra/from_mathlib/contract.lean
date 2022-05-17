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

variables {N : Type*} [add_comm_group N] [module R N]

/-- Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def fold_twice_aux
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) :
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

lemma fold_twice_aux_apply_apply
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) (m : M) (x) (fx) :
    fold_twice_aux Q f m (x, fx) = (ι Q m * x, f m (x, fx)) := rfl

lemma fold_twice_aux_apply_apply_mk
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    fold_twice_aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) := rfl

lemma fold_twice_aux_fold_twice_aux 
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (v : M) (x) (fx) :
  fold_twice_aux Q f v (fold_twice_aux Q f v (x, fx)) = Q v • (x, fx) :=
begin
  simp only [fold_twice_aux_apply_apply],
  rw [←mul_assoc, ι_sq_scalar, ← algebra.smul_def, hf, prod.smul_mk],
end

lemma fold_twice_aux_comp_fold_twice_aux
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (v : M) :
  fold_twice_aux Q f v ∘ₗ fold_twice_aux Q f v = algebra_map _ _ (Q v) :=
linear_map.ext $ prod.rec $ by exact fold_twice_aux_fold_twice_aux Q f hf v

/-- Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def fold_twice
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx)
  (n : N) :
  clifford_algebra Q →ₗ[R] N :=
linear_map.snd _ _ _ ∘ₗ
  (foldr Q (fold_twice_aux Q f) (fold_twice_aux_comp_fold_twice_aux Q _ hf)) (1, n)

lemma fold_twice_algebra_map
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
  fold_twice Q f hf n (algebra_map R _ r) = r • n :=
congr_arg prod.snd (foldr_algebra_map _ _ _ _ _)

lemma fold_twice_ι 
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
  fold_twice Q f hf n (ι Q m) = f m (1, n) :=
congr_arg prod.snd (foldr_ι _ _ _ _ _)

lemma fold_twice_ι_mul 
  (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
  (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x):
  fold_twice Q f hf n (ι Q m * x) = f m (x, fold_twice Q f hf n x) :=
begin
  dsimp [fold_twice],
  rw [foldr_mul, foldr_ι, fold_twice_aux_apply_apply_mk],
  refine congr_arg (f m) (prod.mk.eta.symm.trans _),
  congr' 1,
  apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) x,
  { simp_rw [foldr_algebra_map, prod.smul_mk, algebra.algebra_map_eq_smul_one] },
  { rw [map_add, prod.fst_add, hx, hy] },
  { rw [foldr_mul, foldr_ι, fold_twice_aux_apply_apply_mk, hx], },
end

variables (B : module.dual R M)

/-- The map `g v (x, y) = (ι Q v * x, -ι Q v * y + B v • x)` -/
@[simps]
def apply_dual_aux (B : module.dual R M) :
  M →ₗ[R] clifford_algebra Q × clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  exact -v_mul.compl₂ (linear_map.snd _ (clifford_algebra Q) _) +
            B.smul_right (linear_map.fst _ (clifford_algebra Q) (clifford_algebra Q)),
end

lemma apply_dual_aux_apply_dual_aux (v : M) (x : clifford_algebra Q) (fx : clifford_algebra Q) :
  apply_dual_aux Q B v (ι Q v * x, apply_dual_aux Q B v (x, fx)) = Q v • fx :=
begin
  simp only [apply_dual_aux_apply_apply],
  rw [neg_mul_eq_mul_neg, neg_add, neg_neg, mul_add, mul_neg, mul_smul_comm,
    ←sub_eq_add_neg, sub_add_cancel, ←mul_assoc, ι_sq_scalar, ←algebra.smul_def],
end

lemma apply_dual_aux_one_zero (v : M) :
  apply_dual_aux Q B v (1, 0) = algebra_map R _ (B v) :=
by simp_rw [apply_dual_aux_apply_apply, mul_zero, neg_zero, zero_add,
    algebra.algebra_map_eq_smul_one]

/-- Contract an element of the exterior algebra with an element `B : module.dual R M`. -/
def apply_dual : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
fold_twice Q (apply_dual_aux Q B) (apply_dual_aux_apply_dual_aux Q B) 0

@[simp] lemma apply_dual_ι (x : M) : apply_dual Q B (ι Q x) = algebra_map R _ (B x) :=
(fold_twice_ι _ _ _ _ _).trans $ apply_dual_aux_one_zero _ _ _

@[simp] lemma apply_dual_algebra_map (r : R) : apply_dual Q B (algebra_map R _ r) = 0 :=
(fold_twice_algebra_map _ _ _ _ _).trans $ smul_zero _

@[simp] lemma apply_dual_one : apply_dual Q B 1 = 0 :=
by simpa only [map_one] using apply_dual_algebra_map Q B 1

lemma apply_dual_ι_mul (a : M) ( b : clifford_algebra Q) :
  apply_dual Q B (ι Q a * b) = -(ι Q a * apply_dual Q B b) + B a • b :=
fold_twice_ι_mul _ _ _ _ _ _

end clifford_algebra
