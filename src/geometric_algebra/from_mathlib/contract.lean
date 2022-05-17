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

variables (B : module.dual R M)

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
  {N : Type*} [ add_comm_group N] [module R N]
    (f : M →ₗ[R] clifford_algebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx):
  (N →ₗ[R] clifford_algebra Q →ₗ[R] N) :=
(foldr Q (fold_twice_aux Q f)
  (fold_twice_aux_comp_fold_twice_aux Q _ hf) ∘ₗ linear_map.inr _ _ _).compr₂ (linear_map.snd _ _ _)


/-- The map `g v (x, y) = (ι Q v * x, -ι Q v * y + B v • x)` -/
@[simps?]
def apply_dual_aux' (B : module.dual R M) :
  M →ₗ[R] clifford_algebra Q × clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  exact -v_mul.compl₂ (linear_map.snd _ (clifford_algebra Q) _) +
            B.smul_right (linear_map.fst _ (clifford_algebra Q) (clifford_algebra Q)),
end

/-- The map `g v (x, y) = (ι Q v * x, -ι Q v * y + B v • x)` -/
def apply_dual_aux (B : module.dual R M) :
  M →ₗ[R] module.End R (clifford_algebra Q × clifford_algebra Q) :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  have l := v_mul.compl₂ (linear_map.fst _ _ (clifford_algebra Q)),
  have r := -v_mul.compl₂ (linear_map.snd _ (clifford_algebra Q) _) +
            B.smul_right (linear_map.fst _ (clifford_algebra Q) (clifford_algebra Q)),
  exact
    { to_fun := λ v, (l v).prod (r v),
      map_add' := λ v₂ v₂, linear_map.ext $ λ x, prod.ext
        (linear_map.congr_fun (l.map_add _ _) x) (linear_map.congr_fun (r.map_add _ _) x),
      map_smul' := λ c v, linear_map.ext $ λ x, prod.ext
        (linear_map.congr_fun (l.map_smul _ _) x) (linear_map.congr_fun (r.map_smul _ _) x), },
end

lemma apply_dual_aux_apply_apply (v : M) (x : clifford_algebra Q × clifford_algebra Q) :
  apply_dual_aux Q B v x = (ι Q v * x.fst, -(ι Q v * x.snd) + B v • x.fst) :=
rfl

lemma apply_dual_aux_apply_dual_aux (v : M) (x : clifford_algebra Q × clifford_algebra Q) :
  apply_dual_aux Q B v (apply_dual_aux Q B v x) = Q v • x :=
begin
  cases x,
  simp only [apply_dual_aux_apply_apply],
  rw [neg_mul_eq_mul_neg, neg_add, neg_neg, mul_add, mul_neg, mul_smul_comm,
    ←sub_eq_add_neg, sub_add_cancel, ←mul_assoc, ←mul_assoc, ι_sq_scalar, ←algebra.smul_def,
    ←algebra.smul_def, prod.smul_mk],
end

lemma apply_dual_aux_comp_apply_dual_aux (v : M) :
  apply_dual_aux Q B v ∘ₗ apply_dual_aux Q B v = algebra_map _ _ (Q v) :=
linear_map.ext $ apply_dual_aux_apply_dual_aux Q B v

lemma apply_dual_aux_one_zero (v : M) :
  apply_dual_aux Q B v (1, 0) = (ι Q v, algebra_map R _ (B v)) :=
by simp_rw [apply_dual_aux_apply_apply, mul_one, mul_zero, neg_zero, zero_add,
    algebra.algebra_map_eq_smul_one]

/-- Contract an element of the exterior algebra with an element `B : module.dual R M`. -/
def apply_dual : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
linear_map.snd _ _ _ ∘ₗ
  ((lift Q ⟨apply_dual_aux Q B, apply_dual_aux_comp_apply_dual_aux Q B⟩).to_linear_map.flip (1, 0))

lemma apply_dual_def (x : clifford_algebra Q) :
  apply_dual Q B x =
    (lift Q ⟨apply_dual_aux Q B, apply_dual_aux_comp_apply_dual_aux Q B⟩ x (1, 0)).2 := rfl

@[simp] lemma apply_dual_ι (x : M) : apply_dual Q B (ι Q x) = algebra_map R _ (B x) :=
by simp only [apply_dual_def, lift_ι_apply, apply_dual_aux_one_zero]

@[simp] lemma apply_dual_algebra_map (r : R) : apply_dual Q B (algebra_map R _ r) = 0 :=
by simp only [apply_dual_def, alg_hom.commutes, prod.smul_mk, module.algebra_map_End_apply,
  smul_zero]

@[simp] lemma apply_dual_one : apply_dual Q B 1 = 0 :=
by simpa only [map_one] using apply_dual_algebra_map Q B 1

/-- TODO: generalize `ι Q b` to an arbitrary element `b`. -/
lemma apply_dual_ι_mul_ι (a b : M) :
  apply_dual Q B (ι Q a * ι Q b) = apply_dual Q B (ι Q a) * ι Q b - ι Q a * apply_dual Q B (ι Q b) :=
begin
  dsimp [apply_dual_def],
  simp_rw [alg_hom.map_mul, linear_map.mul_apply, lift_ι_apply, apply_dual_aux_apply_apply, mul_zero, neg_zero,
    zero_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, neg_add_eq_sub],
end
/-- TODO: generalize `ι Q b` to an arbitrary element `b`. -/
lemma apply_dual_ι_mul (a : M) ( b : clifford_algebra Q) :
  apply_dual Q B (ι Q a * b) = -(ι Q a * apply_dual Q B b) + B a • b :=
begin
  have := congr_arg prod.snd (apply_dual_aux_apply_apply Q B a (b, apply_dual Q B b)),
  refine eq.trans _ this,
  rw [apply_dual_def, alg_hom.map_mul, linear_map.mul_apply],
  -- rw [apply_dual_def, alg_hom.map_mul, lift_ι_apply, linear_map.mul_apply],
  -- congr' 2,

  ---- Nope:
  -- apply clifford_algebra.foldr_induction _ (λ r, _) (λ x y hx hy, _) (λ m x hx, _) b,
  -- { simp_rw [← algebra.commutes, ←algebra.smul_def, linear_map.map_smul, apply_dual_ι,
  --     apply_dual_algebra_map, mul_zero, neg_zero, zero_add, algebra.smul_def, ←map_mul, mul_comm] },
  -- { rw [mul_add, map_add, map_add, mul_add, smul_add, neg_add, add_add_add_comm, hx, hy] },
  -- { rw [map_mul, lift_ι_apply, linear_map.mul_apply, hx, apply_dual_aux_apply_apply],


  ---- Also nope
  -- dsimp only,
  --   sorry},
  -- clear this,
  -- have : b ∈ ⊤ := submodule.mem_top,
  -- rw supr_ι_range_eq_top at this,
  -- rw [alg_hom.map_mul, lift_ι_apply],
  -- rw [apply_dual_def, apply_dual_def, lift_ι_apply, map_mul, lift_ι_apply,
  --   linear_map.mul_apply, apply_dual_aux_apply_apply, ←apply_dual_def,
  --   apply_dual_aux_one_zero, ←algebra.smul_def],
  -- dsimp only,
  -- congr' 2,
  -- induction b using clifford_algebra.induction,
  -- { simp_rw [alg_hom.commutes, module.algebra_map_End_apply, prod.smul_mk,
  --     apply_dual_algebra_map, algebra.algebra_map_eq_smul_one, smul_zero] },
  -- { simp_rw [lift_ι_apply, apply_dual_ι], sorry },
  -- case h_mul : a b ha hb {
  --     rw [map_mul, linear_map.mul_apply, hb], },
  -- suffices :
  --   ((lift Q ⟨apply_dual_aux Q B, apply_dual_aux_comp_apply_dual_aux Q B⟩).to_linear_map.flip (1, 0))
  --     = (linear_map.id : clifford_algebra Q →ₗ[R] clifford_algebra Q),
  -- { sorry },
end

end clifford_algebra
