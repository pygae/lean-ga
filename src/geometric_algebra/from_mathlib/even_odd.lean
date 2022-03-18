/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.grading
import linear_algebra.quadratic_form.prod
import linear_algebra.dfinsupp
import linear_algebra.quadratic_form.prod
import algebra.algebra.subalgebra.basic
import algebra.direct_sum.internal
import data.zmod.basic
import geometric_algebra.from_mathlib.fold

/-!
# Grading by ℤ / 2ℤ, using `direct_sum`

This file is an alternative to the `add_monoid_algebra` approach using `direct_sum`.

The main result is now in mathlib, as `clifford_algebra.graded_algebra`.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

/-- The embedding of pairs of vectors into the even subalgebra, as a bilinear map. -/
@[simps]
def even.ι : M →ₗ[R] M →ₗ[R] even Q :=
linear_map.mk₂ R (λ m₁ m₂, ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_even_odd_zero _ _ _⟩)
  (λ _ _ _, by { simp only [linear_map.map_add, add_mul], refl })
  (λ _ _ _, by { simp only [linear_map.map_smul, smul_mul_assoc], refl })
  (λ _ _ _, by { simp only [linear_map.map_add, mul_add], refl })
  (λ _ _ _, by { simp only [linear_map.map_smul, mul_smul_comm], refl })

@[simp] lemma even.ι_same (m : M) : even.ι Q m m = algebra_map R _ (Q m) :=
subtype.ext $ ι_sq_scalar Q m

@[simp] lemma even.ι_contract (m₁ m₂ m₃ : M) :
  even.ι Q m₁ m₂ * even.ι Q m₂ m₃ = Q m₂ • even.ι Q m₁ m₃ :=
subtype.ext $
  calc  ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃)
      = ι Q m₁ * ((ι Q m₂ * ι Q m₂) * ι Q m₃) : by simp only [mul_assoc]
  ... = Q m₂ • (ι Q m₁ * ι Q m₃) : by rw [algebra.smul_def, ι_sq_scalar, algebra.left_comm]

variables {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] M →ₗ[R] A)

/-- Two algebra morphisms from the even subalgebra are equal if they agree on pairs of generators.
-/
@[ext]
lemma even.alg_hom_ext ⦃f g : even Q →ₐ[R] A⦄
  (h : (even.ι Q).compr₂ f.to_linear_map = (even.ι Q).compr₂ g.to_linear_map) :
  f = g :=
begin
  ext ⟨x, hx⟩,
  refine even_induction _ _ _ _ _ hx,
  { intro r,
    exact (f.commutes r).trans (g.commutes r).symm },
  { intros x y hx hy ihx ihy,
    have := congr_arg2 (+) ihx ihy,
    exact (f.map_add _ _).trans (this.trans $ (g.map_add _ _).symm) },
  { intros m₁ m₂ x hx ih,
    have := congr_arg2 (*) (linear_map.congr_fun (linear_map.congr_fun h m₁) m₂) ih,
    exact (f.map_mul _ _).trans (this.trans $ (g.map_mul _ _).symm) },
end

namespace even.lift

/-- An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`.  -/
private def S : submodule R (M →ₗ[R] A) :=
submodule.span R {f' | ∃ x m₂, f' = (algebra.lmul_right R x).comp (f.flip m₂)}

/-- An auxiliary bilinear map that is later passed into `clifford_algebra.fold` .-/
private def f_fold : M →ₗ[R] (A × S f) →ₗ[R] (A × S f) :=
linear_map.mk₂ R (λ m acc,
  (acc.2 m, ⟨(algebra.lmul_right R acc.1).comp (f.flip m), submodule.subset_span $ ⟨_, _, rfl⟩⟩))
  (λ m₁ m₂ a, prod.ext
    (linear_map.map_add _ m₁ m₂)
    (subtype.ext $ linear_map.ext $ λ m₃,
      show f m₃ (m₁ + m₂) * a.1 = f m₃ m₁ * a.1 + f m₃ m₂ * a.1,
      by rw [map_add, add_mul]))
  (λ c m a, prod.ext
    (linear_map.map_smul _ c m)
    (subtype.ext $ linear_map.ext $ λ m₃,
      show f m₃ (c • m) * a.1 = c • (f m₃ m * a.1),
      by rw [linear_map.map_smul, smul_mul_assoc]))
  (λ m a₁ a₂, prod.ext rfl (subtype.ext $ linear_map.ext $ λ m₃, mul_add _ _ _))
  (λ c m a, prod.ext rfl (subtype.ext $ linear_map.ext $ λ m₃, mul_smul_comm _ _ _))

@[simp] lemma fst_f_fold_f_fold (m₁ m₂ : M) (x : A × S f) :
  (f_fold f m₁ (f_fold f m₂ x)).fst = f m₁ m₂ * x.fst := rfl

@[simp] lemma snd_f_fold_f_fold (m₁ m₂ m₃ : M) (x : A × S f) :
  ((f_fold f m₁ (f_fold f m₂ x)).snd : M →ₗ[R] A) m₃ = f m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ := rfl

lemma f_fold_f_fold (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (m : M) (x : A × S f) :
  f_fold f m (f_fold f m x) = Q m • x :=
begin
  obtain ⟨a, ⟨g, hg⟩⟩ := x,
  ext : 2,
  { change f m m * a = Q m • a,
    rw [algebra.smul_def, hf] },
  { ext m₁,
    change f _ _ * g m = Q m • g m₁,
    apply submodule.span_induction' _ _ _ _ hg,
    { rintros _ ⟨b, m₃, rfl⟩,
      change f _ _ * (f _ _ * b) = Q m • (f _ _ * b),
      rw [←smul_mul_assoc, ←mul_assoc, hf₂] },
    { change f m₁ m * 0 = Q m • 0,
      rw [mul_zero, smul_zero] },
    { rintros x hx y hy ihx ihy,
      rw [linear_map.add_apply, linear_map.add_apply, mul_add, smul_add, ihx, ihy] },
    { rintros x hx c ihx,
      rw [linear_map.smul_apply, linear_map.smul_apply, mul_smul_comm, ihx, smul_comm] } },
end

lemma f_fold_comp_f_fold (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (m : M) :
  f_fold f m ∘ₗ f_fold f m = Q m • linear_map.id :=
linear_map.ext (f_fold_f_fold Q f hf hf₂ m)

/-- The final auxiliary construction for `clifford_algebra.even.lift`. -/
@[simps]
def aux (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  clifford_algebra.even Q →ₗ[R] A :=
begin
  refine _ ∘ₗ (even Q).val.to_linear_map,
  exact linear_map.fst _ _ _ ∘ₗ foldr Q (f_fold f) (f_fold_comp_f_fold Q f hf hf₂) (1, 0),
end

@[simp] lemma aux_one
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  aux Q f hf hf₂ 1 = 1 :=
(congr_arg prod.fst (foldr_one _ _ _ _))

@[simp] lemma aux_ι
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃)
  (m₁ m₂ : M) :
  aux Q f hf hf₂ (even.ι Q m₁ m₂) = f m₁ m₂ :=
(congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans begin
  rw [foldr_ι, foldr_ι],
  exact mul_one _,
end

@[simp] lemma aux_algebra_map
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (r) (hr) :
  aux Q f hf hf₂ ⟨algebra_map R _ r, hr⟩ = algebra_map R _ r :=
(congr_arg prod.fst (foldr_algebra_map _ _ _ _ _)).trans (algebra.algebra_map_eq_smul_one r).symm

@[simp] lemma aux_mul
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (x y : even Q) :
  aux Q f hf hf₂ (x * y) = aux Q f hf hf₂ x * aux Q f hf hf₂ y :=
begin
  cases x,
  cases y,
  refine (congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans _,
  dsimp only,
  refine even_induction Q _ _ _ _ x_property,
  { intros r,
    rw [foldr_algebra_map, aux_algebra_map],
    exact (algebra.smul_def r _), },
  { intros x y hx hy ihx ihy,
    rw [linear_map.map_add, prod.fst_add, ihx, ihy, ←add_mul, ←linear_map.map_add],
    refl, },
  { rintros m₁ m₂ x (hx : x ∈ even Q) ih,
    rw [aux_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold, ih,
      ←mul_assoc, subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold],
      refl }
end

end even.lift

open even.lift

variables (A)

/-- The type of bilinear maps which are accepted by `clifford_algebra.even.lift`. -/
@[reducible]
def even_hom : Type* :=
{ f : M →ₗ[R] M →ₗ[R] A //
  (∀ m, f m m = algebra_map R _ (Q m)) ∧ (∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) }

variables {A}

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
def even.lift :
  even_hom Q A ≃ (clifford_algebra.even Q →ₐ[R] A) :=
{ to_fun := λ f, alg_hom.of_linear_map
    (aux Q f f.prop.1 f.prop.2) (aux_one Q f f.prop.1 f.prop.2) (aux_mul Q f f.prop.1 f.prop.2),
  inv_fun := λ F, ⟨(even.ι Q).compr₂ F.to_linear_map,
    λ m, (F.congr_arg $ even.ι_same _ _).trans $ F.commutes _,
    λ m₁ m₂ m₃,
      (F.map_mul _ _).symm.trans $ (F.congr_arg $ even.ι_contract _ _ _ _).trans $ F.map_smul _ _⟩,
  left_inv := λ f, subtype.ext $ linear_map.ext₂ $ even.lift.aux_ι Q _ _ _,
  right_inv := λ F, even.alg_hom_ext Q $ linear_map.ext₂ $ even.lift.aux_ι Q _ _ _ }

@[simp] lemma even.lift_ι (f : even_hom Q A) (m₁ m₂ : M) :
  even.lift Q f (even.ι Q m₁ m₂) = f m₁ m₂ :=
even.lift.aux_ι _ _ _ _ _ _

end clifford_algebra
