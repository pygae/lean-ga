/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.grading
import linear_algebra.quadratic_form.prod
import linear_algebra.dfinsupp
import linear_algebra.quadratic_form.prod
import algebra.algebra.subalgebra
import algebra.direct_sum.internal
import data.zmod.basic
import geometric_algebra.from_mathlib.fold

/-!
# Grading by ℤ / 2ℤ, using `direct_sum`

This file is an alternative to the `add_monoid_algebra` approach using `direct_sum`.

The main result is now in mathlib, as `clifford_algebra.graded_algebra`.
-/

section to_move

lemma commute.mul_self_sub_mul_self_eq {R} [ring R] {a b : R}(h : commute a b) :
  a * a - b * b = (a + b) * (a - b) :=
begin
  rw [add_mul, mul_sub, mul_sub, h.eq],
  abel,
end

lemma commute.mul_self_sub_mul_self_eq' {R} [ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a - b) * (a + b) :=
begin
  rw [mul_add, sub_mul, sub_mul, h.eq],
  abel,
end

def _root_.submodule.to_subalgebra {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (p : submodule R A)
  (h_one : (1 : A) ∈ p)
  (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : subalgebra R A :=
{ mul_mem' := h_mul,
  algebra_map_mem' := λ r, begin
    rw algebra.algebra_map_eq_smul_one,
    apply p.smul_mem _ h_one,
  end,
  ..p}

@[simp, to_additive] lemma prod.swap_mul {α β} [has_mul α] [has_mul β] (x y : α × β) :
  prod.swap (x * y) = prod.swap x * prod.swap y := rfl

end to_move

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)


lemma ι_mul_ι_mem_even_odd_zero (m₁ m₂ : M) :
  ι Q m₁ * ι Q m₂ ∈ even_odd Q 0 :=
submodule.mem_supr_of_mem ⟨2, rfl⟩ begin
  rw [subtype.coe_mk, pow_two],
  exact submodule.mul_mem_mul ((ι Q).mem_range_self m₁) ((ι Q).mem_range_self m₂),
end


attribute [elab_as_eliminator] submodule.pow_induction_on'

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

@[simps]
def even.ι : M →ₗ[R] M →ₗ[R] even Q :=
begin
  refine linear_map.mk₂ R (λ m₁ m₂, ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_even_odd_zero _ _ _⟩) _ _ _ _;
    intros,
  { simp only [linear_map.map_add, add_mul], refl },
  { simp only [linear_map.map_smul, smul_mul_assoc], refl },
  { simp only [linear_map.map_add, mul_add], refl },
  { simp only [linear_map.map_smul, mul_smul_comm], refl },
end

@[simp] lemma even.ι_same (m : M) : even.ι Q m m = algebra_map R _ (Q m) :=
subtype.ext $ ι_sq_scalar Q m


@[simp] lemma even.ι_contract (m₁ m₂ m₃ : M) :
  even.ι Q m₁ m₂ * even.ι Q m₂ m₃ = Q m₂ • even.ι Q m₁ m₃ :=
begin
  ext,
  dsimp only [subalgebra.coe_mul, subalgebra.coe_smul, even.ι_apply_apply_coe],
  rw [←mul_assoc _ (ι Q m₂), mul_assoc (ι Q m₁), ι_sq_scalar, mul_assoc, ← algebra.smul_def,
    mul_smul_comm],
end

/-- To show a property is true on the even subalgebra, it suffices to show it is true
on the scalars, closed under addition, and under left-multipliation by a pair of vectors. -/
lemma even_induction {P : Π x, x ∈ even_odd Q 0 → Prop}
  (hr : ∀ r, P (algebra_map R _ r) ((even Q).algebra_map_mem _))
  (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (submodule.add_mem _ hx hy))
  (hιι_mul: ∀ m₁ m₂ {x hx}, P x hx → P (ι Q m₁ * ι Q m₂ * x)
    ((even Q).mul_mem (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
  (x : clifford_algebra Q) (hx : x ∈ even_odd Q 0) : P x hx :=
begin
  apply submodule.supr_induction',
  { refine subtype.rec _,
    simp_rw [subtype.coe_mk, zmod.nat_coe_zmod_eq_zero_iff_dvd],
    rintros _ ⟨n, rfl⟩ x,
    simp_rw pow_mul,
    intro h,
    refine submodule.pow_induction_on' ((ι Q).range ^ 2) hr _ _ h,
    { intros x y n hx hy,
      apply hadd, },
    { intros x hx n y hy ihy,
      revert hx,
      simp_rw pow_two,
      intro hx,
      refine submodule.mul_induction_on' _ _ hx,
      { simp_rw linear_map.mem_range,
        rintros _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩,
        refine hιι_mul _ _ ihy, },
      { intros x hx y hy ihx ihy,
        simp_rw add_mul,
        apply hadd ihx ihy } } },
  { have := hr 0,
    simp_rw ring_hom.map_zero at this,
    exact this },
  { intros x y hx hy,
    apply hadd, }
end

notation `↑ₐ` := algebra_map _ (clifford_algebra _)

variables {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] M →ₗ[R] A)
namespace even.lift

def S : submodule R (M →ₗ[R] A) :=
submodule.span R {x | ∃ (acc1 : A) (m : M), x = (algebra.lmul_right R acc1).comp (f.flip m)}

def f_fold : M →ₗ[R] (A × (S f)) →ₗ[R] (A × (S f)) :=
linear_map.mk₂ R (λ m acc, (acc.2 m, ⟨(algebra.lmul_right R acc.1).comp (f.flip m),
  submodule.subset_span $ ⟨_, _, rfl⟩⟩))
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
  (λ m a₁ a₂, prod.ext rfl
    (subtype.ext $ linear_map.ext $ λ m₃, mul_add _ _ _))
  (λ c m a, prod.ext rfl
    (subtype.ext $ linear_map.ext $ λ m₃, mul_smul_comm _ _ _))

@[simp] lemma fst_f_fold_f_fold  (m₁ m₂ : M) (x : A × (S f)) :
  (f_fold f m₁ (f_fold f m₂ x)).fst = f m₁ m₂ * x.fst := rfl

@[simp] lemma snd_f_fold_f_fold (m₁ m₂ m₃ : M) (x : A × (S f)) :
  ((f_fold f m₁ (f_fold f m₂ x)).snd : M →ₗ[R] A) m₃ = f m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ := rfl

@[simp]
def folded_hom
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  (A × (S f)) →ₗ[R] clifford_algebra Q →ₗ[R] (A × (S f)) :=
@foldr R _ M _ _ (A × (S f)) _ _ Q (even.lift.f_fold f) $ λ m₂, linear_map.ext $ begin
  rintro ⟨a, ⟨g, hg⟩⟩,
  rw [linear_map.comp_apply],
  ext : 2,
  { change f m₂ m₂ * a = Q m₂ • a,
    rw [algebra.smul_def, hf] },
  { ext m₁,
    change f _ _ * g m₂ = Q m₂ • g m₁,
    apply submodule.span_induction' _ _ _ _ hg,
    { rintros _ ⟨b, m₃, rfl⟩,
      change f _ _ * (f _ _ * b) = Q m₂ • (f _ _ * b),
      rw [←smul_mul_assoc, ←mul_assoc, hf₂] },
    { change f m₁ m₂ * 0 = Q m₂ • 0,
      rw [mul_zero, smul_zero] },
    { rintros x hx y hy ihx ihy,
      rw [linear_map.add_apply, linear_map.add_apply, mul_add, smul_add, ihx, ihy] },
    { rintros x hx c ihx,
      rw [linear_map.smul_apply, linear_map.smul_apply, mul_smul_comm, ihx, smul_comm] } },
end

end even.lift

open even.lift

@[simps]
def even.liftₗ
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  clifford_algebra.even Q →ₗ[R] A :=
begin
  let F := (linear_map.fst _ _ _).comp (folded_hom Q f hf hf₂ (1, 0)),
  refine F.comp (even Q).val.to_linear_map
end

@[simp] lemma even.liftₗ_one
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  even.liftₗ Q f hf hf₂ 1 = 1 :=
(congr_arg prod.fst (foldr_one _ _ _ _))


@[simp] lemma even.liftₗ_ι
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃)
  (m₁ m₂ : M) :
  even.liftₗ Q f hf hf₂ (even.ι Q m₁ m₂) = f m₁ m₂ :=
(congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans begin
  rw [foldr_ι, foldr_ι],
  exact mul_one _,
end

@[simp] lemma even.liftₗ_algebra_map
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (r) :
  even.liftₗ Q f hf hf₂ ⟨algebra_map R _ r, subalgebra.algebra_map_mem _ _⟩ = algebra_map R _ r :=
(congr_arg prod.fst (foldr_algebra_map _ _ _ _ _)).trans
  (algebra.algebra_map_eq_smul_one r).symm

@[simp] lemma even.liftₗ_mul
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) (x y : even Q) :
  even.liftₗ Q f hf hf₂ (x * y) = even.liftₗ Q f hf hf₂ x * even.liftₗ Q f hf hf₂ y :=
begin
  cases x,
  cases y,
  refine (congr_arg prod.fst (foldr_mul _ _ _ _ _ _)).trans _,
  dsimp only,
  apply even_induction Q _ _ _ _ x_property,
  { intros r,
    rw [foldr_algebra_map, even.liftₗ_algebra_map],
    exact (algebra.smul_def r _), },
  { intros x y hx hy ihx ihy,
    rw [linear_map.map_add, prod.fst_add, ihx, ihy, ←add_mul, ←linear_map.map_add],
    refl, },
  { rintros m₁ m₂ x (hx : x ∈ even Q) ih,
    rw [even.liftₗ_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold, ih,
      ←mul_assoc, subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold],
      refl }
end

def even.lift
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) :
  clifford_algebra.even Q →ₐ[R] A :=
alg_hom.of_linear_map (even.liftₗ Q f hf hf₂)
  (even.liftₗ_one Q f hf hf₂)
  (even.liftₗ_mul Q f hf hf₂)

@[simp] lemma even.lift_ι
  (hf : ∀ m, f m m = algebra_map R _ (Q m))
  (hf₂ : ∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃)
  (m₁ m₂ : M) :
  even.lift Q f hf hf₂ (even.ι Q m₁ m₂) = f m₁ m₂ :=
even.liftₗ_ι _ _ _ _ _ _

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

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
def even.lift_equiv :
  { f : M →ₗ[R] M →ₗ[R] A //
      (∀ m, f m m = algebra_map R _ (Q m)) ∧
      (∀ m₁ m₂ m₃, f m₁ m₂ * f m₂ m₃ = Q m₂ • f m₁ m₃) } ≃
  (clifford_algebra.even Q →ₐ[R] A) :=
{ to_fun := λ f, even.lift Q f f.prop.1 f.prop.2,
  inv_fun := λ F, ⟨(even.ι Q).compr₂ F.to_linear_map,
    λ m, (F.congr_arg $ even.ι_same _ _).trans $ F.commutes _,
    λ m₁ m₂ m₃,
      (F.map_mul _ _).symm.trans $ (F.congr_arg $ even.ι_contract _ _ _ _).trans $ F.map_smul _ _⟩,
  left_inv := λ f, subtype.ext $ linear_map.ext $ λ m₁, linear_map.ext $ λ m₂,
    even.liftₗ_ι Q _ _ _ _ _,
  right_inv := λ F, even.alg_hom_ext Q $ linear_map.ext $ λ m₁, linear_map.ext $ λ m₂,
    even.liftₗ_ι Q _ _ _ _ _ }

end clifford_algebra
