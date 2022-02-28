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

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)

def _root_.submodule.to_subalgebra {A : Type*} [semiring A] [algebra R A] (p : submodule R A)
  (h_one : (1 : A) ∈ p)
  (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : subalgebra R A :=
{ mul_mem' := h_mul,
  algebra_map_mem' := λ r, begin
    rw algebra.algebra_map_eq_smul_one,
    apply p.smul_mem _ h_one,
  end,
  ..p}

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

namespace equiv_even

@[reducible]
def Q' : quadratic_form R (M × R) := (Q.prod $ -@quadratic_form.sq R _)

/-- The unit vector in the new dimension -/
def e0 : clifford_algebra (Q' Q) := ι (Q' Q) (0, 1)

lemma eq_smul_e0 (r : R) : ι (Q' Q) (0, r) = r • e0 Q :=
by rw [e0, ←linear_map.map_smul, prod.smul_mk, smul_zero, smul_eq_mul, mul_one]

lemma e0_mul_e0 : e0 Q * e0 Q = -1 :=
(ι_sq_scalar _ _).trans begin
  simp,
end

lemma neg_e0_mul_ι (m : M) : -(e0 Q * ι _ (m, 0)) = ι _ (m, 0) * e0 Q :=
begin
  refine neg_eq_of_add_eq_zero ((ι_mul_ι_add_swap _ _).trans _),
  dsimp [quadratic_form.polar],
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero, quadratic_form.map_zero,
    add_sub_cancel, sub_self, map_zero, zero_sub],
end

lemma neg_ι_mul_e0 (m : M) : -(ι _ (m, 0) * e0 Q) = e0 Q * ι _ (m, 0) :=
begin
  rw neg_eq_iff_neg_eq,
  exact neg_e0_mul_ι _ m
end

/-- The embedding from the smaller algebra into the new larger one. -/
def to_even : clifford_algebra Q →ₐ[R] clifford_algebra.even (Q' Q) :=
begin
  refine clifford_algebra.lift Q ⟨_, λ m, _⟩,
  { refine linear_map.cod_restrict _ _ (λ m, submodule.mem_supr_of_mem ⟨2, rfl⟩ _),
    exact (algebra.lmul_left R $ e0 Q).comp ((ι _).comp $ linear_map.inl R M R),
    rw [subtype.coe_mk, pow_two],
    exact submodule.mul_mem_mul (linear_map.mem_range_self _ _) (linear_map.mem_range_self _ _), },
  { ext1,
    dsimp only [subalgebra.coe_mul, linear_map.cod_restrict_apply, linear_map.comp_apply,
      algebra.lmul_left_apply, linear_map.inl_apply, subalgebra.coe_algebra_map],
    rw [←neg_ι_mul_e0] {occs := occurrences.pos [1]},
    rw [←mul_neg, mul_assoc, ←mul_assoc _ (e0 _), neg_mul, e0_mul_e0, neg_neg, one_mul,
      ι_sq_scalar],
    dsimp [Q'],
    rw [zero_mul, neg_zero, add_zero], }
end

@[simp]
lemma to_even_ι (m : M) : (to_even Q (ι Q m) : clifford_algebra (Q' Q)) = e0 Q * ι (Q' Q) (m, 0) :=
begin
  rw [to_even, clifford_algebra.lift_ι_apply, linear_map.cod_restrict_apply],
  refl,
end


notation `↑ₐ` := algebra_map _ (clifford_algebra _)

@[simp, to_additive] lemma prod.swap_mul {α β} [has_mul α] [has_mul β] (x y : α × β) :
  prod.swap (x * y) = prod.swap x * prod.swap y := rfl


variables {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] M →ₗ[R] A)
namespace even.lift

-- THIS IS FALSE!
def S : submodule R (M →ₗ[R] A) :=
{ carrier := {x | ∃ (acc1 : A) (m : M), x = (algebra.lmul_right R acc1).comp (f.flip m)},
  zero_mem' := sorry,
  add_mem' := sorry,
  smul_mem' := sorry }

def f_fold : M →ₗ[R] (A × (S f)) →ₗ[R] (A × (S f)) :=
linear_map.mk₂ R (λ m acc, (acc.2 m, ⟨(algebra.lmul_right R acc.1).comp (f.flip m), _, _, rfl⟩))
  sorry sorry sorry sorry

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
  rintro ⟨a, ⟨_, b, m₃, rfl⟩⟩,
  rw [linear_map.comp_apply],
  ext : 2,
  { change f m₂ m₂ * a = Q m₂ • a,
    rw [algebra.smul_def, hf] },
  { ext m₁,
    change f _ _ * (f _ _ * b) = Q m₂ • (f _ _ * b),
    rw [←smul_mul_assoc, ←mul_assoc, hf₂] }
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

instance : module R (clifford_algebra.even Q) :=
by apply_instance

lemma _root_.commute.mul_self_sub_mul_self_eq {R} [ring R] {a b : R}(h : commute a b) :
  a * a - b * b = (a + b) * (a - b) :=
begin
  rw [add_mul, mul_sub, mul_sub, h.eq],
  abel,
end

lemma _root_.commute.mul_self_sub_mul_self_eq' {R} [ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a - b) * (a + b) :=
begin
  rw [mul_add, sub_mul, sub_mul, h.eq],
  abel,
end

/--
x.fst * f m m = Q m • x.fst
x.snd m * f m y = Q m • x.snd y

x * ⇑(⇑f m) m = ⇑Q m • x
0 * ⇑(⇑f m) m = ⇑Q m • 0
0 * ⇑(⇑f m) x_1 = ⇑Q m • 0
⇑x m * ⇑(⇑f m) x_1 = ⇑Q m • ⇑x x_1

Basics:

f ⟨0,1⟩ (f ⟨x,0⟩ acc) = ι x * acc
f ⟨x,0⟩ (f ⟨0,1⟩ acc) = -ι x * acc
f ⟨x,0⟩ (f ⟨y,0⟩ acc) = ι x * ι y * acc
f ⟨0,1⟩ (f ⟨0,1⟩ acc) = -acc

Combined

f ⟨x,rx⟩ (f ⟨y,ry⟩ acc) = (ιx + rx) * (ιy - ry) * acc

So

f ⟨x,rx⟩ (f ⟨x,rx⟩ acc) = (ιx + rx)^2 * acc
                      = (Qx + 2rxιx + rx^2) * acc
                      = (Qx - rx^2) * acc

f x (f e0 (f e0 (f e0 acc))) = x * x * acc
f x (f e0 acc) = x * acc

try:
  f ⟨x,rx⟩ (a1, a2) = ((ι x + r) * a2, (ι x - r) * a1)

check:
  f ⟨x,rx⟩ (f ⟨x,rx⟩ (a1, a2)) = f ⟨x,rx⟩ ((ι x + r) * a2, (ι x - r) * a1)

--/
def of_even : clifford_algebra.even (Q' Q) →ₐ[R] clifford_algebra Q :=
begin
  let f : (M × R) →ₗ[R] (M × R) →ₗ[R] clifford_algebra Q :=
  linear_map.mk₂ R (λ x y,
    (ι Q x.fst + algebra_map R _ x.snd) * (ι Q y.fst - algebra_map R _ y.snd))
      sorry sorry sorry sorry,
  have hc : ∀ (r : R) (x : clifford_algebra Q), commute (algebra_map _ _ r) x := algebra.commutes,
  have hm : ∀ m : M × R,
    ι Q m.1 * ι Q m.1 - algebra_map R _ m.2 * algebra_map R _ m.2 = algebra_map R _ (Q' Q m),
  { intro m,
    rw [ι_sq_scalar, ←ring_hom.map_mul, ←ring_hom.map_sub,
      sub_eq_add_neg, Q', quadratic_form.prod_to_fun, quadratic_form.neg_apply,
      quadratic_form.sq_to_fun] },
  refine even.lift (Q' Q) f _ _; dsimp only [f, linear_map.mk₂_apply],
  { intro m,
    rw [←(hc _ _).symm.mul_self_sub_mul_self_eq, hm] },
  { intros m₁ m₂ m₃,
    rw [←mul_smul_comm, ←mul_assoc, mul_assoc(_ + _), ←(hc _ _).symm.mul_self_sub_mul_self_eq',
      algebra.smul_def, ←mul_assoc, hm] },
end

lemma of_even_ι (x y : M × R) :
  of_even Q (even.ι _ x y) = (ι Q x.1 + algebra_map R _ x.2) * (ι Q y.1 - algebra_map R _ y.2) :=
even.lift_ι _ _ _ _ _ _

lemma mul_mul_mul_assoc {α} [semigroup α] (a b c d : α) :
  (a * b) * (c * d) = a * (b * c) * d := by rw [mul_assoc, mul_assoc, mul_assoc]

lemma of_even_comp_to_even :
  (to_even Q).comp (of_even Q) = alg_hom.id R _ :=
even.alg_hom_ext _ $ linear_map.ext $ λ m₁, linear_map.ext $ λ m₂, begin
  ext : 1,
  change ↑(to_even Q (of_even Q (even.ι (Q' Q) m₁ m₂))) = ι (Q' Q) m₁ * ι (Q' Q) m₂,
  rw [of_even_ι, alg_hom.map_mul, alg_hom.map_add, alg_hom.map_sub, alg_hom.commutes,
    alg_hom.commutes, subalgebra.coe_mul, subalgebra.coe_add, subalgebra.coe_sub,
    to_even_ι, to_even_ι, subalgebra.coe_algebra_map, subalgebra.coe_algebra_map],
  rw [mul_sub, add_mul, add_mul, ←mul_assoc (algebra_map _ _ _), ←algebra.smul_def,
      mul_assoc _ _ (algebra_map _ _ _), ←algebra.commutes, ←mul_assoc _ (algebra_map _ _ _),
      ←algebra.commutes, ←algebra.smul_def,
      ←neg_ι_mul_e0, neg_mul, mul_mul_mul_assoc, e0_mul_e0, mul_neg,
      mul_one, neg_mul, neg_neg, sub_eq_add_neg, neg_add],
  conv_rhs {
    rw [←prod.fst_add_snd m₁, ←prod.fst_add_snd m₂, linear_map.map_add, linear_map.map_add,
      eq_smul_e0, eq_smul_e0, mul_add, add_mul, add_mul, smul_mul_smul, e0_mul_e0, smul_neg,
      ←algebra.algebra_map_eq_smul_one, ring_hom.map_mul, mul_smul_comm, ←neg_e0_mul_ι, smul_neg,
      ←smul_mul_assoc],
  },
end

def even_equiv : clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q' Q) :=
alg_equiv.of_alg_hom
  (to_even Q)
  (of_even Q)
  (of_even_comp_to_even Q)
  (begin
    -- ext,
    -- dsimp only [of_even, to_even],
    sorry
  end)

end equiv_even

end clifford_algebra
