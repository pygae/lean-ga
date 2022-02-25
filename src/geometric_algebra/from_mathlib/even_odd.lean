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

/-- The even submodule is also a subalgebra. -/
def even : subalgebra R (clifford_algebra Q) :=
(even_odd Q 0).to_subalgebra
  set_like.graded_monoid.one_mem
  (λ x y hx hy, add_zero (0 : zmod 2) ▸ set_like.graded_monoid.mul_mem hx hy)

lemma even_to_submodule : (even Q).to_submodule = even_odd Q 0 :=
rfl

-- def even.lift {A} [semiring A] [algebra R A] (f : M →ₗ[R] M →ₗ[R] A)
--   (cond : ∀ v w, f v w * f v w = sorry) : even Q →ₐ[R] A :=
-- begin

-- end

namespace equiv_even

@[reducible]
def Q' : quadratic_form R (M × R) := (Q.prod $ -@quadratic_form.sq R _)

/-- The unit vector in the new dimension -/
def e0 : clifford_algebra (Q' Q) := ι (Q' Q) (0, 1)

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
/--

x*y -> (e0 * x) * (e0 * y) = -(x * e0) * (e0 * y) = x * y

e0*e0 -> -1
e0 -> NA
e0*x -> x
x*y -> x * y
(e0 + x)*y = y + x*y

-/
def of_even : clifford_algebra.even (Q' Q) →ₐ[R] clifford_algebra Q :=
begin
  refine alg_hom.comp _ (subalgebra.val _),
  refine clifford_algebra.lift _ ⟨_, λ m, _⟩,
  -- have := (ι Q).comp (linear_map.fst _ _ _),
  exact (ι Q).comp (linear_map.fst _ _ _) + (algebra.linear_map _ _).comp (linear_map.snd _ _ _),
  dsimp,
  rw [add_mul, mul_add, mul_add, ι_sq_scalar, ←ring_hom.map_mul],
end

#check 1

@[simp, to_additive] lemma prod.swap_mul {α β} [has_mul α] [has_mul β] (x y : α × β) :
  prod.swap (x * y) = prod.swap x * prod.swap y := rfl
#check prod.swap_prod_mk
/--

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
def of_even' : clifford_algebra.even (Q' Q) →ₗ[R] clifford_algebra Q :=
begin
  let f : (M × R) →ₗ[R] (clifford_algebra Q × clifford_algebra Q)
                  →ₗ[R] (clifford_algebra Q × clifford_algebra Q) :=
    linear_map.mk₂ R (λ x acc,
      ((ι Q x.fst + algebra_map R _ x.snd), (ι Q x.fst - algebra_map R _ x.snd)) * acc.swap)
      sorry sorry sorry sorry,
  have := foldr (Q' Q) f _,
  swap,
  { intro m,
    apply linear_map.ext,
    rintro a,
    dsimp only [f, linear_map.comp_apply, linear_map.mk₂_apply, prod.swap_mul, prod.swap_prod_mk,
      linear_map.smul_apply, linear_map.id_apply, Q', quadratic_form.prod_to_fun,
      quadratic_form.sq_to_fun, quadratic_form.neg_apply],
    simp only [←mul_assoc, prod.swap_swap, algebra.smul_def],
    congr' 1,
    simp only [mul_add, add_mul, sub_mul, mul_sub, prod.mk_mul_mk],
    change (_, _) = (_, _),
    simp only [←ring_hom.map_mul, ←algebra.commutes, ι_sq_scalar],
    have : _ = _ := _,
    refine congr_arg2 prod.mk this this,
    rw [add_comm (_ * ι Q _), add_sub_add_right_eq_sub,
      ←ring_hom.map_mul, ←ring_hom.map_sub, sub_eq_add_neg] },
  refine (linear_map.fst _ _ _).comp ((this (1, 1)).dom_restrict _),
end


def even_equiv : clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q.prod $ -@quadratic_form.sq R _) :=
alg_equiv.of_alg_hom
  _
  sorry --(clifford_algebra.lift _ ⟨_, _⟩)
  _
  _

end equiv_even

end clifford_algebra
