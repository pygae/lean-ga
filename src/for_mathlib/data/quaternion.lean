/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.quaternion
import tactic.ring

/-! For `algebra/quaternion.lean`. -/

open_locale quaternion
namespace quaternion_algebra

variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A] (c₁ c₂ : R)

@[simp]
lemma smul_mk (r : R) (re im_i im_j im_k : R) :
  r • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂]) = ⟨r • re, r • im_i, r • im_j, r • im_k⟩ := rfl


lemma algebra_map_eq (r : R) : algebra_map R ℍ[R,c₁,c₂] r = ⟨r, 0, 0, 0⟩ := rfl

variables (A)

/-- A quaternions structure contains the information sufficient to show that a subalgebra of `A`
is compatible with `ℍ[R,c₁,c₂]`. -/
structure quaternion_structure :=
(i : A)
(i_mul_i : i * i = c₁ • 1)
(j : A)
(j_mul_j : j * j = c₂ • 1)
(k : A)
(i_mul_j : i * j = k)
(j_mul_i : j * i = -k)

variables {A}

namespace quaternion_structure

variables {c₁ c₂}

@[ext]
protected def ext {q₁ q₂ : quaternion_structure A c₁ c₂} (hi : q₁.i = q₂.i) (hj : q₁.j = q₂.j) :
  q₁ = q₂ :=
begin
  cases q₁,
  cases q₂,
  congr',
  rw [←q₁_i_mul_j, ←q₂_i_mul_j],
  congr'
end

variables (q : quaternion_structure A c₁ c₂)
include q

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[simp] lemma i_mul_k : q.i * q.k = c₁ • q.j :=
by rw [←i_mul_j, ←mul_assoc, i_mul_i, smul_mul_assoc, one_mul]

@[simp] lemma k_mul_i : q.k * q.i = -c₁ • q.j :=
by rw [←i_mul_j, mul_assoc, j_mul_i, mul_neg_eq_neg_mul_symm, i_mul_k, neg_smul]

@[simp] lemma k_mul_j : q.k * q.j = c₂ • q.i :=
by rw [←i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]

@[simp] lemma j_mul_k : q.j * q.k = -c₂ • q.i :=
by rw [←i_mul_j, ←mul_assoc, j_mul_i, neg_mul_eq_neg_mul_symm, k_mul_j, neg_smul]

@[simp] lemma k_mul_k : q.k * q.k = -((c₁ * c₂) • 1) :=
by rw [←i_mul_j, mul_assoc, ←mul_assoc q.j _ _, j_mul_i, ←i_mul_j,
  ←mul_assoc, mul_neg_eq_neg_mul_symm, ←mul_assoc, i_mul_i, smul_mul_assoc, one_mul, neg_mul_eq_neg_mul_symm,
  smul_mul_assoc, j_mul_j, smul_smul]

def lift (x : ℍ[R,c₁,c₂]) : A :=
algebra_map R _ x.re + x.im_i • q.i + x.im_j • q.j + x.im_k • q.k

#check tactic.interactive.abel

lemma lift_zero : q.lift (0 : ℍ[R,c₁,c₂]) = 0 := by simp [lift]
lemma lift_one : q.lift (1 : ℍ[R,c₁,c₂]) = 1 := by simp [lift]
lemma lift_add (x y : ℍ[R,c₁,c₂]) : q.lift (x + y) = q.lift x + q.lift y :=
by { simp [lift, add_smul], abel }
lemma lift_mul (x y : ℍ[R,c₁,c₂]) : q.lift (x * y) = q.lift x * q.lift y :=
begin
  simp only [lift, algebra.algebra_map_eq_smul_one],
  simp only [add_mul],
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    ←algebra.smul_def, smul_add, smul_smul],
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k],
  simp only [smul_smul, smul_neg, sub_eq_add_neg, add_smul, ←add_assoc, mul_neg_eq_neg_mul_symm, neg_smul],
  simp only [mul_right_comm _ _ (c₁ * c₂), mul_comm _ (c₁ * c₂)],
  simp only [mul_comm _ c₁, mul_right_comm _ _ c₁],
  simp only [mul_comm _ c₂, mul_right_comm _ _ c₂],
  simp only [←mul_comm c₁ c₂, ←mul_assoc],
  simp [sub_eq_add_neg, add_smul, ←add_assoc],
  abel
end

lemma lift_smul (r : R) (x : ℍ[R,c₁,c₂]) : q.lift (r • x) = r • q.lift x :=
by simp [lift, mul_smul, ←algebra.smul_def]

/-- A `quaternion_structure` implies an `alg_hom` from the quaternions. -/
@[simps]
def lift_hom : ℍ[R,c₁,c₂] →ₐ[R] A :=
alg_hom.mk'
  { to_fun := q.lift,
    map_zero' := q.lift_zero,
    map_one' := q.lift_one,
    map_add' := q.lift_add,
    map_mul' := q.lift_mul }
  q.lift_smul

omit q

@[simps]
def of_hom (F : ℍ[R,c₁,c₂] →ₐ[R] A) : quaternion_structure A c₁ c₂ :=
{ i := F ⟨0, 1, 0, 0⟩,
  i_mul_i := begin
    rw [←F.map_mul, mk_mul_mk, ←algebra.algebra_map_eq_smul_one, ←F.commutes],
    simp,
    refl,
  end,
  j := F ⟨0, 0, 1, 0⟩,
  j_mul_j := begin
    rw [←F.map_mul, mk_mul_mk, ←algebra.algebra_map_eq_smul_one, ←F.commutes],
    simp,
    refl,
  end,
  k := F ⟨0, 0, 0, 1⟩,
  i_mul_j := begin
    rw [←F.map_mul, mk_mul_mk],
    simp,
  end,
  j_mul_i := begin
    rw [←F.map_mul, mk_mul_mk, eq_neg_iff_eq_neg, ←F.map_neg],
    simp,
  end }

end quaternion_structure

def lift :
  quaternion_structure A c₁ c₂ ≃ (ℍ[R,c₁,c₂] →ₐ[R] A) :=
{ to_fun := quaternion_structure.lift_hom,
  inv_fun := quaternion_structure.of_hom,
  left_inv := λ q, begin
    ext;
    simp [quaternion_structure.lift],
  end,
  right_inv := λ F, begin
    ext,
    dsimp [quaternion_structure.lift],
    rw ←F.commutes,
    simp only [←F.commutes, ←F.map_smul, ←F.map_add, mk_add_mk, smul_mk, smul_zero, algebra_map_eq],
    congr,
    simp,
  end }

end quaternion_algebra
