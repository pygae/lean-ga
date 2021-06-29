/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import algebra.quaternion
import for_mathlib.data.quaternion

/-!
# The quaternions are isomorphic to a clifford algebra
-/

namespace clifford_algebra_quaternion

open_locale quaternion
open quaternion_algebra

variables {R : Type*} [comm_ring R] (c₁ c₂ : R)

/-- The quadratic form. -/
def Q : quadratic_form R (R × R) :=
c₁ • quadratic_form.lin_mul_lin (linear_map.fst _ _ _) (linear_map.fst _ _ _) +
c₂ • quadratic_form.lin_mul_lin (linear_map.snd _ _ _) (linear_map.snd _ _ _)

variables {c₁ c₂}

@[simp]
lemma Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) := rfl

/-- Intermediate result of `clifford_algebra_complex.equiv_quaternion`: clifford algebras over
`clifford_algebra_quaternion.Q` above can be converted to `ℍ[R,c₁,c₂`. -/
def to_quaternion : clifford_algebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,c₂] :=
clifford_algebra.lift (Q c₁ c₂) ⟨
  { to_fun := λ v, (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]),
    map_add' := λ v₁ v₂, by simp,
    map_smul' := λ r v, by ext; simp},
  λ v, begin
    dsimp,
    ext,
    all_goals {dsimp, ring},
  end⟩

@[simp]
lemma to_quaternion_ι (v : R × R) :
  to_quaternion (clifford_algebra.ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]) :=
clifford_algebra.lift_ι_apply _ _ v

def of_quaternion : ℍ[R,c₁,c₂] →ₐ[R] clifford_algebra (Q c₁ c₂) :=
quaternion_structure.lift_hom {
  i := clifford_algebra.ι (Q c₁ c₂) (1, 0),
  j := clifford_algebra.ι (Q c₁ c₂) (0, 1),
  k := clifford_algebra.ι (Q c₁ c₂) (1, 0) * clifford_algebra.ι (Q c₁ c₂) (0, 1),
  i_mul_i := begin
    rw [clifford_algebra.ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  j_mul_j := begin
    rw [clifford_algebra.ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  i_mul_j := sorry,
  j_mul_i := sorry }

/-- The clifford algebra over `clifford_algebra_quaternion.Q` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps]
def equiv_quaternion : clifford_algebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂] :=
alg_equiv.of_alg_hom to_quaternion of_quaternion
  (begin
    ext1,
    dsimp,
    sorry,
  end)
  (begin
    ext1,
    dsimp,
    sorry,
  end)

end clifford_algebra_quaternion
