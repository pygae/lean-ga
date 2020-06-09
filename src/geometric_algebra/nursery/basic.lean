/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

The following code is inspired by 
[`feat(data/quaternion): define quaternions and prove some basic properties #2339`](https://github.com/leanprover-community/mathlib/pull/2339/)
and https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/basic.lean
-/

import tactic.ring_exp ring_theory.algebra algebra.opposites algebra.commute data.equiv.ring
import linear_algebra.quadratic_form
import data.real.basic
import data.complex.basic
import analysis.normed_space.real_inner_product

/-!
> TODO: Sync the docstring with actual code

# Geometric Algebra

In this file we define geometric algebra `𝒢[R]` over a commutative field `F`, and define some
algebraic structures on `𝒢[F]`. Type 𝒢 using `\McG`.

## Main definitions

* [geometric algebra](https://en.wikipedia.org/wiki/Geometric_algebra)
  * `quadratic_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/quadratic_form.lean
  * `field`: https://github.com/leanprover-community/mathlib/blob/master/src/algebra/field.lean
  * `bilinear_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/bilinear_form.lean

## Notation

* `𝒢₃[F]` : the space of geometric algebra 𝒢(3)

## Implementation notes

We define geometric_algebra over any field `F`, not just `ℝ` or `ℂ` to be able to deal with.
In particular(hopefully), all definitions in this file are computable.

## Tags

geometric_algebra
-/

/-
  The following definition follows a not-so-general definition in
  Axiomatic development in Geometric Algebra for Physicists(GA4P).

  It is considered to be limited, which can be observed from
  the following implications of the definition:

  - it can't accept a vanilla vector algebra as a GA
  - it can't accept ℂ as a GA

  The definition is still of interest because from it we can
  reproduce many results in GA4P.
-/

class geometric_algebra (G : Type*) (K : Type*) (V : Type*)
[field K] [has_coe K G]
[add_comm_group V] [vector_space K V] [has_coe V G]
[ring G] [algebra K G]
 :=
(vec_sq_scalar : ∀ v : V, ∃ k : K, (v * v : G) = (k : G))

namespace geometric_algebra

section

variables {G : Type*} {K : Type*} {V : Type*}
[field K] [has_coe K G]
[add_comm_group V] [vector_space K V] [has_coe V G]
[ring G] [algebra K G]
[GA : geometric_algebra G K V]

variables (A B C : G)

-- prove properties and identities for GA

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def square {X : Type*} [has_coe X G] (A : X) : G := A * A

def sym_prod {X : Type*} [has_coe X G] (A B : X) : G := A * B + B * A

local infix `*₊`:75 := sym_prod

local postfix `²`:80 := square

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar [geometric_algebra G K V] : ∀ (a b : V), ∃ k : K, a *₊ b = (k : G) :=
assume a b,
have h1 : (a + b)² = (a² + b² + a *₊ b : G), from begin
  repeat {rw square},
  sorry
  -- G : Type u_1,
  -- K : Type u_2,
  -- V : Type u_3,
  -- _inst_1 : field K,
  -- _inst_2 : has_coe K G,
  -- _inst_3 : add_comm_group V,
  -- _inst_4 : vector_space K V,
  -- _inst_5 : has_coe V G,
  -- _inst_6 : ring G,
  -- _inst_7 : algebra K G,
  -- _inst_8 : geometric_algebra G K V,
  -- a b : V
  -- ⊢ ↑(a + b) * ↑(a + b) = ↑a * ↑a + ↑b * ↑b + a*₊b
  -- repeat {unfold coe, unfold lift_t, unfold has_lift_t.lift, unfold coe_t, unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe},
end,
have h2 : a *₊ b = ((a + b)² - a² - b² : G), from by sorry,
have vec_sq_scalar :
          ∀ v : V, ∃ k : K, (v² : G) = (k : G), from
begin
  intro v,
  apply geometric_algebra.vec_sq_scalar (v),
  repeat {assumption},
end,
exists.elim (vec_sq_scalar (a + b))
(
  assume kab,
  exists.elim (vec_sq_scalar a)
  (
    assume ka,
    exists.elim (vec_sq_scalar b)
    (
      assume kb,
      begin
        intros hb ha hab,
        rw h2,
        use kab - ka - kb,
        rw [hb, ha, hab],
        -- 1 goal
        -- G : Type u_1,
        -- K : Type u_2,
        -- V : Type u_3,
        -- _inst_1 : field K,
        -- _inst_2 : has_coe K G,
        -- _inst_3 : add_comm_group V,
        -- _inst_4 : vector_space K V,
        -- _inst_5 : has_coe V G,
        -- _inst_6 : ring G,
        -- _inst_7 : algebra K G,
        -- _inst_8 : geometric_algebra G K V,
        -- a b : V,
        -- h1 : (a + b)² = a² + b² + a*₊b,
        -- h2 : a*₊b = (a + b)² - a² - b²,
        -- vec_sq_scalar : ∀ (v : V), ∃ (k : K), v² = ↑k,
        -- kab ka kb : K,
        -- hb : b² = ↑kb,
        -- ha : a² = ↑ka,
        -- hab : (a + b)² = ↑kab
        -- ⊢ ↑kab - ↑ka - ↑kb = ↑(kab - ka - kb)
        sorry
      end
    )
  )
)

end

end geometric_algebra

-- the trivial case: prove ℝ is a GA

instance : has_coe ℝ ℝ := { coe := λ x, x }

noncomputable instance : geometric_algebra ℝ ℝ ℝ := {
    vec_sq_scalar := begin
        intro v,
        use v * v,
        refl
    end
}

-- class has_geometric_product (G : Type*) :=
-- (add {α : Type*} {β : Type*} : α → β → G)
-- (mul {α : Type*} {β : Type*} : α → β → G)
-- (assoc : ∀ A B C : G, (A * B) * C = A * (B * C))
-- (left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C))
-- (right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C))
-- (vec_sq_scalar {K : Type*} {V : Type*} [field K] [add_comm_group V] [vector_space K V]:
--     ∀ v : V, ∃ k : K, v * v = k)

inductive vec_gp_res
(K : Type*) (V : Type*) [field K] [add_comm_group V] [vector_space K V]
| scalar : K → vec_gp_res
| bivec  : V → V → vec_gp_res

class has_vec_gp (K : Type*) (V : Type*) [field K] [add_comm_group V] [vector_space K V] :=
(mul : V → V → vec_gp_res K V)
(assoc : ∀ A B C : V, mul (mul A B) C = (mul A (mul B C))
-- type mismatch at application
--   mul (mul A B)
-- term
--   mul A B
-- has type
--   vec_gp_res K V : Type (max ? ?)
-- but is expected to have type
--   V : Type ?