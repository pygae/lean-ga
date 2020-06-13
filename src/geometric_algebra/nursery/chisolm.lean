/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

This file is based on https://arxiv.org/abs/1205.5935
-/
import algebra.group.hom
import ring_theory.algebra
import data.real.basic
import data.complex.basic

universes u u₀ u₁

class geometric_algebra (G : Type*)
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
[ring G]
-- TODO: find better ways to map G₀ and G₁ to G
-- [has_coe G₀ G] [has_coe G₁ G]
-- [G₀ →+* G]
-- [algebra G₀ G]
:=
(f₀ : G₀ →+* G)
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = f₀ k )

namespace geometric_algebra

section

variables  (G : Type*)
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀] [char_zero G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
[ring G]
-- TODO: find better ways to map G₀ and G₁ to G
-- [has_coe G₀ G] [has_coe G₁ G]
-- [G₀ →+* G]
-- [algebra G₀ G]
[GA : geometric_algebra G G₀ G₁]

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def square (a : G) := a * a

def sym_prod (a b : G) := a * b + b * a

-- local postfix `²`:80 := λ a : G, a * a

-- local infix `*₊`:75 := λ a b : G, a * b + b * a

-- def square {X : Type*} [has_coe X G] (A : X) : G := A * A

-- def sym_prod {X : Type*} [has_coe X G] (A B : X) : G := A * B + B * A

local infix `*₊`:75 := sym_prod

local postfix `²`:80 := square

#check f₀

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar :
∀ (a b : G₁), ∃ k : G₀, 
  f₁ a *₊ f₁ b = f₀ k := by sorry


end

end geometric_algebra
