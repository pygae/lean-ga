/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song
-/

import tactic.ring_exp ring_theory.algebra algebra.opposites algebra.commute data.equiv.ring
import linear_algebra.quadratic_form
import data.real.basic
import data.complex.basic
import analysis.normed_space.real_inner_product
import geometry.manifold.real_instances

universes u u₀ u₁

class geometric_algebra (G : Type u)
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : set G) [field G₀] [char_zero G₀] [has_zero G₀] [has_one G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : set G) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
[ring G]
:=
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, (v * v : G) ∈ G₀)

namespace geometric_algebra

section

variables (G : Type*)
(G₀ : set G) [field G₀] [char_zero G₀] [has_zero G₀] [has_one G₀]
(G₁ : set G) [add_comm_group G₁] [vector_space G₀ G₁]
[ring G]
[geometric_algebra G G₀ G₁]

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def square {X : Type*} [X : set G] (A : X) : G := A * A

def sym_prod {X : Type*} [X : set G] (A B : X) : G := A * B + B * A

local infix `*₊`:75 := sym_prod

local postfix `²`:80 := square

lemma vec_sym_prod_scalar [geometric_algebra G G₀ G₁] :
∀ (a b : G₁), (a * b + b * a : G) ∈ G₀ :=
by sorry

end

end geometric_algebra

