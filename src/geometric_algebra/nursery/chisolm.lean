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

import tactic.apply_fun
import tactic

universes u u₀ u₁

/- Needed for zero_pairwise_ortho_vector -/
-- lemma pairwise_of_repeat {X : Type*} {x : X} {n : ℕ} {r : X → X → Prop} (hr : r x x) :
--   list.pairwise r (list.repeat x n) :=
-- begin
--   induction n with d hd,
--   { exact list.pairwise.nil},
--   { apply list.pairwise.cons _ hd,
--     intros a ha,
--     convert hr,
--     exact list.eq_of_mem_repeat ha,
--   }
-- end

class geometric_algebra
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀]
-- Axiom 3: G contains a subset G1 closed under addition, 
-- and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
(G : Type*) [ring G]
[algebra G₀ G]
:=
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
-- TODO clearly this should be nameed following "contraction rule", I'm thinking maybe `contract`?
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k )

namespace geometric_algebra

section basic

parameters
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

def fᵥ : G₁ →+ G := f₁ G₀

def fₛ : G₀ →+* G := algebra_map G₀ G

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def prod_vec (a b : G₁) : G := fᵥ a * fᵥ b

local infix `*ᵥ`:75 := prod_vec

-- def square (a : G) := a * a

def square_vec (a : G₁) := a *ᵥ a

-- local postfix `²`:80 := square

local postfix `²ᵥ`:80 := square_vec

def sym_prod_vec (a b : G₁) := a *ᵥ b + b *ᵥ a

local infix `*₊ᵥ`:75 := sym_prod_vec

def is_orthogonal (a : G₁) (b : G₁) : Prop := sym_prod_vec a b = 0

theorem zero_is_orthogonal (a : G₁) : is_orthogonal 0 a := begin
  unfold is_orthogonal,
  unfold sym_prod_vec,
  unfold prod_vec,
  simp
end

/- a list of r orthogonal vectors, which may be non-unique -/
def pairwise_ortho_vector (r : ℕ) := {l : vector G₁ r // l.val.pairwise is_orthogonal}

/- need this for later, can't seem to get the type inference to work if I inline it-/
-- def zero_pairwise_ortho_vector (r : ℕ) : pairwise_ortho_vector r := ⟨
--   vector.repeat (0 : G₁) r, begin
--   unfold vector.repeat subtype.val,
--   apply pairwise_of_repeat,
--   apply zero_is_orthogonal,
-- end⟩

def is_rblade (r : ℕ) (b : G) : Prop :=
  -- a product of orthogonal vectors an a scalar
  (∃ (k: G₀) (v : pairwise_ortho_vector r),
   b = fₛ k * list.prod (v.val.val.map fᵥ))

-- r-blades
def Bᵣ (r : ℕ) := set_of (is_rblade r)

-- r-vectors
def Gᵣ (r : ℕ) := add_subgroup.closure (Bᵣ r)

example (r : ℕ) : add_comm_group (Gᵣ r) := by apply_instance

-- multi-vectors
def Mᵣ (r : ℕ) := add_subgroup.closure (⋃ (r : ℕ), (Gᵣ r).carrier)

example (r : ℕ) : add_comm_group (Mᵣ r) := by apply_instance
  
def grade_select {r : ℕ} (m : Mᵣ r) (g : ℕ) : Gᵣ g := sorry

@[simp]
def is_scalar : G → Prop := is_rblade 0

end basic

end geometric_algebra
