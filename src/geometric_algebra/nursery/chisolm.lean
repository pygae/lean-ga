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
extends G₁ →+ G
:=
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, (v * v : G) ∈ G₀)

namespace geometric_algebra

section

variables (G : Type u)
(G₀ : set G) [field G₀] [char_zero G₀] [has_zero G₀] [has_one G₀]
(G₁ : set G) [add_comm_group G₁] [vector_space G₀ G₁]
[ring G]
[algebra G₀ G]
[geometric_algebra G G₀ G₁]

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def square (a : G) := a * a

def sym_prod (a b : G) := a * b + b * a

local postfix `²`:80 := λ a : G, a * a

local infix `*₊`:75 := λ a b : G, a * b + b * a

lemma vec_sym_prod_scalar [geometric_algebra G G₀ G₁] :
∀ (a b : G₁), a *₊ b ∈ G₀ :=
assume a b,
have h1 : (a + b)² = (a² + b² + a *₊ b : G), from begin
    simp only [],
    rw distrib.left_distrib (↑a + ↑b) ↑a ↑b,
    rw distrib.right_distrib _ _ ↑a,
    rw distrib.right_distrib _ _ ↑b,
    cc,
end,
have h2 : a *₊ b = ((a + b)² - a² - b² : G), from
begin
    apply_fun (λ x, - (a² + b²) + x) at h1,
    simp only [],
    noncomm_ring,
end,
have vec_sq_scalar : ∀ v : G₁, v² ∈ G₀, from
begin
  intro v,
  apply geometric_algebra.vec_sq_scalar (v),
  repeat {assumption},
end,
have hl : has_lift_t ↥G₁ ↥G₁, from by sorry,
have h3 : (↑a : G)² ∈ G₀, from by apply vec_sq_scalar,
have h4 : (↑b : G)² ∈ G₀, from by apply vec_sq_scalar,
have h5 : (a + b : G) ∈ G₁ , from
begin
    -- rw add_monoid_hom.map_add',
    -- rewrite tactic failed, did not find instance of the pattern in the target expression
    --   ?m_5.to_fun (?m_6 + ?m_7)
    -- 1 goal
    -- G : Type u,
    -- G₀ : set G,
    -- _inst_1 : field ↥G₀,
    -- _inst_2 : char_zero ↥G₀,
    -- _inst_3 : has_zero ↥G₀,
    -- _inst_4 : has_one ↥G₀,
    -- G₁ : set G,
    -- _inst_5 : add_comm_group ↥G₁,
    -- _inst_6 : vector_space ↥G₀ ↥G₁,
    -- _inst_7 : ring G,
    -- _inst_8 : algebra ↥G₀ G,
    -- _inst_9 _inst_10 : geometric_algebra G G₀ G₁,
    -- a b : ↥G₁,
    -- h1 :
    --   (λ (a : G), a * a) (↑a + ↑b) =
    --     (λ (a : G), a * a) ↑a + (λ (a : G), a * a) ↑b + (λ (a b : G), a * b + b * a) ↑a ↑b,
    -- h2 :
    --   (λ (a b : G), a * b + b * a) ↑a ↑b =
    --     (λ (a : G), a * a) (↑a + ↑b) - (λ (a : G), a * a) ↑a - (λ (a : G), a * a) ↑b,
    -- vec_sq_scalar : ∀ (v : ↥G₁), (λ (a : G), a * a) ↑v ∈ G₀,
    -- hl : has_lift_t ↥G₁ ↥G₁,
    -- h3 : (λ (a : G), a * a) ↑a ∈ G₀,
    -- h4 : (λ (a : G), a * a) ↑b ∈ G₀
    -- ⊢ ↑a + ↑b ∈ G₁
    sorry
end,
have h6 : (↑a + ↑b)² ∈ G₀, from
begin
    simp only [],
    simp only [] at vec_sq_scalar,
    sorry
end,
begin
    simp only [] at h2,
    simp only [],
    rw h2,
    sorry
    --apply vec_sq_scalar (↑a),
end

end

end geometric_algebra

