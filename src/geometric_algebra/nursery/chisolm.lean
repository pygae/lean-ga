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
(scalar_hom : G₀ →+* G)
(vec_hom : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, vec_hom(v) * vec_hom(v) = scalar_hom(k) )

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

local postfix `²`:80 := λ a : G, a * a

local infix `*₊`:75 := λ a b : G, a * b + b * a

-- def square {X : Type*} [has_coe X G] (A : X) : G := A * A

-- def sym_prod {X : Type*} [has_coe X G] (A B : X) : G := A * B + B * A

-- local infix `*₊`:75 := sym_prod

-- local postfix `²`:80 := square

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar :
∀ (a b : G₁), ∃ k : G₀, a *₊ b = (k : G) :=
assume a b,
have h1 : (a + b)² = (a² + b² + a *₊ b : G), from begin
  repeat {rw square},
  sorry
  -- G : Type u_1,
  -- G₀ : Type u_2,
  -- G₁ : Type u_3,
  -- _inst_1 : field G₀,
  -- _inst_2 : has_coe G₀ G,
  -- _inst_3 : add_comm_group G₁,
  -- _inst_4 : vector_space G₀ G₁,
  -- _inst_5 : has_coe G₁ G,
  -- _inst_6 : ring G,
  -- _inst_7 : algebra G₀ G,
  -- _inst_8 : geometric_algebra G G₀ G₁,
  -- a b : G₁
  -- ⊢ ↑(a + b) * ↑(a + b) = ↑a * ↑a + ↑b * ↑b + a*₊b
  -- repeat {unfold coe, unfold lift_t, unfold has_lift_t.lift, unfold coe_t, unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe},
end,
have h2 : a *₊ b = ((a + b)² - a² - b² : G), from by sorry,
have vec_sq_scalar :
          ∀ v : G₁, ∃ k : G₀, (v² : G) = (k : G), from
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
        simp only [],
        simp only [] at h1,
        simp only [] at h2,
        simp only [] at ha,
        simp only [] at hb,
        simp only [] at hab,
        rw [hb, ha],
        
        -- 1 goal
        -- G : Type u_1,
        -- G₀ : Type u_2,
        -- G₁ : Type u_3,
        -- _inst_1 : field G₀,
        -- _inst_2 : has_coe G₀ G,
        -- _inst_3 : add_comm_group G₁,
        -- _inst_4 : vector_space G₀ G₁,
        -- _inst_5 : has_coe G₁ G,
        -- _inst_6 : ring G,
        -- _inst_7 : algebra G₀ G,
        -- _inst_8 : geometric_algebra G G₀ G₁,
        -- a b : G₁,
        -- h1 : (a + b)² = a² + b² + a*₊b,
        -- h2 : a*₊b = (a + b)² - a² - b²,
        -- vec_sq_scalar : ∀ (v : G₁), ∃ (k : G₀), v² = ↑k,
        -- kab ka kb : G₀,
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
