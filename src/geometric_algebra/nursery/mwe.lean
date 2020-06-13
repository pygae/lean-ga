/-
This file will be changed drastically all the time, it's only for reproduce the problem as 
a [minimal working example](https://leanprover-community.github.io/mwe.html) to ask on 
[Zulip](http://leanprover.zulipchat.com/)
-/

import ring_theory.algebra

class geometric_algebra (G : Type*)
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀] [char_zero G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit.
[ring G]
[algebra G₀ G]
:=
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k)

namespace geometric_algebra

section

variables (G : Type*)
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀] [char_zero G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit.
[ring G]
[algebra G₀ G]
[GA : geometric_algebra G G₀ G₁]

def square (a : G) := a * a

def sym_prod (a b : G) := a * b + b * a

local infix `*₊`:75 := sym_prod

local postfix `²`:80 := square

#check f₁

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar_failed :
∀ (a b : G₁), ∃ k : G₀, 
  f₁ a *₊ f₁ b = algebra_map _ _ k := by sorry

-- type mismatch at application
--   f₁ a
-- term
--   a
-- has type
--   G₁ : Type u_3
-- but is expected to have type
--   Type ? : Type (?+1)
-- Additional information:
-- minimal.lean:43:2: context: switched to simple application elaboration procedure because failed to use expected type to elaborate it, error message
--   type mismatch, term
--     f₁ ?m_2
--   has type
--     ?m_1 →+ ?m_2 : Type (max ? ?)
--   but is expected to have type
--     Type ? : Type (?+1)

lemma vec_sym_prod_scalar_still_failed :
∀ (a b : G₁), ∃ k : G₀, 
  (f₁ G₀ a) *₊ (f₁ G₀ b) = algebra_map _ _ k := by sorry
-- failed to synthesize type class instance for
-- G₀ : Type u_2,
-- _inst_1 : field G₀,
-- _inst_2 : char_zero G₀,
-- G₁ : Type u_3,
-- _inst_3 : add_comm_group G₁,
-- _inst_4 : vector_space G₀ G₁,
-- a b : G₁,
-- k : G₀
-- ⊢ ring (Type ?)

end

end geometric_algebra