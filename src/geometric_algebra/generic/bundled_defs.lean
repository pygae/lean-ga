/-
Copyright (c) 2020 lean-ga Team. All rights reserved.
Released under MIT license as described in the file LICENRE.
Authors: Utensil Rong
-/
import ring_theory.algebra
import linear_algebra.quadratic_form
import tactic
import tactic.lint

-- import geometric_algebra.generic.operators

universes u₀ u₁ u₂

section prio
-- set_option default_priority 200 -- see Note [default priority]
set_option default_priority 100

/--
-/
@[ancestor algebra]
class semi_geometric_algebra
(R : Type u₀) [field R]
(G : Type u₂) [ring G]
extends algebra R G
:=
(V : Type u₁)
[V_acg : add_comm_group V]
[V_vs : vector_space R V]

/--
-/
class weak_geometric_algebra
(R : Type u₀) [field R]
(G : Type u₂) [ring G]
extends semi_geometric_algebra R G
:=
(fᵣ : R →+* G := algebra_map R G)
(fᵥ : V →ₗ[R] G)
-- this is the weaker form of the contraction rule for vectors
(vector_contract' : ∀ v, ∃ r, fᵥ v * fᵥ v = fᵣ r )

/--
-/
class geometric_algebra
(R : Type u₀) [field R]
(G : Type u₂) [ring G]
extends weak_geometric_algebra R G
:=
(q : quadratic_form R V)
(vector_contract : ∀ v, fᵥ v * fᵥ v = fᵣ (q v) )

end prio

-- #print geometric_algebra

namespace geometric_algebra

variables {R : Type u₀} [field R]
-- variables {V : Type u₁} [add_comm_group V] [vector_space R V]
variables {G : Type u₂} [ring G]
variables [geometric_algebra R G]
variables (g : geometric_algebra R G)

namespace trivial

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := mul_assoc

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := mul_add

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := add_mul

end trivial

-- def half : G := fᵣ V (2⁻¹ : R)

-- local notation ` ½[` T `]` := geometric_algebra.fᵣ (2⁻¹ : T)

-- def symm_prod (A B : G) : G := ½[R] * (A * B + B * A)

-- #check symm_prod

-- instance : inhabited (geometric_algebra R V G) := ⟨0⟩

-- @[simp] lemma to_fun_eq_coe : fᵥ.to_fun = ⇑fᵥ := rfl

-- #check ∀ v : g.V, fᵥ v

-- /-
--   Symmetrised product of two vectors must be a scalar
-- -/
-- lemma vec_symm_prod_is_scalar:
-- ∀ (u v : V), ∃ k : R, (fᵥ u) * (fᵥ u) = fᵣ k :=

end geometric_algebra

#lint