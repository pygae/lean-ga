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
-- set_option old_structure_cmd true

/--
-/
class semi_geometric_algebra
(R : Type u₀) [field R]
(V : Type u₁) [add_comm_group V] [vector_space R V]
(G : Type u₂) [ring G]
extends algebra R G

class weak_geometric_algebra
(R : Type u₀) [field R]
(V : Type u₁) [add_comm_group V] [vector_space R V]
(G : Type u₂) [ring G]
extends semi_geometric_algebra R V G
:=
(fᵣ : R →+* G := algebra_map R G)
(fᵥ : V →+ G)
-- this is the weaker form of the contraction rule for vectors
(vector_contract' : ∀ v, ∃ r, fᵥ v * fᵥ v = fᵣ r )

class geometric_algebra
(R : Type u₀) [field R]
(V : Type u₁) [add_comm_group V] [vector_space R V]
(G : Type u₂) [ring G]
extends weak_geometric_algebra R V G
:=
(q : quadratic_form R V)
(vector_contract : ∀ v, fᵥ v * fᵥ v = fᵣ (q v) )

end prio

-- #print geometric_algebra

namespace geometric_algebra

variables {R : Type u₀} [field R]
variables {V : Type u₁} [add_comm_group V] [vector_space R V]
variables {G : Type u₂} [ring G]
variables (GA : geometric_algebra R V G)

/-
@[reducible]
def weak_geometric_algebra.vector_contract' : ∀ {R : Type u₀} [_inst_1 : field R] {V : Type u₁} [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V]
{G : Type u₂} [_inst_4 : ring G] [c : weak_geometric_algebra R V G] (v : V),
  ∃ (r : R),
    ⇑(weak_geometric_algebra.fᵥ R) v * ⇑(weak_geometric_algebra.fᵥ R) v = ⇑(weak_geometric_algebra.fᵣ V) r :=
λ (R : Type u₀) [_inst_1 : field R] (V : Type u₁) [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V]
(G : Type u₂) [_inst_4 : ring G] [c : weak_geometric_algebra R V G], [weak_geometric_algebra.vector_contract' c]
-/
#print weak_geometric_algebra.vector_contract'

/-
@[reducible]
def geometric_algebra.vector_contract : ∀ {R : Type u₀} [_inst_1 : field R] {V : Type u₁} [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V]
{G : Type u₂} [_inst_4 : ring G] [c : geometric_algebra R V G] (v : V),
  ⇑(weak_geometric_algebra.fᵥ R) v * ⇑(weak_geometric_algebra.fᵥ R) v =
    ⇑(weak_geometric_algebra.fᵣ V) (⇑(q G) v) :=
λ (R : Type u₀) [_inst_1 : field R] (V : Type u₁) [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V]
(G : Type u₂) [_inst_4 : ring G] [c : geometric_algebra R V G], [geometric_algebra.vector_contract c]
-/
#print geometric_algebra.vector_contract

/-
theorem geometric_algebra.dummy : ∀ {R : Type u₀} [_inst_1 : field R] {V : Type u₁} [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V]
(v : V), ∃ (r : R), r = r ∧ v = v :=
λ {R : Type u₀} [_inst_1 : field R] {V : Type u₁} [_inst_2 : add_comm_group V] [_inst_3 : vector_space R V], sorry
-/
lemma dummy : ∀ v : V, ∃ r : R, r = r ∧ v = v := sorry

#print dummy

-- example : ∀ v : V, ∃ r : R,
--   ⇑(weak_geometric_algebra.fᵥ R) v * ⇑(weak_geometric_algebra.fᵥ R) v = ⇑(weak_geometric_algebra.fᵣ V) r

end geometric_algebra

#lint