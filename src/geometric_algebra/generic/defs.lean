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

universes ur uv ug

variables {R : Type ur} [field R]
variables {V : Type uv} [add_comm_group V] [vector_space R V]
variables {G : Type ug} [ring G]

section prio
-- set_option default_priority 200 -- see Note [default priority]
set_option default_priority 100
set_option old_structure_cmd true

/--
-/
@[ancestor algebra]
class semi_geometric_algebra
(R : Type ur) [field R]
(V : Type uv) [add_comm_group V] [vector_space R V]
(G : Type ug) [ring G]
extends algebra R G

class weak_geometric_algebra
(R : Type ur) [field R]
(V : Type uv) [add_comm_group V] [vector_space R V]
(G : Type ug) [ring G]
extends semi_geometric_algebra R V G
:=
(fᵣ : R →+* G)
-- this follows normed_algebra in analysis.normed_space.basic
(fᵣ_algebra_map_eq : fᵣ = algebra_map R G)
(fᵥ : V →+ G)
-- this is the weaker form of the contraction rule for vectors
(vector_contract' : ∀ v, ∃ r, fᵥ v * fᵥ v = fᵣ r )

class geometric_algebra
(R : Type ur) [field R]
(V : Type uv) [add_comm_group V] [vector_space R V]
(G : Type ug) [ring G]
extends weak_geometric_algebra R V G
:=
(q : quadratic_form R V)
(vector_contract : ∀ v, fᵥ v * fᵥ v = fᵣ (q v) )

end prio

-- #print geometric_algebra

namespace geometric_algebra

variables [geometric_algebra R V G]

-- instance : inhabited (geometric_algebra R V G) := ⟨0⟩

end geometric_algebra

#lint