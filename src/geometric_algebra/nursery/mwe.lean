/-
This file will be changed drastically all the time, it's only for reproduce the problem as 
a [minimal working example](https://leanprover-community.github.io/mwe.html) to ask on 
[Zulip](http://leanprover.zulipchat.com/)
-/

import algebra.group.hom
import ring_theory.algebra
import data.real.basic
import data.complex.basic

universes u u₀ u₁

class geometric_algebra
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀]
-- Axiom 3: G contains a subset G1 closed under addition, and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit.
-- The additive identity is called 0 and the multiplicative identity is called 1.
(G : Type*) [ring G] [algebra G₀ G]
:=
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k )

namespace geometric_algebra

section

variables
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

def square (a : G) := a * a

def sym_prod (a b : G) := a * b + b * a

local infix `*₊`:75 := sym_prod

local postfix `²`:80 := square

#check @f₁

-- implicit G₀
def f₁' : G₁ →+ G := f₁ G₀

#check @f₁'
/-
f₁' :
  Π {G₀ : Type u_4} [_inst_1 : field G₀]
  {G₁ : Type u_5} [_inst_2 : add_comm_group G₁] [_inst_3 : vector_space G₀ G₁]
  {G : Type u_6} [_inst_4 : ring G] [_inst_5 : algebra G₀ G]
  [_inst_6 : geometric_algebra G₀ G₁ G],
  G₁ →+ G
-/

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar_works_but_not_ideal :
∀ (a b : G₁), ∃ k : G₀,
  f₁ G₀ a *₊ f₁ G₀ b = algebra_map G₀ G k := by sorry
/-
OK, it seems Lean knows G₁ from a and b,
but requires explicit G₀ to know to which G f₁ belongs
-/

lemma vec_sym_prod_scalar_works_inferred_as_much_as_possible :
∀ (a b : G₁), ∃ k : G₀,
  f₁ G₀ a *₊ f₁ G₀ b = algebra_map _ G k := by sorry
/-
The only thing can be inferred is the type of k from k
-/

lemma vec_sym_prod_scalar_better_but_failed:
∀ (a b : G₁), ∃ k : G₀,
  f₁' a *₊ f₁' b = algebra_map G₀ G k := by sorry
/-
Here's why I "think" this should work:
- rhs fixed G₀ and G, a and b fixed G₁, Lean should know everything about f₁'
- plus *₊ fixed G too

Note that now I've made all parameters in f₁' implicit
-/

lemma vec_sym_prod_scalar_ideal_but_seems_impossble_in_lean:
∀ (a b : G₁), ∃ k : G₀,
  a *₊ b = k := by sorry
/-
Here's why I further "think" this should work:
- a and b fixed G₁
- *₊ fixed G
- G₀ can be inferred from [geometric_algebra G₀ G₁ G]

Here's why I want it:

It's closer to how it's stated in literature, without the hassle of homs
and I have to state more complicated theoerem that involves more +-*/exp
as in https://github.com/pygae/GAlgebra.jl/blob/master/test/runtests.jl#L321

Here's how I'm so close to it:

If I relax →+ and demand [has_coe G₀ G], then I get to state it like:

lemma vec_sym_prod_scalar [geometric_algebra G K V] :
∀ (a b : V), ∃ k : K, a *₊ b = (k : G) := by sorry

as in https://github.com/pygae/lean-ga/blob/master/src/geometric_algebra/nursery/basic.lean#L98
-/

end

end geometric_algebra