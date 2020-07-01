/-
This file will be changed drastically all the time, it's only for reproduce the problem as 
a [minimal working example](https://leanprover-community.github.io/mwe.html) to ask on 
[Zulip](http://leanprover.zulipchat.com/)
-/

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
import data.complex.module
import tactic

universes u u? u?

class geometric_algebra
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G? : Type*) [field G?]
-- Axiom 3: G contains a subset G1 closed under addition, 
-- and ? ? G0, v ? G1 implies ?v = v? ? G1.
(G? : Type*) [add_comm_group G?] [vector_space G? G?]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
(G : Type*) [ring G]
[algebra G? G]
:=
(f? : G? ?+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ? v : G?, ? k : G?, f? v * f? v = algebra_map _ _ k )

namespace geometric_algebra

section

parameters
{G? : Type*} [field G?]
{G? : Type*} [add_comm_group G?] [vector_space G? G?]
{G : Type*} [ring G] [algebra G? G] [geometric_algebra G? G? G]

def f? : G? ?+ G := f? G?

def f? : G? ?+* G := algebra_map G? G

instance field_ga (K : Type*) [field K] : geometric_algebra K K K := {
  f? := {
    to_fun := id,
    map_zero' := rfl,
    map_add' := begin
      simp only [forall_const, id.def, eq_self_iff_true]
    end
  },
  vec_sq_scalar := begin
    intro v,
    use v * v,
    simp only [algebra.id.map_eq_self, add_monoid_hom.coe_mk, id.def],
  end
}

-- noncomputable instance rc_alg : algebra ? ? := {
--   smul := ? r c, r * c,
--   to_fun := ?x, x,
--   map_one' := rfl,
--   map_mul' := begin
--       intros x y,
--       norm_cast,
--   end,
--   map_zero' := rfl,
--   map_add' := begin
--     intros x y,
--     norm_cast,
--   end,
--   commutes' := begin
--     intros r x,
--     simp only [],
--     cc,
--   end,
--   smul_def' := begin
--     intros r x,
--     simp only [],
--   end
-- }

noncomputable instance rrc_ga : geometric_algebra ? ? ? := {
  f? := {
    to_fun := ?x, x,
    map_zero' := rfl,
    map_add' := begin
      intros x y,
      norm_cast,
    end
  },
  vec_sq_scalar := begin
    intro v,
    use v * v,
    simp only [add_monoid_hom.coe_mk, ring_hom.map_mul],
    sorry
  end
}

-- noncomputable instance complex_ga : geometric_algebra ? ? ? := {
--   f? := {
--     to_fun := id,
--     map_zero' := rfl,
--     map_add' := by simp,
--   },
--   vec_sq_scalar := /- false -/
-- } 

end


end geometric_algebra
