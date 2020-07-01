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
-- import data.complex.module

import tactic.apply_fun
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

lemma assoc : ? A B C : G, (A * B) * C = A * (B * C) := ? A B C, semigroup.mul_assoc A B C

lemma left_distrib : ? A B C : G, A * (B + C) = (A * B) + (A * C) := ? A B C, distrib.left_distrib A B C

lemma right_distrib : ? A B C : G, (A + B) * C = (A * C) + (B * C) := ? A B C, distrib.right_distrib A B C

def prod_vec (a b : G?) : G := f? a * f? b

local infix `*?`:75 := prod_vec

def square (a : G) := a * a

def square_vec (a : G?) := a *? a

local postfix `²`:80 := square

local postfix `²?`:80 := square_vec

def sym_prod (a b : G) := a * b + b * a

def sym_prod_vec (a b : G?) := a *? b + b *? a

local infix `*?`:75 := sym_prod

local infix `*??`:75 := sym_prod_vec

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

noncomputable instance rc_alg : algebra ? ? := {
  smul := ? r c, r * c,
  to_fun := ?x, ?x, 0?,
  map_one' := rfl,
  map_mul' := begin
      intros x y,
      apply complex.ext,
      {
        simp only [complex.mul_re, sub_zero, mul_zero]
      },
      {
        simp only [add_zero, zero_mul, complex.mul_im, mul_zero]
      }
  end,
  map_zero' := rfl,
  map_add' := begin
    intros x y,
    apply complex.ext,
    {
      rw [complex.add_re],
    },
    {
      rw [complex.add_im, add_zero],
    }
  end,
  commutes' := begin
    intros r x,
    simp only [],
    cc,
  end,
  smul_def' := begin
    intros r x,
    simp only [],
    abel,
  end
}

noncomputable instance rrc_ga : geometric_algebra ? ? ? := {
  f? := {
    to_fun := ?x, ?x, 0?,
    map_zero' := rfl,
    map_add' := begin
      intros x y,
      apply complex.ext,
      {
        rw [complex.add_re],
      },
      {
        rw [complex.add_im, add_zero],
      }
    end
  },
  vec_sq_scalar := begin
    intro v,
    use v * v,
    simp only [add_monoid_hom.coe_mk],
    /-
      v : ?
      ? {re := v, im := 0} * {re := v, im := 0} = ?(algebra_map ? ?) (v * v)
    -/    
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
