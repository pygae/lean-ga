/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

The following code is inspired by 
[`feat(data/quaternion): define quaternions and prove some basic properties #2339`](https://github.com/leanprover-community/mathlib/pull/2339/)
and https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/basic.lean
-/

import tactic.ring_exp ring_theory.algebra algebra.opposites algebra.commute data.equiv.ring
import linear_algebra.quadratic_form
import data.real.basic
import data.complex.basic

/-!
# Geometric Algebra

In this file we define geometric algebra `𝔾[R]` over a commutative field `F`, and define some
algebraic structures on `𝔾[F]`. Type 𝔾 using `\McG`.

In this file we define geometric algebra `𝒢[R]` over a commutative field `F`, and define some
algebraic structures on `𝒢[F]`. Type 𝒢 using `\McG`.

TODO: Decide the notation.

## Main definitions

* `geometric_algebra V F g` :
  [geometric algebra](https://en.wikipedia.org/wiki/Geometric_algebra), 
  a finite-dimensional quadratic space $V$ over a field $F$ with a symmetric bilinear form
  $g: V \times V \rightarrow F$
  * `quadratic_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/quadratic_form.lean
  * `field`: https://github.com/leanprover-community/mathlib/blob/master/src/algebra/field.lean
  * `bilinear_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/bilinear_form.lean

* `𝒢₃[F]` : the space of geometric algebra 𝒢(3)

We also define the following algebraic structures on `𝒢[F]`:

* `ring 𝒢[V, F, g]` and `algebra R 𝒢[V, F, g]` : for any commutative field `F`;
* `ring 𝒢₃[F]` and `algebra R 𝒢₃[F]` : for any commutative field `F`;
* `domain 𝒢₃[F]` : for a linear ordered commutative field `F`;
* `division_algebra 𝒢₃[F]` : for a linear ordered commutative field `F`.
'
## Notation

* `𝒢[V, F, g]` : the space of geometric algebra
* `𝒢₃[F]` : the space of geometric algebra 𝒢(3)

## Implementation notes

We define quaternions over any field `F`, not just `ℝ` or `ℂ` to be able to deal with.
In particular(hopefully), all definitions in this file are computable.

## Tags

geometric_algebra
-/

-- abbreviation vector_space (k : Type u) (M : Type v) [field k] [add_comm_group M] := module k M
-- structure quadratic_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M]


-- @[nolint unused_arguments, ext]
-- class geometric_algebra (S: Type*) (F: Type*)
-- [field F] [add_comm_group S] [V : vector_space F S] :=
-- (metric : bilin_form F S)

-- class geometric_algebra (F : Type*) (S : Type*) (G : Type*) [field F] [add_comm_group S] [V : vector_space F S]
-- extends semigroup G :=
-- (metric : bilin_form F S)

-- class geometric_algebra (G : Type*) (K : Type*) (V : Type*)
-- [field K] [has_coe K G]
-- [add_comm_group V] [vector_space K V] [has_coe V G]
-- [ring G]
--  :=
-- (v_sq_in_k : ∀ v : V, ∃ k : K, (↑v : G) * (↑v : G) = (↑k : G))

class geometric_algebra (G : Type*) (K : Type*) (V : Type*)
[field K] [has_lift K G]
[add_comm_group V] [vector_space K V] [has_lift V G]
[ring G] [algebra K G]
 :=
[assoc : ∀ (a b c : G), (a * b) * c = a * (b * c)]
[left_distrib : ∀ a b c : G, a * (b + c) = (a * b) + (a * c)]
[right_distrib : ∀ a b c : G, (a + b) * c = (a * c) + (b * c)]
(v_sq_in_k : ∀ v : V, ∃ k : K, (↑v : G) * (↑v : G) = (↑k : G))

/-

class test :=
(K : Type*)
(V : Type*)
[field : field K]
[group : add_comm_group V]
[space : vector_space K V]

#check test.mk ℝ ℝ -- test.mk ℝ ℝ : test

noncomputable instance test_rr : test := {
  K := ℝ,
  V := ℝ
}

class test'
(K : Type*)
(V : Type*)
[field : field K]
[group : add_comm_group V]
[space : vector_space K V]

#check test' ℝ ℝ -- test' ℝ ℝ : Type

instance test'_rr : test' ℝ ℝ := by sorry -- by apply_instance -- tactic.mk_instance failed to generate instance for

-- class test''
-- (K : Type*)
-- (V : Type*)
-- [field : field K]
-- [group : add_comm_group V]
-- extends vector_space K V -- invalid 'structure' extends, 'vector_space' is not a structure

-/


-- class geometric_algebra (G : Type*) (K : set G) (V : set G)
-- [field K]
-- [add_comm_group V] [vector_space K V] -- [Q : quadratic_form K V]
-- [ring G]
-- [is_subring K]
-- [is_subring V]
-- extends algebra K G
--  :=
-- (inner_product : quadratic_form K V)

-- notation `𝒢[` F`,` S`,` G `]` := geometric_algebra F S G

namespace geometric_algebra

variables (G : Type*) (K : Type*) (V : Type*)
[field K] [has_lift K G]
[add_comm_group V] [vector_space K V] [has_lift V G]
[ring G] [algebra K G]

variables (a b c : G) [GA : geometric_algebra G K V]

lemma gp_assoc : (a * b) * c = a * (b * c) := semigroup.mul_assoc a b c

lemma gp_distrib : a * (b + c) = a * b + a * c := distrib.left_distrib a b c

-- prove ℝ is a GA

instance : has_lift ℝ ℝ := { lift := λ x, x }

noncomputable instance : geometric_algebra ℝ ℝ ℝ := {
    assoc := (λ a b c, semigroup.mul_assoc a b c),
    left_distrib := (λ a b c, distrib.left_distrib a b c),
    right_distrib := (λ a b c, distrib.right_distrib a b c),
    v_sq_in_k := begin
        intro v,
        use (↑v) * (↑v),
        refl
    end
}

-- TODO: prove ℂ is a GA

-- instance : vector_space ℝ ℂ := sorry

-- := {! !}

-- instance : geometric_algebra ℝ ℂ ℂ := 
-- {
--     smul := _,
--     to_fun := _,
--     map_one' := _,
--     map_mul' := _,
--     map_zero' := _,
--     map_add' := _,
--     commutes' := _,
--     smul_def' := _
-- }

-- TODO: prove properties and identities for 𝒢

end geometric_algebra


