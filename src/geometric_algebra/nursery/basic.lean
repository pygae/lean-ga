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
import analysis.normed_space.real_inner_product

/-!
> TODO: Sync the docstring with actual code

# Geometric Algebra

In this file we define geometric algebra `𝒢[R]` over a commutative field `F`, and define some
algebraic structures on `𝒢[F]`. Type 𝒢 using `\McG`.

## Main definitions

* [geometric algebra](https://en.wikipedia.org/wiki/Geometric_algebra)
  * `quadratic_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/quadratic_form.lean
  * `field`: https://github.com/leanprover-community/mathlib/blob/master/src/algebra/field.lean
  * `bilinear_form`: https://github.com/leanprover-community/mathlib/blob/master/src/linear_algebra/bilinear_form.lean

## Notation

* `𝒢₃[F]` : the space of geometric algebra 𝒢(3)

## Implementation notes

We define geometric_algebra over any field `F`, not just `ℝ` or `ℂ` to be able to deal with.
In particular(hopefully), all definitions in this file are computable.

## Tags

geometric_algebra
-/

/-
  The following definition follows a not-so-general definition in
  Axiomatic development in Geometric Algebra for Physicists(GA4P).

  It is considered to be limited, which can be observed from
  the following implications of the definition:

  - it can't accept a vanilla vector algebra as a GA
  - it can't accept ℂ as a GA

  The definition is still of interest because from it we can
  reproduce many results in GA4P.
-/

class geometric_algebra (G : Type*) (K : Type*) (V : Type*)
[field K] [has_coe K G]
[add_comm_group V] [vector_space K V] [has_coe V G]
[ring G] [algebra K G]
 :=
(v_sq_in_k : ∀ v : V, ∃ k : K, (↑v : G) * (↑v : G) = (↑k : G))

namespace geometric_algebra

variables (G : Type*) (K : Type*) (V : Type*)
[field K] [has_coe K G]
[add_comm_group V] [vector_space K V] [has_coe V G]
[ring G] [algebra K G]

variables (a b c : G) [GA : geometric_algebra G K V]

lemma assoc : ∀ a b c : G, (a * b) * c = a * (b * c) := λ a b c, semigroup.mul_assoc a b c

lemma left_distrib : ∀ a b c : G, a * (b + c) = (a * b) + (a * c) := λ a b c, distrib.left_distrib a b c

lemma right_distrib : ∀ a b c : G, (a + b) * c = (a * c) + (b * c) := λ a b c, distrib.right_distrib a b c

end geometric_algebra

-- the trivial case: prove ℝ is a GA

instance : has_coe ℝ ℝ := { coe := λ x, x }

noncomputable instance : geometric_algebra ℝ ℝ ℝ := {
    v_sq_in_k := begin
        intro v,
        use (↑v) * (↑v),
        refl
    end
}

-- TODO: prove properties and identities for 𝒢


