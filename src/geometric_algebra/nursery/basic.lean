/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

The following code is inspired by 
[`feat(data/quaternion): define quaternions and prove some basic properties #2339`](https://github.com/leanprover-community/mathlib/pull/2339/)
and https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/basic.lean
-/

import tactic.ring_exp ring_theory.algebra algebra.opposites algebra.commute data.equiv.ring

/-!
# Geometric Algebra

In this file we define geometric algebra `𝔾[R]` over a commutative field `F`, and define some
algebraic structures on `𝔾[F]`. Type 𝔾 using `\bbG`.

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

@[nolint unused_arguments, ext]
structure geometric_algebra (V: Type*) (F: Type*) (g: Type*):=
mk {} :: (todo : F)

notation `𝒢[` V`,` F`,` g `]` := geometric_algebra V F g

namespace geometric_algebra

variables {V: Type*} {F: Type*} {g: Type*} [field F] (todo : F)

end geometric_algebra


