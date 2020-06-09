/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song
-/

import tactic.ring_exp ring_theory.algebra algebra.opposites algebra.commute data.equiv.ring
import linear_algebra.quadratic_form
import data.real.basic
import data.complex.basic
import analysis.normed_space.real_inner_product
import geometry.manifold.real_instances

/-- The standard Euclidean space, functions on a finite type. For an `n`-dimensional space
use `euclidean_space (fin n)`.  -/
-- @[derive add_comm_group, nolint unused_arguments]
-- def euclidean_space (n : Type*) [fintype n] : Type* := n → ℝ

/--
The space `ℝ^n`. Note that the name is slightly misleading, as we only need a normed space
structure on `ℝ^n`, but the one we use here is the sup norm and not the euclidean one -- this is not
a problem for the manifold applications, but should probably be refactored at some point.
-/
-- def euclidean_space2 (n : ℕ) : Type := (fin n → ℝ)

constant n : ℕ

notation `ℝ[` n `]` := euclidean_space (fin n)

notation `𝔾[` n `]` := euclidean_space (fin 2^n)

@[derive add_comm_group, derive vector_space ℝ]
def geometric_algebra (N : Type*) [fintype N] : Type* := N → ℝ

#check ℝ[3]

constant R3 : ℝ[3]

#reduce R3 0

-- #check geometric_algebra

structure G (n : ℕ)



