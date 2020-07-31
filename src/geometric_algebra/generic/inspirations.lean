/-
Copyright (c) 2020 lean-ga Team. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

This file contains only imports which are just the lean files
that the authors draw inspirations from.
-/
import init.core
import init.function

import algebra.group.defs
import algebra.group.hom
-- [refactor(algebra/module): change module into an abbreviation for semimodule #2848](https://github.com/leanprover-community/mathlib/pull/2848)
import algebra.module
-- [feat(algebra/add_torsor): torsors of additive group actions #2720](https://github.com/leanprover-community/mathlib/pull/2720/files)
import algebra.add_torsor
import algebra.direct_limit
-- def closure
import group_theory.subgroup
import ring_theory.algebra
-- structure bilin_form
-- def is_sym
import linear_algebra.bilinear_form
-- def polar
-- structure quadratic_form
import linear_algebra.quadratic_form
-- def module_equiv_finsupp
import linear_algebra.basis
-- @[derive [add_comm_group, module R]] def dual
-- def eval_equiv
-- def dual_basis
import linear_algebra.dual
-- def tensor_product
import linear_algebra.tensor_product
-- @[reducible] def finite_dimensional
import linear_algebra.finite_dimensional
import linear_algebra.affine_space

import data.equiv.basic
import data.real.basic
import data.complex.basic
import data.complex.module
import data.matrix.basic

-- def angle
import geometry.euclidean
-- class inner_product_space
import geometry.manifold.real_instances

import analysis.convex.cone
import analysis.normed_space.basic
import analysis.normed_space.real_inner_product

import tactic
import tactic.lint

/-
### Lean/Mathlib PRs

- [`feat(data/quaternion): define quaternions and prove some basic properties #2339`](https://github.com/leanprover-community/mathlib/pull/2339/)
- [refactor(algebra/module): change module into an abbreviation for semimodule #2848](https://github.com/leanprover-community/mathlib/pull/2848)
- [feat(algebra/add_torsor): torsors of additive group actions #2720](https://github.com/leanprover-community/mathlib/pull/2720/files)
-/

#lint