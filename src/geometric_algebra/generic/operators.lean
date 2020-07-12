/-
Copyright (c) 2020 lean-ga Team. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

This file defines operators with local notations and no axioms.
-/
import tactic.lint

universes u

namespace geometric_algebra

class has_dot               (α : Type u) := (dot : α → α → α)
class has_wedge             (α : Type u) := (wedge : α → α → α)

-- class has_geom_prod         (α : Type u) := (geom_prod : α → α → α)

class has_scalar_prod       (α : Type u) := (scalar_prod : α → α → α)

class has_symm_prod         (α : Type u) := (symm_prod : α → α → α)
class has_asymm_prod        (α : Type u) := (asymm_prod : α → α → α)

class has_left_contract     (α : Type u) := (left_contract : α → α → α)
class has_right_contract    (α : Type u) := (right_contract : α → α → α)

-- export has_dot (dot)
-- export has_wedge (wedge)

local infix ⬝ := has_dot.dot
local infix ∧ := has_wedge.wedge

-- local infix ∘ := has_geom_prod.geom_prod

reserve infix ` ⊛ `:70
local infix ` ⊛ ` := has_scalar_prod.scalar_prod

reserve infix ` ⊙ `:70
reserve infix ` ⊠ `:70
local infix ` ⊙ ` := has_symm_prod.symm_prod
local infix ` ⊠ ` := has_asymm_prod.asymm_prod

reserve infix ` ⨼ `:70
reserve infix ` ⨽ `:70
local infix ⨼ := has_left_contract.left_contract
local infix ⨽ := has_right_contract.right_contract

end geometric_algebra

#lint

