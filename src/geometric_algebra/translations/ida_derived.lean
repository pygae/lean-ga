/-
Copyright (c) 2020 Eric Wieser, Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song
-/

import data.real.basic
import algebra.algebra.basic
import algebra.direct_sum.module

/-!
# Derived from "A New Formalization of Origami in Geometric Algebra"

This version is an incorrect but accidentally simpler attempt at translating what is now
`ida.multivector`. It is included for completeness, but not referenced in our paper.
-/

namespace ida'

open_locale big_operators
open_locale direct_sum

-- explicitly give coordinates
def rvector : fin 4 → Type
| ⟨0, _⟩ := ℝ  -- scalar
| ⟨1, _⟩ := ℝ × ℝ × ℝ
| ⟨2, _⟩ := ℝ × ℝ × ℝ
| ⟨3, _⟩ := ℝ  -- psuedo-scalar
| ⟨n + 4, _⟩ := by linarith

-- clumsy definition of addition within r-vectors
instance : Π i, add_comm_group (rvector i)
| ⟨0, _⟩ := by {unfold rvector, apply_instance}
| ⟨1, _⟩ := by {unfold rvector, apply_instance}
| ⟨2, _⟩ := by {unfold rvector, apply_instance}
| ⟨3, _⟩ := by {unfold rvector, apply_instance}
| ⟨n + 4, _⟩ := by linarith

-- lean has all we need to define multivector composition!
abbreviation multivector := ⨁ i, rvector i
def grade (m : multivector) (i) : rvector i := m i
def multivector.of (i) := direct_sum.of rvector i

-- define multiplication elementwise - tedious
def rvector_mul : Π {i j}, rvector i → rvector j → multivector
| ⟨0, _⟩ ⟨0, _⟩ a b :=
    multivector.of 0 (a * b : ℝ)
| ⟨1, _⟩ ⟨1, _⟩ ⟨a₁, a₂, a₃⟩ ⟨b₁, b₂, b₃⟩ :=
    -- euclidean dot product
    multivector.of 0 (a₁ * b₁ + a₂ * b₂ + a₃ * b₃ : ℝ) +
    -- cross product
    multivector.of 2 (sorry : ℝ × ℝ × ℝ)
| _ _ _ _ :=
    -- down this path lies madness or code generation
    sorry

-- build up the algebra structure
instance : has_mul multivector := ⟨λ a b, ∑ i j, rvector_mul (grade a i) (grade b j)⟩
instance : ring multivector := sorry
instance : algebra ℝ multivector := sorry

end ida'
