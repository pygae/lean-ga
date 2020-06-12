/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song

This file is a failing attempt based on
A New Formalization of Origami in Geometric Algebra
by Tetsuo Ida, Jacques Fleuriot, and Fadoua Ghourabi

-/
import tactic.ring_exp ring_theory.algebra algebra.opposites data.equiv.ring
import linear_algebra.quadratic_form
import data.real.basic
import data.complex.basic
import analysis.normed_space.real_inner_product
import geometry.manifold.real_instances

import meta.coinductive_predicates

universe u

-- -- Generalize ℝ to field K to allow complexification
-- inductive grade (K : Type u) [field K]
-- | scalar           : K → grade
-- | vec              : fin 3 → K → grade
-- | bivec            : fin 3 → K → grade
-- | trivec           : K → grade

-- inductive mvec  (K : Type u) [field K]
-- | zero             : grade K → mvec
-- | cons             : grade K → mvec → mvec

-- Generalize ℝ to field K to allow complexification

--  invalid constructor ⟨...⟩, expected type is not an inductive type
-- def v : fin 3 → ℝ := ⟨0, 0, 0⟩

def vec_zero : ℝ × ℝ × ℝ := ⟨0, 0, 0⟩

-- mutual inductive grade, mvec
-- -- with gzero : grade
-- -- | scalar           : grade.scalar
-- -- | vec              : grade.vec
-- -- | bivec            : grade.bivec
-- -- | trivec           : grade.trivec
-- with grade : Type u
-- | scalar           : ℝ → grade
-- | vec              : (ℝ × ℝ × ℝ) → grade
-- | bivec            : (ℝ × ℝ × ℝ) → grade
-- | trivec           : ℝ → grade
-- | add              : grade → grade → grade
-- with mvec : Type u
-- | zero {}           : mvec
-- | app             : grade → mvec → mvec

-- inductive mvec : Type u
-- | scalar           : ℝ → mvec
-- | vec              : (ℝ × ℝ × ℝ) → mvec
-- | bivec            : (ℝ × ℝ × ℝ) → mvec
-- | trivec           : ℝ → mvec
-- | concat           : mvec → mvec → mvec

-- inductive mvec : Type u
-- | scalar           : ℝ → mvec
-- | vec              : (ℝ × ℝ × ℝ) → mvec
-- | bivec            : (ℝ × ℝ × ℝ) → mvec
-- | trivec           : ℝ → mvec
-- | concat           : mvec → mvec → mvec

mutual inductive grade, mvec
with grade : Type u
| scalar (s         : ℝ) : grade
| vec    (v : ℝ × ℝ × ℝ) : grade
| bivec  (B : ℝ × ℝ × ℝ) : grade
| trivec (Ixyz      : ℝ) : grade
with mvec : Type u
| atom (h : grade)            : mvec
| cons (h : grade) (t : mvec) : mvec

-- def mvec.make (h : grade) : mvec := mvec.cons h mvec.zero

mutual def grade.add, mvec.add
with grade.add : grade → grade → mvec
| (grade.scalar α) (grade.scalar β) := mvec.atom $ grade.scalar (α + β)
| (grade.vec ⟨x₁, x₂, x₃⟩) (grade.vec ⟨y₁, y₂, y₃⟩) := mvec.atom $ grade.vec ⟨x₁ + y₁, x₂ + y₂, x₃ + y₃⟩
| (grade.bivec ⟨A₁, A₂, A₃⟩) (grade.bivec ⟨B₁, B₂, B₃⟩) := mvec.atom $ grade.bivec ⟨A₁ + B₁, A₂ + B₂, A₃ + B₃⟩
| (grade.trivec γ) (grade.trivec δ) := mvec.atom $ grade.trivec (γ + δ)
| x y := mvec.add (mvec.atom x) (mvec.atom y)
with mvec.add : mvec → mvec → mvec
| x y := sorry

namespace mvec

-- def grade : mvec → fin 3 → mvec
-- | 

-- def add : mvec → mvec → mvec
-- | (scalar α) (scalar β) := scalar (α + β)
-- | (vec ⟨x₁, x₂, x₃⟩) (vec ⟨y₁, y₂, y₃⟩) := vec ⟨x₁ + y₁, x₂ + y₂, x₃ + y₃⟩
-- | (bivec ⟨A₁, A₂, A₃⟩) (vec ⟨B₁, B₂, B₃⟩) := bivec ⟨A₁ + B₁, A₂ + B₂, A₃ + B₃⟩
-- | (trivec γ) (trivec δ) := trivec (γ + δ)

end mvec



-- mutual def grade.add, mvec.add
-- with grade.add : grade → grade → mvec
-- | (scalar α) (scalar β) := scalar (α + β)
-- -- | (vec ⟨x₁, x₂, x₃⟩) (vec ⟨y₁, y₂, y₃⟩) := vec ⟨x₁ + y₁, x₂ + y₂, x₃ + y₃⟩
-- -- | (bivec ⟨A₁, A₂, A₃⟩) (vec ⟨B₁, B₂, B₃⟩) := bivec ⟨A₁ + B₁, A₂ + B₂, A₃ + B₃⟩
-- -- | (trivec γ) (trivec δ) := trivec (γ + δ)
-- with mvec.add : mvec → mvec → mvec

-- local notation g `⊹` m := mvec.app g m

-- #print mvec.zero

-- def g₀ : grade := grade.scalar 0

-- #check mvec.app g₀ mvec.zero

-- #check g₀ ⊹ mvec.zero

-- -- #reduce g₀ ⊹ mvec.zero

-- def mvec.add : mvec → mvec → mvec := sorry

namespace grade

def zero : grade := grade.scalar 0

def add : grade → grade → grade
| (scalar α) (scalar β) := scalar (α + β)
| (vec ⟨x₁, x₂, x₃⟩) (vec ⟨y₁, y₂, y₃⟩) := vec ⟨x₁ + y₁, x₂ + y₂, x₃ + y₃⟩
| (bivec ⟨A₁, A₂, A₃⟩) (vec ⟨B₁, B₂, B₃⟩) := bivec ⟨A₁ + B₁, A₂ + B₂, A₃ + B₃⟩
| (trivec γ) (trivec δ) := trivec (γ + δ)
| A B := sorry

end grade

-- inductive mvec
-- | zero {}          : mvec
-- | sum              : mvec → grade → mvec

-- namespace mvec

-- def add : mvec → mvec → grade

-- end mvec

-- instance : has_zero mvec := ⟨mvec.scalar 0⟩

-- instance : has_one mvec := ⟨mvec.scalar 0⟩

-- instance : has_add grade := {
--     add
--     | scalar
-- }

-- ⟨λ x y,
--   ⟨x.scalar + y.scalar, x.vec + y.vec, x.bivec + y.bivec, x.trivec + y.trivec⟩⟩

-- coinductive mvec (K : Type u) [field K] : grade K → Prop
-- | step : ∀{k : K} {ω : grade K}, a ∈ s → mvec ω → mvec (a :: ω)

-- coinductive 

/-



-/