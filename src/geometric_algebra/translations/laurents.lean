/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.field.basic
import algebra.module.prod
import algebra.punit_instances
import data.vector
import tactic

/-!
# Derived from "A Formalization of Grassmann-Cayley Algebra in Coq and Its Application to Theorem Proving in Projective Geometry"

by Laurent Fuchs and Laurent Théry
-/

namespace laurent

variables (α : Type) [field α]

-- vectors
def Kₙ : ℕ → Type
| 0 := unit
| (n + 1) := α × Kₙ n
-- addition and scalar multiplication
instance : Π (n : ℕ), add_comm_group (Kₙ α n)
| 0 := by {dunfold Kₙ, apply_instance}
| (n + 1) := by {dunfold Kₙ, haveI := Kₙ.add_comm_group n, apply_instance}
instance : Π n, module α (Kₙ α n)
| 0 := by {dunfold Kₙ, apply_instance}
| (n + 1) := by {dunfold Kₙ, haveI := Kₙ.module n, apply_instance}

-- multivectors
def Gₙ : ℕ → Type
| 0 := α
| (n + 1) := Gₙ n × Gₙ n
-- addition
instance : Π n, add_comm_group (Gₙ α n)
| 0 := by {unfold Gₙ, apply_instance}
| (n + 1) := by {unfold Gₙ, haveI := Gₙ.add_comm_group n, apply_instance}

variables {α}

-- coercions
def coe_α : Π {n}, α → Gₙ α n
| 0 k := k
| (n + 1) k := (coe_α 0, coe_α k)
instance has_coe_α : Π n, has_coe α (Gₙ α n) := λ n, ⟨coe_α⟩
def coe_Kₙ : Π {n}, Kₙ α n → Gₙ α n
| 0 k := 0
| (n + 1) ⟨x₁, x₂⟩ := (x₁, coe_Kₙ x₂)
instance has_coe_Kₙ : Π n, has_coe (Kₙ α n) (Gₙ α n) := λ n, ⟨coe_Kₙ⟩

-- conjugation
def conj : Π {n}, Gₙ α n → Gₙ α n
| 0 x := x
| (n + 1) ⟨x₁, x₂⟩ := (-conj x₁, conj x₂)
def conj_d : Π {n}, Gₙ α n → Gₙ α n
| 0 x := x
| (n + 1) ⟨x₁, x₂⟩ := (conj x₁, -conj x₂)
prefix `̅`:max := conj  -- this unicode is probably a bad idea...
notation `̅`:max x `ᵈ` := conj_d x -- this unicode is definitly a bad idea!

-- vee and wedge
reserve infix `⋎`:70
def vee : Π {n}, Gₙ α n → Gₙ α n → Gₙ α n
| 0 x y := (x * y : α)
| (n + 1) ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := let infix ` ⋎ ` := vee in
    (x₁ ⋎ y₂ + ̅x₂ ⋎ y₁, x₂ ⋎ y₂)
infix ` ⋎ ` := vee
reserve infix `⋏`:70
def wedge : Π {n}, Gₙ α n → Gₙ α n → Gₙ α n
| 0 x y := (x * y : α)
| (n + 1) ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := let infix ` ⋏ ` := wedge in
    (x₂ ⋏ y₂, x₁ ⋏ y₂ + x₂ ⋏ ̅y₁ᵈ)
infix ` ⋏ ` := wedge

variables {a b : Gₙ α 2}
#check (a + b) ⋎ (a ⋏ b)

end laurent
