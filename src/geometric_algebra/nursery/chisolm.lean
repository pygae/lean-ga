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

import tactic.apply_fun
import tactic

universes u u₀ u₁

class geometric_algebra
-- Axiom 2: G contains a field G0 of characteristic zero which includes 0 and 1.
(G₀ : Type*) [field G₀]
-- Axiom 3: G contains a subset G1 closed under addition, 
-- and λ ∈ G0, v ∈ G1 implies λv = vλ ∈ G1.
(G₁ : Type*) [add_comm_group G₁] [vector_space G₀ G₁]
-- Axiom 1: G is a ring with unit. 
-- The additive identity is called 0 and the multiplicative identity is called 1.
(G : Type*) [ring G]
[algebra G₀ G]
:=
(f₁ : G₁ →+ G)
-- Axiom 4: The square of every vector is a scalar.
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k )

namespace geometric_algebra

section


parameters
{G₀ : Type u} [field G₀]
{G₁ : Type u} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type u} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]


-- define a blade representation
-- TODO: how to describe the fact that the vector argument to `graded` must be orthogonal?
inductive blade : nat → Type u
| scalar : G₀ → blade 0
| vector : G₁ → blade 1
| graded {n : ℕ} : G₁ → blade (n + 1) → blade (n + 2)
namespace blade
  instance g0_coe : has_coe G₀ (blade 0) := { coe := blade.scalar }
  instance g1_coe : has_coe G₁ (blade 1) := { coe := blade.vector }

  -- define zero and one on the blades
  def zero : Π (n : ℕ), blade n
  | 0 := blade.scalar (0 : G₀)
  | 1 := blade.vector (0 : G₁)
  | (nat.succ $ nat.succ n) := blade.graded (0 : G₁) (zero $ nat.succ n)
  instance has_zero {n : ℕ} : has_zero (blade n) := { zero := zero n }
  instance r0_has_one : has_one (blade 0) := { one := (1 : G₀) }

  -- define add on the blades
  def r0_add (a : blade 0) (b : blade 0) : blade 0 := begin
    cases a with a',
    cases b with b', 
    exact blade.scalar (a' + b')
  end
  instance r0_has_add : has_add (blade 0) := { add := r0_add }
  def r1_add (a : blade 1) (b : blade 1) : blade 1 := begin
    cases a,
    cases b,
    exact blade.vector (a_1 + b_1)
  end
  instance r1_has_add : has_add (blade 1) := { add := r1_add }
end blade

-- define a sum-of-blades representation
inductive hom_mv : nat → Type u
| scalar : blade 0 -> hom_mv 0
| vector : blade 1 -> hom_mv 1
| graded {n : ℕ} : list (blade $ nat.succ $ nat.succ n) → (hom_mv $ nat.succ $ nat.succ n)

namespace hom_mv
  def coe : Π {n : ℕ}, (blade n) → hom_mv n
  | 0 := hom_mv.scalar
  | 1 := hom_mv.vector
  | (r + 2) := λ b, hom_mv.graded [b]
  instance has_blade_coe {r : ℕ} : has_coe (blade r) (hom_mv r) := { coe := coe }
  instance has_g0_coe : has_coe G₀ (hom_mv 0) := { coe := λ s, coe s }
  instance has_g1_coe : has_coe G₁ (hom_mv 1) := { coe := λ s, coe s }

  -- define zero and one on the hom_mvs
  instance has_zero {n : ℕ} : has_zero (hom_mv n) := { zero := (0 : blade n) }
  instance r0_has_one : has_one (hom_mv 0) := { one := (1 : blade 0) }

  def add : Π {n : ℕ}, hom_mv n → hom_mv n → hom_mv n
  | 0 := λ a b, begin
    cases a with a',
    cases b with b',
    exact hom_mv.scalar (a' + b'),
  end
  | 1 := λ a b, begin
    cases a,
    cases b,
    exact hom_mv.vector (a_1 + b_1)
  end
  | (n + 2) := λ a b,begin
    cases a,
    cases b,
    exact hom_mv.graded (a_a ++ b_a),
  end
  instance has_add {n : ℕ} : has_add (hom_mv n) := { add := add }
end hom_mv

inductive multivector : nat → Type u
| scalar : hom_mv 0 → multivector 0
| augment {n : ℕ} : multivector n → hom_mv (nat.succ n) → multivector (nat.succ n)


namespace mv
  -- define zero and one on the multivectors
  def mv_zero : Π (n : ℕ), multivector n
  | 0 := multivector.scalar (0 : G₀)
  | 1 := multivector.augment (mv_zero 0) 0
  | (nat.succ $ nat.succ n) := multivector.augment (mv_zero $ nat.succ n) (hom_mv.graded [])
  def mv_one : Π (n : ℕ), multivector n
  | 0 := multivector.scalar (1 : G₀)
  | 1 := multivector.augment (mv_one 0) 0
  | (nat.succ $ nat.succ n) := multivector.augment (mv_one $ nat.succ n) (hom_mv.graded [])
  instance mv_has_zero {n : ℕ} : has_zero (multivector n) := { zero := mv_zero n }
  instance mv_has_one {n : ℕ} : has_one (multivector n) := { one := mv_one n }

  -- blades are coercible to multivectors
  def hom_mv_coe : Π {n : ℕ}, (hom_mv n) -> (multivector n)
  | nat.zero := λ b, multivector.scalar b
  | (nat.succ n) := λ b, multivector.augment (mv_zero n) b
  instance has_hom_mv_coe  {n : ℕ} : has_coe (hom_mv n) (multivector n) := { coe := hom_mv_coe }
  instance has_g0_coe : has_coe G₀ (multivector 0) := { coe := λ s, hom_mv_coe $ hom_mv.scalar $ blade.scalar s }
  instance has_g1_coe : has_coe G₁ (multivector 1) := { coe := λ v, hom_mv_coe $ hom_mv.vector $ blade.vector v }

  -- multivectors are up-coercible
  def augment_coe {n : ℕ} (mv : multivector n) : multivector (nat.succ n) := multivector.augment mv 0
  instance has_augment_coe {n : ℕ} : has_coe (multivector n) (multivector (nat.succ n)) := { coe := augment_coe }

  def mv_add : Π {n : ℕ}, multivector n → multivector n → multivector n
  | 0 := λ a b, begin
    cases a,
    cases b,
    exact multivector.scalar (a_1 + b_1)
  end
  | (nat.succ n) := λ a b, begin
    cases a with z z a' ar,
    cases b with z z b' br,
    exact multivector.augment (mv_add a' b') (ar + br)
  end
  instance has_add {n: ℕ} : has_add (multivector n) := { add := mv_add }
end mv

parameter v : G₁

--  Addition!
#check ((2 + v) : multivector 1)
#check ((2 + v) : multivector 2)

def fᵥ : G₁ →+ G := f₁ G₀

def fₛ : G₀ →+* G := algebra_map G₀ G

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def prod_vec (a b : G₁) := fᵥ a * fᵥ b

local infix `*ᵥ`:75 := prod_vec

def square (a : G) := a * a

def square_vec (a : G₁) := a *ᵥ a

local postfix `²`:80 := square

local postfix `²ᵥ`:80 := square_vec

def sym_prod (a b : G) := a * b + b * a

def sym_prod_vec (a b : G₁) := a *ᵥ b + b *ᵥ a

local infix `*₊`:75 := sym_prod

local infix `*₊ᵥ`:75 := sym_prod_vec

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar:
∀ (a b : G₁), ∃ k : G₀, a *₊ᵥ b = fₛ k :=
assume a b,
have h1 : (a + b)²ᵥ = a²ᵥ + b²ᵥ + a *₊ᵥ b, from begin
  unfold square_vec sym_prod_vec prod_vec,
  rw add_monoid_hom.map_add fᵥ a b,
  rw left_distrib,
  repeat {rw right_distrib},
  abel,
end,
have vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, v²ᵥ = fₛ k, from
  λ v, geometric_algebra.vec_sq_scalar(v),
exists.elim (vec_sq_scalar (a + b))
(
  assume kab,
  exists.elim (vec_sq_scalar a)
  (
    assume ka,
    exists.elim (vec_sq_scalar b)
    (
      assume kb,
      begin
        intros hb ha hab,
        rw [hb, ha, hab] at h1,
        use kab - ka - kb,
        repeat {rw ring_hom.map_sub},
        rw h1,
        abel,
      end
    )
  )
)

end

end geometric_algebra
