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

/- Needed for zero_pairwise_ortho_vector -/
-- lemma pairwise_of_repeat {X : Type*} {x : X} {n : ℕ} {r : X → X → Prop} (hr : r x x) :
--   list.pairwise r (list.repeat x n) :=
-- begin
--   induction n with d hd,
--   { exact list.pairwise.nil},
--   { apply list.pairwise.cons _ hd,
--     intros a ha,
--     convert hr,
--     exact list.eq_of_mem_repeat ha,
--   }
-- end

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
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

def fᵥ : G₁ →+ G := f₁ G₀

def fₛ : G₀ →+* G := algebra_map G₀ G

lemma assoc : ∀ A B C : G, (A * B) * C = A * (B * C) := λ A B C, semigroup.mul_assoc A B C

lemma left_distrib : ∀ A B C : G, A * (B + C) = (A * B) + (A * C) := λ A B C, distrib.left_distrib A B C

lemma right_distrib : ∀ A B C : G, (A + B) * C = (A * C) + (B * C) := λ A B C, distrib.right_distrib A B C

def prod_vec (a b : G₁) : G := fᵥ a * fᵥ b

local infix `*ᵥ`:75 := prod_vec

def square (a : G) := a * a

def square_vec (a : G₁) := a *ᵥ a

local postfix `²`:80 := square

local postfix `²ᵥ`:80 := square_vec

def sym_prod (a b : G) := a * b + b * a

def sym_prod_vec (a b : G₁) := a *ᵥ b + b *ᵥ a

local infix `*₊`:75 := sym_prod

local infix `*₊ᵥ`:75 := sym_prod_vec


def is_orthogonal (a : G₁) (b : G₁) : Prop := sym_prod_vec a b = 0

theorem zero_is_orthogonal (a : G₁) : is_orthogonal 0 a := begin
  unfold is_orthogonal,
  unfold sym_prod_vec,
  unfold prod_vec,
  simp
end

/- a list of r orthogonal vectors, which may be non-unique -/
def pairwise_ortho_vector (r : ℕ) := {l : vector G₁ r // l.val.pairwise is_orthogonal}

/- need this for later, can't seem to get the type inference to work if I inline it-/
-- def zero_pairwise_ortho_vector (r : ℕ) : pairwise_ortho_vector r := ⟨
--   vector.repeat (0 : G₁) r, begin
--   unfold vector.repeat subtype.val,
--   apply pairwise_of_repeat,
--   apply zero_is_orthogonal,
-- end⟩


-- r-blades
def is_rblade (r : ℕ) (b : G) : Prop :=
  -- a product of orthogonal vectors an a scalar
  (∃ (k: G₀) (v : pairwise_ortho_vector r),
   b = fₛ k * list.prod (v.val.val.map fᵥ))

def Bᵣ (r : ℕ) := set_of (is_rblade r)

namespace Bᵣ
  variables {r : ℕ}

  lemma all_G₀_is_rblade0 (k : G₀) : is_rblade 0 (fₛ k) := begin
    use [k, list.pairwise.nil],
    unfold vector.nil subtype.val list.map,
    rw list.prod_nil,
    simp,
  end
  lemma all_G₁_is_rblade1 (a : G₁) : is_rblade 1 (fᵥ a) := begin
    use 1,
    use ⟨(vector.cons a vector.nil), list.pairwise_singleton _ a⟩,
    unfold vector.cons vector.nil subtype.val list.map,
    rw [list.prod_cons, list.prod_nil],
    simp,
  end

  instance has_coe_from_G₀ : has_coe G₀ (Bᵣ 0) := { coe := λ k, ⟨fₛ k, all_G₀_is_rblade0 k⟩}
  instance has_coe_from_G₁ : has_coe G₁ (Bᵣ 1) := { coe := λ a, ⟨fᵥ a, all_G₁_is_rblade1 a⟩}

  -- these are trivial, but somehow still needed
  instance has_coe_to_G : has_coe (Bᵣ r) G := { coe := subtype.val }
  @[simp]
  lemma is_rblade (b : Bᵣ r) : is_rblade r b := b.property

  /- todo: do we want this? -/
  -- instance has_zero : has_zero (Bᵣ r) := {
  --   zero := ⟨(0 : G), begin
  --     use [0, zero_pairwise_ortho_vector r],
  --     simp,
  --   end⟩ 
  -- }

  def neg (b : Bᵣ r) : Bᵣ r := ⟨-b.val, begin
    cases b with b' hb,
    exact exists.elim hb begin
      intros a ha,
      use -a,
      simp [ha],
    end
  end⟩

  instance has_neg (r : ℕ) : has_neg (Bᵣ r) := { neg := neg}
end Bᵣ

-- r-vectors
def Gᵣ (r : ℕ) := add_subgroup.closure (Bᵣ r)
namespace Gᵣ
  variables {r : ℕ}
  instance addgroup : add_comm_group (Gᵣ r) := (Gᵣ r).to_add_comm_group
end Gᵣ

-- multi-vectors
def Mᵣ (r : ℕ) := add_subgroup.closure (⋃ (r : ℕ), (Gᵣ r).carrier)
namespace Mᵣ
  variables {r : ℕ}
  instance addgroup : add_comm_group (Mᵣ r) := (Mᵣ r).to_add_comm_group
end Mᵣ

@[simp]
def is_scalar : G → Prop := is_rblade 0

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar (a b : G₁) : is_scalar (a *₊ᵥ b) :=
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
        have h2 : (fₛ (kab - ka - kb : G₀) : G) = sym_prod_vec a b, by {
          repeat {rw ring_hom.map_sub},
          rw h1,
          abel,
        },
        rw ← h2,
        rw is_scalar,
        apply Bᵣ.all_G₀_is_rblade0, -- this feels clumsy, can I make this automatic?
      end
    )
  )
)


end


end geometric_algebra
