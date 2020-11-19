/-
Copyright (c) 2020 Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Utensil Song, Eric Wieser

This file is based on https://arxiv.org/abs/1205.5935
-/
import algebra.group.hom
import algebra.algebra.basic
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
-- TODO clearly this should be nameed following "contraction rule", I'm thinking maybe `contract`?
(vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, f₁ v * f₁ v = algebra_map _ _ k )

namespace geometric_algebra

section basic

parameters
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

def fᵥ : G₁ →+ G := f₁ G₀

abbreviation fₛ : G₀ →+* G := algebra_map G₀ G

def prod_vec (a b : G₁) : G := fᵥ a * fᵥ b

local infix `*ᵥ`:75 := prod_vec

def square_vec (a : G₁) := a *ᵥ a

local postfix `²ᵥ`:80 := square_vec

def sym_prod_vec (a b : G₁) := a *ᵥ b + b *ᵥ a

local infix `*₊ᵥ`:75 := sym_prod_vec

def is_orthogonal (a : G₁) (b : G₁) : Prop := sym_prod_vec a b = 0

theorem zero_is_orthogonal (a : G₁) : is_orthogonal 0 a := begin
  unfold is_orthogonal,
  unfold sym_prod_vec,
  unfold prod_vec,
  simp
end

/-- a list of `r` orthogonal vectors, which may be non-unique -/
abbreviation pairwise_ortho_vector (r : ℕ) := {l : vector G₁ r // l.to_list.pairwise is_orthogonal}

/- need this for later, can't seem to get the type inference to work if I inline it-/
-- def zero_pairwise_ortho_vector (r : ℕ) : pairwise_ortho_vector r := ⟨
--   vector.repeat (0 : G₁) r, begin
--   unfold vector.repeat subtype.val,
--   apply pairwise_of_repeat,
--   apply zero_is_orthogonal,
-- end⟩


/-- r-blades -/
def is_rblade (r : ℕ) (b : G) : Prop :=
  -- a product of orthogonal vectors an a scalar
∃ (k : G₀) (v : pairwise_ortho_vector r),
  b = k • ((v : vector G₁ r).map fᵥ).to_list.prod

def Bᵣ (r : ℕ) := set_of (is_rblade r)

namespace Bᵣ
  variables {r : ℕ}

  lemma all_G₀_is_rblade0 (k : G₀) : is_rblade 0 (fₛ k) := begin
    use [k, list.pairwise.nil],
    simp [algebra.smul_def],
  end
  lemma all_G₁_is_rblade1 (a : G₁) : is_rblade 1 (fᵥ a) := begin
    use [1, ⟨vector.cons a vector.nil, list.pairwise_singleton _ a⟩],
    rw vector.to_list_map,
    simp,
  end

  instance has_coe_from_G₀ : has_coe G₀ (Bᵣ 0) := { coe := λ k, ⟨fₛ k, all_G₀_is_rblade0 k⟩}
  instance has_coe_from_G₁ : has_coe G₁ (Bᵣ 1) := { coe := λ a, ⟨fᵥ a, all_G₁_is_rblade1 a⟩}

  -- this is trivial, but maybe still needed
  @[simp]
  lemma coe_is_rblade (b : Bᵣ r) : is_rblade r b := b.prop

  /- todo: do we want this? -/
  -- instance has_zero : has_zero (Bᵣ r) := {
  --   zero := ⟨(0 : G), begin
  --     use [0, zero_pairwise_ortho_vector r],
  --     simp,
  --   end⟩ 
  -- }

  /- scalar multiple of an element of Bᵣ is also in Bᵣ -/
  lemma smul_mem {b : G} {k : G₀} (hb : is_rblade r b) : is_rblade r (k • b) := begin
    obtain ⟨a, factors, ha_1⟩ := hb,
    refine ⟨k * a, factors, _⟩,
    rw [ha_1, mul_smul],
  end

  /- now show via trivial proofs that Bᵣ is a mul_action and has_neg -/
  instance mul_action (r : ℕ) : mul_action G₀ (Bᵣ r) :=
  { smul := λ k b, ⟨k • (b : G), smul_mem b.prop⟩,
    one_smul := λ b, subtype.eq $ one_smul _ b,
    mul_smul := λ k₁ k₂ b, subtype.eq $ mul_smul k₁ k₂ b }

  instance has_neg (r : ℕ) : has_neg (Bᵣ r) := { neg := λ b, (-1 : G₀) • b }

end Bᵣ

/-- `r`-vectors -/
def Gᵣ (r : ℕ) := add_subgroup.closure (Bᵣ r)

example (r : ℕ) : add_comm_group (Gᵣ r) := by apply_instance
namespace Gᵣ
  variables {r : ℕ}

  -- this is trivial, but maybe needed
  -- instance has_coe_from_Bᵣ : has_coe (Bᵣ r) (Gᵣ r) := { coe := λ b, ⟨b.val, add_subgroup.subset_closure b.property⟩ }

  -- scalar multiple of an element of Gᵣ is also in Gᵣ
  lemma smul_mem {v : G} {k : G₀} (hv : v ∈ Gᵣ r) : (k • v) ∈ Gᵣ r :=
  add_subgroup.closure_induction hv
    (λ x hx, add_subgroup.subset_closure $ by exact Bᵣ.smul_mem hx)
    (by {
      rw smul_zero, exact (Gᵣ r).zero_mem, })
    (λ a b, by {
      rw smul_add, exact (Gᵣ r).add_mem, })
    (λ a, by {
      rw smul_neg, exact (Gᵣ r).neg_mem, })

  -- now show via trivial proofs that Gᵣ is a semimodule (basically a vector space)
  instance has_scalar (r : ℕ) : semimodule G₀ (Gᵣ r) :=
  { smul := λ k v, ⟨k • v, smul_mem v.prop⟩,
    one_smul := λ v, subtype.eq $ one_smul _ v,
    mul_smul := λ k₁ k₂ v, subtype.eq $ mul_smul k₁ k₂ v,
    smul_zero := λ v, subtype.eq $ smul_zero v,
    zero_smul := λ v, subtype.eq $ zero_smul _ v,
    add_smul := λ k₁ k₂ v, subtype.eq $ add_smul k₁ k₂ v,
    smul_add := λ k v₁ v₂, subtype.eq $ smul_add k v₁ v₂,
    zero_smul := λ v, subtype.eq $ zero_smul _ v }

end Gᵣ

/-- multi-vectors of at most grade `r` -/
def Mᵣ (r : ℕ) := add_subgroup.closure (⋃ (r' : fin r), (Gᵣ r').carrier)
example (r : ℕ) : add_comm_group (Mᵣ r) := infer_instance

abbreviation is_scalar : G → Prop := is_rblade 0

/--
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar (a b : G₁) : is_scalar (a *₊ᵥ b) :=
have h1 : (a + b)²ᵥ = a²ᵥ + b²ᵥ + a *₊ᵥ b, from begin
  unfold square_vec sym_prod_vec prod_vec,
  rw fᵥ.map_add a b,
  rw left_distrib,
  repeat {rw right_distrib},
  abel,
end,
have vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, v²ᵥ = fₛ k, from
  λ v, geometric_algebra.vec_sq_scalar(v),
begin
  obtain ⟨kab, hab⟩ := vec_sq_scalar (a + b),
  obtain ⟨ka, ha⟩ := vec_sq_scalar a,
  obtain ⟨kb, hb⟩ := vec_sq_scalar b,
  rw [hb, ha, hab] at h1,
  have h2 : (fₛ (kab - ka - kb : G₀) : G) = sym_prod_vec a b, by {
    repeat {rw ring_hom.map_sub},
    rw h1,
    abel,
  },
  rw ← h2,
  exact Bᵣ.all_G₀_is_rblade0 _, -- this feels clumsy, can I make this automatic?
end

end basic

end geometric_algebra
