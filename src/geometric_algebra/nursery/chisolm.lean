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
  | 0 (scalar a) (scalar b) := hom_mv.scalar (a + b)
  | 1 (vector a) (vector b) := hom_mv.vector (a + b)
  | (n + 2) (graded a) (graded b) := hom_mv.graded (a ++ b)

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
  | 0 (multivector.scalar a) (multivector.scalar b) := multivector.scalar (a + b)
  | (nat.succ n) (multivector.augment a ar) (multivector.augment b br) :=
    multivector.augment (mv_add a b) (ar + br)

  instance has_add {n: ℕ} : has_add (multivector n) := { add := mv_add }
end mv

parameter v : G₁

--  Addition!
#check ((2 + v) : multivector 1)
#check ((2 + v) : multivector 2)

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
