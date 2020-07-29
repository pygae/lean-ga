import algebra.group
import tactic
import ring_theory.algebra
import linear_algebra.quadratic_form

universe u

variables (α : Type u)

/-
Groups defined three ways
-/
namespace Group

namespace extends_has

structure group extends has_mul α, has_one α, has_inv α :=
(mul_assoc : ∀ (a b c : α), a * b * c = a * (b * c))
(one_mul : ∀ (a : α), 1 * a = a)
(mul_one : ∀ (a : α), a * 1 = a)
(mul_left_inv : ∀ (a : α), a⁻¹ * a = 1)

end extends_has

namespace explicit

structure group :=
(mul : α → α → α)
(infix `*` := mul)
(mul_assoc : ∀ (a b c : α), a * b * c = a * (b * c))

(one : α)
(notation `𝟙` := one)
(one_mul : ∀ (a : α), 𝟙 * a = a)
(mul_one : ∀ (a : α), a * 𝟙 = a)

(inv : α → α)
(postfix `⁻¹` := inv)
(mul_left_inv : ∀ (a : α), a⁻¹ * a = 𝟙)

end explicit

namespace in_real_lean

class group (α : Type u) extends monoid α, has_inv α :=
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)

class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)

attribute [to_additive add_group] group

end in_real_lean

end Group

/-
An example of a proof
-/
namespace proof_demo
open int

theorem le.antisymm : ∀ {a b : ℤ}, a ≤ b → b ≤ a → a = b :=
begin
assume a b : ℤ, assume (H₁ : a ≤ b) (H₂ : b ≤ a),
obtain ⟨n, Hn⟩ := int.le.dest H₁,
obtain ⟨m, Hm⟩ := int.le.dest H₂,
have H₃ : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : rfl
      ... = a + (n + m)                     : by rw of_nat_eq_coe
      ... = a + n + m                       : by rw add_assoc
      ... = b + m                           : by rw Hn
      ... = a                               : Hm
      ... = a + 0                           : by rw add_zero,
have H₄ : of_nat (n + m) = of_nat 0, from add_left_cancel H₃,
have H₅ : n + m = 0,                 from of_nat.inj H₄,
have h₆ : n = 0,                     from nat.eq_zero_of_add_eq_zero_right H₅,
show a = b, from
  calc
    a = a + 0    : by simp_rw [add_zero]
  ... = a + n    : by simp_rw [h₆, int.coe_nat_zero]
  ... = b        : Hn
end
end proof_demo


/- An example of geometric algebra -/
namespace GA

namespace unbundled_weak

variables (K : Type u) [field K]

variables (V : Type u) [add_comm_group V] [vector_space K V]

def sqr {α : Type u} [has_mul α] (x : α) := x * x
local postfix `²`:80 := sqr

structure GA (G : Type u) [ring G] [algebra K G] :=
(fₛ : K →+* G)
(fᵥ : V →ₗ[K] G)
(vec_contraction : ∀ v : V, ∃ k : K, (fᵥ v)² = fₛ k)

/-
  Symmetrised product of two vectors must be a scalar
-/
example
(G : Type u) [ring G] [algebra K G] [ga : GA K V G] :
∀ aᵥ bᵥ : V, ∃ kₛ : K,
  let a := ga.fᵥ aᵥ, b := ga.fᵥ bᵥ, k := ga.fₛ kₛ in
    a * b + b * a = k :=
begin
  -- simplify the goal by definition, i.e. remove let etc.
  delta,

  -- vectors aᵥ bᵥ
  assume aᵥ bᵥ,

  -- multivectors a b
  set a := ga.fᵥ aᵥ,
  set b := ga.fᵥ bᵥ,

  -- rewrite the goal to square terms
  rw (show a * b + b * a = (a + b)² - a² - b², from begin
    unfold sqr,
    simp only [left_distrib, right_distrib],
    abel,
  end),
  
  -- rewrite square terms of vectors
  -- to scalars using the vector contraction axiom
  obtain ⟨kabₛ, hab⟩ := ga.vec_contraction (aᵥ + bᵥ),
  obtain ⟨kaₛ, ha⟩ := ga.vec_contraction (aᵥ),
  obtain ⟨kbₛ, hb⟩ := ga.vec_contraction (bᵥ),

  -- map the above to multivectors
  rw [
    show (a + b)² = ga.fₛ kabₛ, by rw [← hab, linear_map.map_add],
    show a² = ga.fₛ kaₛ, by rw [← ha],
    show b² = ga.fₛ kbₛ, by rw [← hb]
  ],

  -- collect scalars
  simp only [← ring_hom.map_sub],

  -- use the scalars as the witness of the existence
  use kabₛ - kaₛ - kbₛ,
end

end unbundled_weak

namespace bundled_quad

variables (K : Type u) [field K]

-- variables (V : Type u) [add_comm_group V] [vector_space K V]

def sqr {α : Type u} [has_mul α] (x : α) := x * x
local postfix `²`:80 := sqr

structure GA (G : Type u) [ring G] [algebra K G] := 
(V : Type u) [vec_is_acg : add_comm_group V] [vec_is_vs : vector_space K V]
(fₛ : K →+* G)
(fᵥ : V →ₗ[K] G)
(q : quadratic_form K V)
(vec_contraction : ∀ v : V, (fᵥ v)² = fₛ (q v))

attribute [instance] GA.vec_is_acg
attribute [instance] GA.vec_is_vs

/-
  Symmetrised product of two vectors must be a scalar
-/
example (G : Type u) [ring G] [algebra K G] [ga : GA K G] :
∀ aᵥ bᵥ : ga.V, let a := ga.fᵥ aᵥ, b := ga.fᵥ bᵥ in
    a * b + b * a = ga.fₛ (quadratic_form.polar ga.q aᵥ bᵥ) :=
begin
  -- simplify the goal by definition, i.e. remove let etc.
  delta,

  -- vectors aᵥ bᵥ
  assume aᵥ bᵥ,

  -- multivectors a b
  set a := ga.fᵥ aᵥ with ha,
  set b := ga.fᵥ bᵥ with hb,

  rw [ha, hb],
  unfold quadratic_form.polar,
  simp only [ring_hom.map_add, ring_hom.map_sub, ←GA.vec_contraction],
  unfold sqr,
  simp only [linear_map.map_add, linear_map.map_sub],
  noncomm_ring,
end

end bundled_quad

end GA