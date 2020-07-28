import algebra.group
import tactic
import ring_theory.algebra
import linear_algebra.quadratic_form

universe u

variables (α : Type u)

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

namespace GA

namespace first

variables (K : Type u) [field K]

variables (V : Type u) [add_comm_group V] [vector_space K V]

structure GA
(G : Type u)
[ring G] extends algebra K G :=
(fₛ : K →+* G)
(fᵥ : V →+ G)
-- (infix ` ❍ `:70 := has_mul.mul)
(postfix `²`:80 := λ x, x * x)
(contraction : ∀ v : V, ∃ k : K, (fᵥ v)² = fₛ k)

-- local infix ` ❍ `:70 := has_mul.mul
local postfix `²`:80 := λ x, x * x

/-
  Symmetrised product of two vectors must be a scalar
-/
example
(G : Type u) [ring G] [ga : GA K V G] :
∀ aᵥ bᵥ : V, ∃ kₛ : K,
let a := ga.fᵥ aᵥ, b := ga.fᵥ bᵥ, k := ga.fₛ kₛ in
a * b + b * a = k :=
begin
  assume aᵥ bᵥ,
  let a := ga.fᵥ aᵥ, 
  let b := ga.fᵥ bᵥ,
  have h1 : (a + b)² = a * b + b * a + a² + b², from begin
    dsimp,
    rw left_distrib,
    repeat {rw right_distrib},
    abel,
  end,
  obtain ⟨kabₛ, hab⟩ := GA.contraction ga (aᵥ + bᵥ),
  obtain ⟨kaₛ, ha⟩ := GA.contraction ga (aᵥ),
  obtain ⟨kbₛ, hb⟩ := GA.contraction ga (bᵥ),
  have h2 : ga.fₛ (kabₛ - kaₛ - kbₛ) = a * b + b * a, by {
    repeat {rw ring_hom.map_sub},
    apply_fun (λ x, x - b * b - a * a) at h1,
    simp [] at h1 ha hb hab,
    simp [←h1, ha, hb, hab],
    abel,
  },
  use kabₛ - kaₛ - kbₛ,
  rw h2,
  abel,
end

end first

end GA