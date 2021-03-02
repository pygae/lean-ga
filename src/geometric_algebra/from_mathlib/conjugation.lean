/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import geometric_algebra.from_mathlib.basic
import algebra.module.opposites

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
/-!
# Conjugations

This file defines the grade reversal and grade involution functions, `reverse` and `involute`.

It does not define any notation for now.
-/

namespace clifford_algebra

section involute

  /-- Grade involution, inverting the sign of each basis vector -/
  def involute : clifford_algebra Q →ₐ[R] clifford_algebra Q :=
  clifford_algebra.lift Q ⟨-(ι Q), λ m, by simp⟩

  @[simp] lemma involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  by simp [involute]

  @[simp] lemma involute_algebra_map (r : R) : involute (↑ₐr : clifford_algebra Q) = ↑ₐr :=
  involute.commutes _

  @[simp] lemma involute_comp_involute : involute.comp involute = alg_hom.id R (clifford_algebra Q) :=
  by { ext, simp }

  lemma involute_involutive : function.involutive (involute : _ → clifford_algebra Q) :=
  alg_hom.congr_fun involute_comp_involute

  lemma involute_prod_map_ι : ∀ l : list M,
    involute (l.map $ ι Q).prod = ((-1 : R)^l.length) • (l.map $ ι Q).prod
  | [] := by simp
  | (x :: xs) := by simp [pow_add, involute_prod_map_ι xs]

end involute

section reverse
  open opposite

  /-- Grade reversion, inverting the multiplication order of basis vectors -/
  def reverse : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
  (op_linear_equiv R).symm.to_linear_map.comp (
    clifford_algebra.lift Q ⟨(opposite.op_linear_equiv R).to_linear_map.comp (ι Q),
      λ m, unop_injective $ by simp⟩).to_linear_map

  @[simp] lemma reverse_ι (m : M) : reverse (ι Q m) = ι Q m :=
  by simp [reverse]

  @[simp] lemma reverse_algebra_map (r : R) : reverse (↑ₐr : clifford_algebra Q) = ↑ₐr :=
  by simp [reverse]

  @[simp] lemma reverse_one  : reverse (1 : clifford_algebra Q) = 1 :=
  reverse_algebra_map 1

  @[simp] lemma reverse_mul (a b : clifford_algebra Q) : reverse (a * b) = reverse b * reverse a :=
  by simp [reverse]

  @[simp] lemma reverse_involutive : function.involutive (reverse : _ → clifford_algebra Q) :=
  λ x, by induction x using clifford_algebra.induction; simp [*]

  lemma reverse_prod_map_ι : ∀ (l : list M), reverse (l.map $ ι Q).prod = (l.map $ ι Q).reverse.prod
  | [] := by simp
  | (x :: xs) := by simp [reverse_prod_map_ι xs]

  lemma reverse_involute_commute : function.commute (reverse : _ → clifford_algebra Q) involute :=
  λ x, by induction x using clifford_algebra.induction; simp [*]

  /-- helper lemma for expanding the sign of reverse -/
  lemma reverse_prod_sign_aux (n : ℕ) :
    (-1 : R)^((n + 1)*(n + 1 + 1)/2) = (-1 : R)^(n*(n + 1)/2) * (-1 : R)^(n + 1) :=
  begin
    -- work with just the exponents
    rw ←pow_add,
    conv_rhs { rw neg_one_pow_eq_pow_mod_two },
    conv_lhs { rw neg_one_pow_eq_pow_mod_two },
    congr' 1,
    -- work through the ugly nat proof
    rw [add_mul, one_mul, mul_add _ (n + 1), mul_one, add_assoc, add_assoc n 1 1, ←add_assoc n n, ←mul_two, ←mul_two],
    have : 0 < 2 := by linarith,
    rw [nat.add_div_eq_of_add_mod_lt _, nat.add_div_eq_of_add_mod_lt _, nat.mul_div_cancel _ this, nat.mul_div_cancel _ this],
    -- extra goals created by `add_div_eq_of_add_mod_lt`
    { rw [nat.mul_mod_left, nat.mul_mod_left, zero_add],
      exact this },
    { rw [nat.add_mod (n * 2), nat.mul_mod_left, nat.mul_mod_left, add_zero, nat.zero_mod, add_zero],
      exact nat.mod_lt _ this },
  end
  
  /-- TODO: this needs an assumption that the vectors are othogonal -/
  lemma reverse_prod_map_sign (l : list M):
    reverse (l.map $ ι Q).prod = ((-1 : R)^(l.length*(l.length + 1)/2)) • (l.map $ ι Q).prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [hxs, reverse_prod_sign_aux, mul_smul],
    congr,
    sorry, -- this needs to be an assumption
  end

end reverse

end clifford_algebra
