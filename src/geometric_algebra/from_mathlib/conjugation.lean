/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import geometric_algebra.from_mathlib.basic
import linear_algebra.clifford_algebra.conjugation
import algebra.module.opposites

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}
/-!
# Conjugations

This file contains additional lemmas about `clifford_algebra.reverse` and `clifford_algebra.involute`.

As more and more goes into Mathlib, this file will become smaller and spaller.
The links above will take you to the collection of mathlib theorems.
-/

namespace clifford_algebra


open mul_opposite

section
variables (Q)

def reverse_aux : clifford_algebra Q →ₐ[R] (clifford_algebra Q)ᵐᵒᵖ :=
  clifford_algebra.lift Q ⟨(op_linear_equiv R).to_linear_map.comp (ι Q),
    λ m, unop_injective $ by simp⟩

lemma reverse_eq_reverse_aux :
  reverse = (op_linear_equiv R).symm.to_linear_map ∘ₗ (reverse_aux Q).to_linear_map := rfl

@[simp] lemma unop_reverse_aux (x : clifford_algebra Q) :
  unop (reverse_aux Q x) = reverse x := rfl

end

section reverse
  open mul_opposite

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
