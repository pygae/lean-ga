import data.nat.basic
import data.real.basic
import data.fintype.basic
import algebra.big_operators
import linear_algebra.basic
import linear_algebra.tensor_product

/-!
# Derived from "Formalization of Geometric Algebra in HOL Light"

This captures a fragment of [this paper](https://link.springer.com/article/10.1007/s10817-018-9498-9),
and [this github repo](https://github.com/jrh13/hol-light/blob/4f2022d3b32eb791231abeb33a85ca818090ba3f/Multivariate/clifford.ml#L496-L504).

This file is primarily about definitions, we're not interested in the proofs used by others so much.
-/

namespace hol

open_locale big_operators

variables (n : ℕ)

-- mapping from subsets of 1:n to coefficients
abbreviation idx := finset (fin n)

@[derive [add_comm_group, semimodule ℝ]]
def multivector : Type := idx n → ℝ

variables {n}

def sym_diff {α : Type*} [has_sup α] [has_sdiff α] (A B : α) : α := (A \ B) ⊔ (B \ A)

/-- generic product indexed by a sign function -/
def generic_prod (sgn : idx n → idx n → ℝ) (a b : multivector n)  : multivector n :=
∑ ai bi in finset.univ,
  pi.single (sym_diff ai bi) ((a ai * b bi) * sgn ai bi)

/-- `generic_prod sgn` is a bilinear map -/
def generic_prod.bilinear (sgn : idx n → idx n → ℝ) :
  multivector n →ₗ[ℝ] multivector n →ₗ[ℝ] multivector n :=
begin
  with_cases { apply linear_map.mk₂ ℝ (generic_prod sgn) },
  case [H1 : a₁ a₂ b, H3 : a b₁ b₂] { all_goals {
    unfold generic_prod,
    simp [←finset.sum_add_distrib, add_mul, mul_add],
    dsimp only,
    congr, ext1, congr, ext1, convert pi.single_add _ _ _; refl
  } },
  case [H2 : c a b, H4 : c a b] { all_goals {
    unfold generic_prod,
    simp [finset.smul_sum, add_smul, smul_add, mul_assoc, mul_left_comm _ c _],
    dsimp only,
    congr, ext1, congr, ext1, convert pi.single_smul _ _ _; refl
  } }
end

/-- wedge product of two multivectors-/
def wedge : multivector n → multivector n → multivector n :=
generic_prod $ λ ai bi,
  if ai ∩ bi ≠ ∅  then 0 else  -- matching blades
  (-1) ^ (
    finset.card $ (ai.product bi).filter $ λ abj, abj.1 > abj.2
  )

/-- `wedge` is associative -/
def wedge.assoc : associative (wedge : multivector n → multivector n → multivector n) :=
λ a b c, sorry

end hol