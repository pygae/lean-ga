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

open_locale big_operators

variables (n : ℕ)

-- mapping from subsets of 1:n to coefficients
abbreviation idx := finset (fin n)

@[derive [add_comm_group, semimodule ℝ]]
def multivector : Type := idx n → ℝ

variables {n}

/-- generic product indexed by a sign function -/
def prod_aux (a b : multivector n) (sgn : idx n → idx n → ℤ) :
  multivector n :=
λ (ci : idx n),
  ∑ ai bi,
    if ai ∪ bi ≠ ci then 0 else  -- not this coefficient
    (a ai * b bi) * sgn ai bi

/-- wedge product of two multivectors-/
def wedge (a b : multivector n) : multivector n :=
prod_aux a b $ λ ai bi,
  if ai ∩ bi ≠ ∅  then 0 else  -- matching blades
  (-1) ^ (
    finset.card $ (ai.product bi).filter $ λ abj, abj.1 > abj.2
  )

/-- `wedge` is a bilinear map -/
def wedge.bilinear : multivector n →ₗ[ℝ] multivector n →ₗ[ℝ] multivector n :=
linear_map.mk₂ ℝ wedge
  (λ a₁ a₂ b, sorry)
  (λ c a b, sorry)
  (λ a b₁ b₂, sorry)
  (λ c a b, sorry)

/-- `wedge` is associative -/
def wedge.assoc : associative (wedge : multivector n → multivector n → multivector n) :=
λ a b c, sorry
