/-
Copyright (c) 2020 Eric Wieser, Utensil Song. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.real.basic
import algebra.algebra.basic
import algebra.direct_sum
import linear_algebra.direct_sum_module

/-!
# Derived from "A New Formalization of Origami in Geometric Algebra"

by Tetsuo Ida, Jacques Fleuriot, and Fadoua Ghourabi
-/

namespace translations.ida

@[ext]
structure multivector :=
(scalar : ℝ)
(vector : fin 3 → ℝ)
(bivec : fin 3 → ℝ)
(trivec : ℝ)

namespace multivector

/-! The basic abelian group operations are defined component-wise. -/
instance : has_zero multivector := ⟨
{ scalar := 0, vector := 0, bivec := 0, trivec := 0}⟩
instance : has_add multivector := ⟨λ x y,
{ scalar := x.scalar + y.scalar,
  vector := x.vector + y.vector,
  bivec := x.bivec + y.bivec,
  trivec := x.trivec + y.trivec}⟩
instance : has_sub multivector := ⟨λ x y,
{ scalar := x.scalar - y.scalar,
  vector := x.vector - y.vector,
  bivec := x.bivec - y.bivec,
  trivec := x.trivec - y.trivec}⟩
instance : has_neg multivector := ⟨λ x,
{ scalar := -x.scalar,
  vector := -x.vector,
  bivec := -x.bivec,
  trivec := -x.trivec}⟩

-- the original paper automates this a bit
instance : add_comm_group multivector :=
{ zero := 0, add := (+), sub := has_sub.sub, neg := has_neg.neg,
  add_zero := λ _, ext _ _ (add_zero _) (add_zero _) (add_zero _) (add_zero _),
  zero_add := λ _, ext _ _ (zero_add _) (zero_add _) (zero_add _) (zero_add _),
  add_assoc := λ _ _ _, ext _ _ (add_assoc _ _ _) (add_assoc _ _ _) (add_assoc _ _ _) (add_assoc _ _ _),
  add_comm := λ _ _, ext _ _ (add_comm _ _) (add_comm _ _) (add_comm _ _) (add_comm _ _),
  add_left_neg := λ _, ext _ _ (add_left_neg _) (add_left_neg _) (add_left_neg _) (add_left_neg _) }

/-! scalar multiplication is also component-wise -/
instance : has_scalar ℝ multivector := ⟨λ r x,
{ scalar := r • x.scalar,
  vector := r • x.vector,
  bivec := r • x.bivec,
  trivec := r • x.trivec}⟩

instance : semimodule ℝ multivector :=
{ smul := (•),
  smul_zero := λ _, ext _ _ (smul_zero _) (smul_zero _) (smul_zero _) (smul_zero _),
  zero_smul := λ _, ext _ _ (zero_smul _ _) (zero_smul _ _) (zero_smul _ _) (zero_smul _ _),
  add_smul := λ _ _ _, ext _ _ (add_smul _ _ _) (add_smul _ _ _) (add_smul _ _ _) (add_smul _ _ _),
  smul_add := λ _ _ _, ext _ _ (smul_add _ _ _) (smul_add _ _ _) (smul_add _ _ _) (smul_add _ _ _),
  one_smul := λ _, ext _ _ (one_smul _ _) (one_smul _ _) (one_smul _ _) (one_smul _ _),
  mul_smul := λ _ _ _, ext _ _ (mul_smul _ _ _) (mul_smul _ _ _) (mul_smul _ _ _) (mul_smul _ _ _),}

open matrix

instance : has_one multivector := ⟨
{ scalar := 1, vector := 0, bivec := 0, trivec := 0}⟩

/-! We do not fully translate the multiplicative structure, as the paper does not contain it and their source
code is no longer available. The content is trivial to reconstruct, but the results are uninteresting.

We continue anyway with just the important statements which the paper makes. -/
instance : has_mul multivector := ⟨λ x y,
{ scalar := x.scalar * y.scalar + dot_product x.vector y.vector
            - dot_product x.bivec y.bivec - x.trivec * y.trivec,
  vector := sorry,
  bivec := sorry,
  trivec := sorry}⟩

instance : ring multivector := sorry

instance : algebra ℝ multivector := sorry

end multivector

end translations.ida