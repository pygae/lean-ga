/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra
import data.zmod.basic

/-!
# Tools built on top of Mathlib's `linear_algebra.clifford_algebra`

Many things here may become "generalized out" as mathlib grows, or end up being PR'd upstream
-/

/-! Random theorems that belong in mathlib not related to GA -/
section to_upstream

  namespace finsupp

  variables {α : Type*} {M : Type*} [has_zero M]

  lemma single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a :=
  begin
    rw [single_apply, single_apply],
    ext,
    split_ifs,
    { rw h, },
    { rw [zero_apply, single_apply, if_t_t], },
  end

  end finsupp

  namespace add_monoid_algebra

  variables (k : Type*) {G : Type*}
  /--
  The `alg_hom` which maps from a grading of an algebra `A` back to that algebra.
  -/
  noncomputable def sum_id {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] :
    add_monoid_algebra A G →ₐ[k] A :=
  lift_nc_alg_hom (alg_hom.id k A) ⟨λ g, 1, by simp, λ a b, by simp⟩ (by simp)

  lemma sum_id_apply {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [add_monoid G] (g : add_monoid_algebra A G) :
    sum_id k g = g.sum (λ _ gi, gi) :=
  by simp [sum_id, lift_nc_alg_hom, lift_nc_ring_hom, lift_nc, alg_hom.id, ring_hom.id]

  end add_monoid_algebra

  namespace opposite

  variables (R : Type*) {M : Type*} [comm_semiring R] [semiring M] [algebra R M]

  @[simps apply]
  def op_linear_equiv : M ≃ₗ[R] Mᵒᵖ :=
  { map_smul' := opposite.op_smul, .. op_add_equiv }

  @[simp] lemma coe_op_linear_equiv : (op_linear_equiv R : M → Mᵒᵖ) = op := rfl
  @[simp] lemma coe_op_linear_equiv_symm :
    ((op_linear_equiv R).symm : Mᵒᵖ → M) = unop := rfl

  @[simp] lemma coe_op_linear_equiv_to_linear_map : ((op_linear_equiv R).to_linear_map : M → Mᵒᵖ) = op := rfl
  @[simp] lemma coe_op_linear_equiv_symm_to_linear_map :
    ((op_linear_equiv R).symm.to_linear_map : Mᵒᵖ → M) = unop := rfl

  end opposite

end to_upstream


variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

namespace clifford_algebra

/-- An induction principle for the `clifford_algebra` derived from `free_algebra.induction`.

If `C` holds for the `algebra_map` of `r : R` into `clifford_algebra Q`, the `ι` of `x : M`, and is
preserved under addition and muliplication, then it holds for all of `clifford_algebra Q`.
-/
@[elab_as_eliminator]
lemma induction {C : clifford_algebra Q → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (clifford_algebra Q) r))
  (h_grade1 : ∀ x, C (ι Q x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : clifford_algebra Q) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : subalgebra R (clifford_algebra Q) := {
    carrier := C,
    one_mem' := h_grade0 1,
    zero_mem' := h_grade0 0,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = algebra_map R s (Q m) } :=
  ⟨{
    to_fun := λ x, ⟨(ι Q) x, h_grade1 x⟩,
    map_add' := λ x y, by { simp_rw (ι Q).map_add x y, refl, },
    map_smul' := λ c x, by { simp_rw (ι Q).map_smul c x, refl, }, },
    λ m, begin
      change (⟨ι Q m * ι Q m, _⟩ : s) = ⟨algebra_map R (clifford_algebra Q) (Q m), _⟩,
      simp_rw ι_square_scalar,
    end ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of of.prop),
  { ext,
    simp [of, subtype.coind], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of.1 of.prop a),
  simp [alg_hom.ext_iff] at of_id,
  exact of_id a,
end

section involute

  /-- Grade involution, inverting the sign of each basis vector -/
  def involute : clifford_algebra Q →ₐ[R] clifford_algebra Q :=
  clifford_algebra.lift Q (-(ι Q)) $ λ m, by simp

  @[simp]
  lemma involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  by simp [involute]

  @[simp]
  lemma involute_algebra_map (r : R) : involute (algebra_map R (clifford_algebra Q) r) = algebra_map R _ r :=
  by simp [involute]

  lemma involute_involutive : function.involutive (involute : clifford_algebra Q → clifford_algebra Q) :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

  lemma involute_prod_map_ι (l : list M) : involute (l.map $ ι Q).prod = ((-1 : R)^l.length) • (l.map $ ι Q).prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [pow_add, hxs],
  end

end involute

section reverse
  open opposite

  /-- Grade reversion, inverting the multiplication order of basis vectors -/
  def reverse : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
  (op_linear_equiv R).symm.to_linear_map.comp (
    clifford_algebra.lift Q ((opposite.op_linear_equiv R).to_linear_map.comp (ι Q))
      $ λ m, unop_injective $ by simp).to_linear_map

  @[simp]
  lemma reverse_ι (m : M) : reverse (ι Q m) = ι Q m :=
  by simp [reverse]

  @[simp]
  lemma reverse_algebra_map (r : R) : reverse (algebra_map R (clifford_algebra Q) r) = algebra_map R _ r :=
  by simp [reverse]

  @[simp]
  lemma reverse_one  : reverse (1 : clifford_algebra Q) = 1 :=
  reverse_algebra_map 1

  @[simp]
  lemma reverse_mul (a b : clifford_algebra Q) : reverse (a * b) = reverse b * reverse a :=
  by simp [reverse]

  lemma reverse_involutive : function.involutive (reverse : clifford_algebra Q → clifford_algebra Q) :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

  lemma reverse_prod_map_ι (l : list M) : reverse (l.map $ ι Q).prod = (l.map $ ι Q).reverse.prod :=
  begin
    induction l with x xs hxs,
    { simp },
    simp [hxs],
  end

  lemma reverse_involute_commute : function.commute (reverse : clifford_algebra Q → clifford_algebra Q) involute :=
  begin
    intro x,
    induction x using clifford_algebra.induction; simp [*],
  end

  /-- helper lemma for expanding the sign of reverse -/
  lemma reverse_prod_sign_aux (n : ℕ) :
    (-1 : R)^((n + 1)*(n + 1 + 1)/2) = (-1 : R)^(n*(n + 1)/2) * (-1 : R)^(n + 1) :=
  begin
    rw ←pow_add,
    conv_rhs { rw neg_one_pow_eq_pow_mod_two },
    conv_lhs { rw neg_one_pow_eq_pow_mod_two },
    congr' 1,
    rw [add_mul, one_mul, mul_add _ (n + 1), mul_one, add_assoc, add_assoc n 1 1, ←add_assoc n n],
    rw nat.add_div,
    rw nat.add_div,
    rw nat.div_self,
    rw nat.mod_self,
    rw add_zero,
    rw nat.add_mod (n + n),
    rw nat.mod_self,
    rw add_zero,
    rw nat.mod_mod,
    have h1 : (n + n) % 2 = 0 := by {rw ←mul_two, simp},
    have h2 : n * (n + 1) % 2 = 0 := sorry, -- should be in mathlib, i hope?
    have h3 : 2 ≠ 0 := by linarith,
    simp [h1, h2, if_neg h3, ←mul_two],
    linarith,
    linarith,
    linarith
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

section grades'

  abbreviation grade_type := zmod 2

  /--
  Separate an element of the clifford algebra into its `zmod 2`-graded components.

  This is defined as an `alg_hom` to `add_monoid_algebra` so that algebra operators can be moved
  before and after the mapping.

  This is _not_ the normal ℕ-graded definition that we usually use in GA. That definition is harder...
  -/
  noncomputable
  def grades' : (clifford_algebra Q) →ₐ[R] add_monoid_algebra (clifford_algebra Q) (grade_type) :=
  lift Q ((finsupp.lsingle 1).comp (ι Q)) $ λ x, begin
    rw [linear_map.comp_apply, finsupp.lsingle_apply, add_monoid_algebra.single_mul_single],
    simp,
    congr,
  end


  /-- Recombining the grades recovers the original element-/
  lemma sum_id_grades :
    (add_monoid_algebra.sum_id R).comp grades' = alg_hom.id R (clifford_algebra Q) :=
  begin
    ext,
    simp [grades', add_monoid_algebra.sum_id_apply, finsupp.sum_single_index],
  end

  noncomputable
  instance : has_coe (add_monoid_algebra (clifford_algebra Q) grade_type) (clifford_algebra Q) := ⟨
    (add_monoid_algebra.sum_id R : add_monoid_algebra (clifford_algebra Q) grade_type →ₐ[R] (clifford_algebra Q))
  ⟩

  @[simp, norm_cast]
  lemma coe_def (x : add_monoid_algebra (clifford_algebra Q) grade_type) : (x : clifford_algebra Q) = add_monoid_algebra.sum_id R x := rfl


  /-- An element of `R` lifted with `algebra_map` has a single grade 0 element -/
  lemma grades'.map_algebra_map (r : R) :
    grades' (algebra_map R (clifford_algebra Q) r) = finsupp.single 0 (algebra_map R _ r) :=
  by simp

  /-- An element of `X` lifted with the canonical `ι R` function has a single grade 1 element -/
  lemma grades'.map_ι (x : M) :
    grades' (ι Q x) = finsupp.single 1 (ι Q x) :=
  by simp [grades']

  -- note this is true for any `zero_hom`, not just `grades'`. Of course, then we need to repeat this
  -- for `add_monoid_hom`, `add_equiv`, `linear_map`, `ring_hom`, `ring_equiv`, `alg_hom`, ...
  private lemma map_single_apply (x : clifford_algebra Q) (i j : grade_type) :
    grades' (finsupp.single i x j) = finsupp.single i (grades' x) j :=
  by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades', grades'.map_zero]

  -- The grade-`i` part consists only of itself -/
  @[simp]
  lemma grades'.map_grades' (x : clifford_algebra Q) (i : grade_type) :
    grades' (grades' x i) = finsupp.single i (grades' x i) :=
  begin
    induction x using clifford_algebra.induction generalizing i,
    case h_grade0 : {
      rw [grades'.map_algebra_map, map_single_apply, grades'.map_algebra_map,
        finsupp.single_of_single_apply],
    },
    case h_grade1 : {
      rw [grades'.map_ι, map_single_apply, grades'.map_ι,
        finsupp.single_of_single_apply],
    },
    case h_add : x y hx hy {
      rw [grades'.map_add, finsupp.add_apply, grades'.map_add, finsupp.single_add, hx, hy],
    },
    case h_mul : f g hx hy {
      rw grades'.map_mul,
      rw add_monoid_algebra.mul_def,
      simp_rw [finsupp.sum_apply],

      -- pull the sums to the outside
      have : finsupp.single i = finsupp.single_add_hom i := rfl,
      rw this,
      simp_rw alg_hom.map_finsupp_sum,
      simp_rw add_monoid_hom.map_finsupp_sum,
      simp_rw finsupp.sum,
      congr, ext1 fi,
      congr, ext1 gi,
      rw ←this,

      -- this proof now resembles the other three
      rw [map_single_apply, grades'.map_mul,
        finsupp.single_of_single_apply],
      rw [hx, hy, add_monoid_algebra.single_mul_single],
    },
  end

end grades'

end clifford_algebra
