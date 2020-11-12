/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra
import missing_from_mathlib

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

notation `↑ₐ`:max x:max := algebra_map _ _ x

namespace clifford_algebra

-- if this fails then you have the wrong branch of mathlib
example : ring (clifford_algebra Q) := infer_instance

variables (Q)
abbreviation clifford_hom (A : Type*) [semiring A] [algebra R A] :=
{ f : M →ₗ[R] A // ∀ m, f m * f m = ↑ₐ(Q m) }
variables {Q}

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
  let of : clifford_hom Q s :=
  ⟨{
    to_fun := λ x, ⟨(ι Q) x, h_grade1 x⟩,
    map_add' := λ x y, subtype.eq $ (ι Q).map_add x y,
    map_smul' := λ c x, subtype.eq $ (ι Q).map_smul c x, },
    λ m, subtype.eq $ ι_square_scalar Q m ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of),
  { ext,
    simp [of, subtype.coind], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of a),
  simp [alg_hom.ext_iff] at of_id,
  exact of_id a,
end

/-- symmetric product of vectors is a scalar -/
lemma vec_symm_prod (a b : M) : ι Q a * ι Q b + ι Q b * ι Q a = ↑ₐ(quadratic_form.polar Q a b) :=
calc ι Q a * ι Q b + ι Q b * ι Q a
      = ι Q (a + b) * ι Q (a + b) - ι Q a * ι Q a - ι Q b * ι Q b :
          by { rw [(ι Q).map_add, mul_add, add_mul, add_mul], abel, }
  ... = ↑ₐ(Q $ a + b) - ↑ₐ(Q a) - ↑ₐ(Q b) :
          by rw [ι_square_scalar, ι_square_scalar, ι_square_scalar]
  ... = ↑ₐ(Q (a + b) - Q a - Q b) :
          by rw [←ring_hom.map_sub, ←ring_hom.map_sub]
  ... = ↑ₐ(quadratic_form.polar Q a b) : rfl

end clifford_algebra
