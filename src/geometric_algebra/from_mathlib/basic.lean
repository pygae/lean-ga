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

/-- TODO: work out what the necessary conditions are here, then make this an instance -/
example : nontrivial (clifford_algebra Q) := sorry

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
  ⟨(ι Q).cod_restrict s.to_submodule h_grade1,
    λ m, subtype.eq $ ι_square_scalar Q m ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of),
  { ext,
    simp [of], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of a),
  exact alg_hom.congr_fun of_id a,
end

/-- two linear maps agree if they agree on 1, `ι v`, and agree on a product if they agree on its parts. -/
@[ext]
def hom_extₗ {N : Type*} [add_comm_monoid N] [semimodule R N] {f g : clifford_algebra Q →ₗ[R] N}
  (h_one : f 1 = g 1)
  (h_mul : ∀ x y, f x = g x → f y = g y → f (x * y) = g (x * y))
  (h_ι : f.comp (ι Q) = g.comp (ι Q)) : f = g :=
linear_map.ext $ λ x, begin
  refine induction _ (linear_map.congr_fun h_ι) h_mul _ x,
  { intros r,
    rw [algebra.algebra_map_eq_smul_one, f.map_smul, g.map_smul, h_one], },
  { intros a b ha hb,
    rw [f.map_add, g.map_add, ha, hb] },
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

/-- A wedge product of n vectors. Note this does not define the wedge product of arbitrary multivectors. -/
def ι_wedge (n : ℕ) [invertible (n.factorial : R)] : alternating_map R M (clifford_algebra Q) (fin n) :=
⅟(n.factorial : R) • ((multilinear_map.mk_pi_algebra_fin R n _).comp_linear_map (λ i, ι Q)).alternatization

end clifford_algebra
