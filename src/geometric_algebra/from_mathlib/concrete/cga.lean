import linear_algebra.clifford_algebra
import analysis.inner_product_space.basic
import geometric_algebra.from_mathlib.basic
/-!
# Conformal Geometric algebra

This files defines the conformalized vector space `conformalize V`, and its associated geometric algebra `CGA`.

A typical usage would use `CGA (euclidean_space ℝ 3)`.
-/

-- the real numbers are not computable
noncomputable theory

variables (V : Type*) [inner_product_space ℝ V]

/-! ## The conformalized space `conformalize V` -/
/-- A conformalized vector has additional $n_0$ and $n_\infty$ components -/
@[derive [add_comm_group, module ℝ]]
def conformalize : Type* := V × ℝ × ℝ

namespace conformalize

variables {V}
/-! Linear maps which extract the three components, with `c_` abbreviating
"coefficient of". -/
def v : conformalize V →ₗ[ℝ] V := linear_map.fst _ _ _
def c_n0 : conformalize V →ₗ[ℝ] ℝ := (linear_map.fst _ _ _).comp (linear_map.snd _ _ _)
def c_ni : conformalize V →ₗ[ℝ] ℝ := (linear_map.snd _ _ _).comp (linear_map.snd _ _ _)

/-! The embedding of directions from `V` into `conformalize V`, and the two
basis vectors. -/
def of_v : V →ₗ[ℝ] conformalize V := linear_map.inl _ _ _
def n0 : conformalize V := (0, 1, 0)
def ni : conformalize V := (0, 0, 1)

/-! Lemmas to train the simplifier about trivial compositions of the above. -/
@[simp] lemma v_of_v (x : V) : (of_v x).v = x := rfl
@[simp] lemma c_n0_of_v (x : V) : (of_v x).c_n0 = 0 := rfl
@[simp] lemma c_ni_of_v (x : V) : (of_v x).c_ni = 0 := rfl
@[simp] lemma v_n0 : (n0 : conformalize V).v = 0 := rfl
@[simp] lemma c_n0_n0 : (n0 : conformalize V).c_n0 = 1 := rfl
@[simp] lemma c_ni_n0 : (n0 : conformalize V).c_ni = 0 := rfl
@[simp] lemma v_ni : (ni : conformalize V).v = 0 := rfl
@[simp] lemma c_n0_ni : (ni : conformalize V).c_n0 = 0 := rfl
@[simp] lemma c_ni_ni : (ni : conformalize V).c_ni = 1 := rfl

/-- The embedding of points from `V` to `conformalize V`. -/
def up (x : V) : conformalize V :=
n0 + of_v x + (1 / 2 * ∥x∥^2 : ℝ) • ni

/-! ## The metric on the conformalized space -/

/-- The metric is the metric of V plus an extra term about n0 and ni. -/
def Q : quadratic_form ℝ (conformalize V) :=
(bilin_form_of_real_inner.comp v v).to_quadratic_form - (2 : ℝ) • quadratic_form.lin_mul_lin c_n0 c_ni

/-- Show the definition is what we expect. -/
@[simp] lemma Q_apply (x : conformalize V) : Q x = ∥x.v∥^2 - 2 * (x.c_n0 * x.c_ni) :=
by simp [Q, inner_self_eq_norm_sq_to_K]

@[simp] lemma Q_up (x : V) : Q (up x) = 0 :=
by simp [up, ←mul_assoc]

/-! Train the simplifier how to act on components -/
@[simp] lemma Q_polar_n0_of_v (x : V) : quadratic_form.polar Q n0 (of_v x) = 0 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_n0_n0 : quadratic_form.polar Q n0 (n0 : conformalize V) = 0 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_n0_ni : quadratic_form.polar Q n0 (ni : conformalize V) = -2 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_ni_of_v (x : V) : quadratic_form.polar Q ni (of_v x) = 0 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_ni_ni : quadratic_form.polar Q ni (n0 : conformalize V) = -2 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_ni_n0 : quadratic_form.polar Q ni (ni : conformalize V) = 0 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_of_v_ni (x : V) : quadratic_form.polar Q (of_v x) n0 = 0 :=
by simp [quadratic_form.polar]
@[simp] lemma Q_polar_of_v_n0 (x : V) : quadratic_form.polar Q (of_v x) ni = 0 :=
by simp [quadratic_form.polar]

-- this one is harder than the rest
@[simp] lemma Q_polar_of_v_of_v (x y : V) : quadratic_form.polar Q (of_v x) (of_v y) = 2 * inner x y :=
begin
  rw [quadratic_form.polar, Q_apply],
  suffices : ∥x + y∥ ^ 2 - ∥x∥ ^ 2 - ∥y∥ ^ 2 = 2 * inner x y,
  { simpa using this, },
  simp only [norm_sq_eq_inner, is_R_or_C.re_to_real],
  rw [inner_add_add_self, ←real_inner_comm y x, two_mul],
  abel,
end

/-- The c_n0 and c_ni terms cancel to give the (negated) distance -/
@[simp] lemma Q_polar_up (x y : V) : quadratic_form.polar Q (up x) (up y) = -dist x y ^ 2 :=
begin
  dunfold up,
  simp only [dist_eq_norm, norm_sq_eq_inner, is_R_or_C.re_to_real, inner_sub_sub_self, ←real_inner_comm y x],
  simp [mul_right_comm, two_mul],
  abel
end

/-! ## The geometric algebra over that space -/

variables (V)
/-- Define the Conformal Geometric Algebra over `V` . -/
abbreviation CGA := clifford_algebra (Q : quadratic_form ℝ $ conformalize V)
variables {V}

open clifford_algebra

lemma ι_up_mul_ι_up_add_swap (x y : V) :
  ι Q (up x) * ι Q (up y) + ι Q (up y) * ι Q (up x) = algebra_map _ _ (-dist x y ^ 2) :=
by rw [ι_mul_ι_add_swap, Q_polar_up]

end conformalize
