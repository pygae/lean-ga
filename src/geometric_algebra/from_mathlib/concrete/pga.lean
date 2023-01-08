import linear_algebra.clifford_algebra
import data.matrix.notation
import data.real.basic
import analysis.inner_product_space.basic
import for_mathlib.analysis.inner_product_space.basic
/-!
# Plane-based Geometric algebra

This files defines the projectivized vector space `projectivize V`, and its associated geometric algebra `CGA`.

A typical usage would use `PGA (euclidean_space ℝ 3)`.

This file is underdeveloped compared to one for `conformalize`, but is included as a skeleton of how to proceed.
-/

-- the real numbers are not computable
noncomputable theory

variables (V : Type*) [inner_product_space ℝ V]

/-- A projectivized vector has additional e0 component -/
@[derive [add_comm_group, module ℝ]]
def projectivize : Type* := V × ℝ

namespace projectivize

variables {V}
/-! Define linear maps to extract the new components -/
def v : projectivize V →ₗ[ℝ] V := linear_map.fst _ _ _
def c_n0 : projectivize V →ₗ[ℝ] ℝ := linear_map.snd _ _ _

/-! The metric is the metric of V with the n0 term ignored. -/
def Q : quadratic_form ℝ (projectivize V) :=
(bilin_form_of_real_inner.comp v v).to_quadratic_form

/-- Show the definition is what we expect. -/
@[simp] lemma Q_apply (x : projectivize V) : Q x = ‖x.v‖^2 :=
by simp [Q, inner_self_eq_norm_sq_to_K]

variables (V)
/-- Define the Plane-based Geometric Algebra over V. -/
abbreviation PGA := clifford_algebra (Q : quadratic_form ℝ $ projectivize V)

/-- And the embedding of the vector space into it.
Note that often the dual of this result is used instead, but we do not have that in our
formalization yet! -/
def up (x : V) : PGA V :=
clifford_algebra.ι _ (x, 1)

end projectivize
