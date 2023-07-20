import linear_algebra.clifford_algebra.basic
import data.complex.module
import ring_theory.tensor_product
import for_mathlib.linear_algebra.bilinear_form.tensor_product

variables {V: Type*} [add_comm_group V] [module ℝ V]
.

open_locale tensor_product

#check bilin_form.tmul

def quadratic_form.complexify (Q : quadratic_form ℝ V) :
  quadratic_form ℂ (ℂ ⊗[ℝ] V) :=
{ to_fun := ,
  to_fun_smul := _,
  exists_companion' := _ }
-- bilin_form.to_quadratic_form $
--   (bilin_form.tmul _ Q.associated)