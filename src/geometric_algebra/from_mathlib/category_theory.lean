import algebra.category.Algebra.basic
import linear_algebra.clifford_algebra.basic
import geometric_algebra.from_mathlib.basic
import for_mathlib.linear_algebra.quadratic_form.isometric_map

open category_theory
open quadratic_form

/-! # Category-theoretic interpretations of `clifford_algebra`

## Main definitions

* `QuadraticModule R`: the category of quadratic modules
* `CliffordAlgebra`: the functor from quadratic modules to algebras

-/

universes v u

set_option old_structure_cmd true

variables (R : Type u) [comm_ring R]

structure QuadraticModule extends Module.{v} R :=
(form' : quadratic_form R carrier)


variables {R}

namespace QuadraticModule

instance : has_coe_to_sort (QuadraticModule.{v} R) (Type v) := ⟨QuadraticModule.carrier⟩


instance (V : QuadraticModule.{v} R) : add_comm_group V := V.is_add_comm_group
instance (V : QuadraticModule.{v} R) : module R V := V.is_module

def form (V : QuadraticModule.{v} R) : quadratic_form R V := V.form'

instance category : category (QuadraticModule.{v} R) :=
{ hom   := λ M N, M.form.isometric_map N.form,
  id    := λ M, isometric_map.id M.form,
  comp  := λ A B C f g, g.comp f,
  id_comp' := λ X Y f, isometric_map.to_linear_map_injective $ linear_map.id_comp _,
  comp_id' := λ X Y f, isometric_map.to_linear_map_injective $ linear_map.comp_id _,
  assoc' := λ W X Y Z f g h, isometric_map.to_linear_map_injective $ linear_map.comp_assoc _ _ _ }

instance concrete_category : concrete_category.{v} (QuadraticModule.{v} R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_Module : has_forget₂ (QuadraticModule R) (Module R) :=
{ forget₂ :=
  { obj := λ M, Module.of R M,
    map := λ M₁ M₂ f, isometric_map.to_linear_map f } }

instance (M N : QuadraticModule R) : linear_map_class (M ⟶ N) R M N :=
{ coe := λ f, f,
  .. isometric_map.semilinear_map_class }

end QuadraticModule

/-- The "clifford algebra" functor, sending a quadratic R-module V to the clifford algebra on `V`. -/
@[simps]
def CliffordAlgebra : QuadraticModule.{u} R ⥤ Algebra.{u} R :=
{ obj := λ M,
  { carrier := clifford_algebra M.form },
  map := λ M N f, clifford_algebra.map _ _ f.to_linear_map f.map_app,
  map_id' := by { intros X, ext1, simp only [clifford_algebra.map_comp_ι], refl },
  map_comp' := λ M N P f g, begin
    ext1,
    simp only [clifford_algebra.map_comp_ι],
    ext1,
    simp_rw [linear_map.comp_apply, alg_hom.to_linear_map_apply, category_theory.comp_apply,
      clifford_algebra.map_apply_ι, isometric_map.coe_to_linear_map],
    simp only [free_algebra.lift_ι_apply, category_theory.coe_comp, function.comp_app,
      types_comp_apply]
  end }
