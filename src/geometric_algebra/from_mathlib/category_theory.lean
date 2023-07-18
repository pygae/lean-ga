import algebra.category.Algebra.basic
import linear_algebra.clifford_algebra.basic
import geometric_algebra.from_mathlib.basic
import for_mathlib.linear_algebra.quadratic_form.isometric_map

/-! # Category-theoretic interpretations of `clifford_algebra`

## Main definitions

* `QuadraticModule R`: the category of quadratic modules
* `CliffordAlgebra`: the functor from quadratic modules to algebras
* `clifford_algebra.is_initial`: the clifford algebra is initial in the category of pairs
  `(A, clifford_hom Q A)`.

-/

open category_theory
open quadratic_form
open clifford_algebra

universes v u w

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
.

variables {M : Type w} [add_comm_group M] [module R M] (Q : quadratic_form R M)

/--
The category of pairs of algebras and `clifford_hom`s to those algebras.

https://empg.maths.ed.ac.uk/Activities/Spin/Lecture1.pdf
-/
structure Cliff :=
(alg : Algebra.{v} R)
(hom : clifford_hom Q alg)

namespace Cliff

/-- Convert a `clifford_hom Q A` to an element of `Cliff Q`. -/
def of {A : Type v} [ring A] [algebra R A] (f : clifford_hom Q A) : Cliff.{v} Q :=
{ alg := Algebra.of R A, hom := f } 

instance : category (Cliff Q) :=
{ hom := λ f g, {h : f.alg ⟶ g.alg // (alg_hom.to_linear_map h).comp f.hom.val = g.hom.val },
  id := λ f, ⟨𝟙 _, linear_map.ext $ λ _, rfl⟩,
  comp := λ x y z f g, ⟨f.val ≫ g.val,
    by simp only [category_struct.comp, alg_hom.comp_to_linear_map, linear_map.comp_assoc,
      f.property, g.property]⟩,
  id_comp' := λ x y f, subtype.ext $ category.id_comp f,
  comp_id' := λ x y f, subtype.ext $ category.comp_id f,
  assoc' := λ w x y z f g h, subtype.ext $ category.assoc f g h }

instance concrete_category : concrete_category.{v} (Cliff.{v} Q) :=
{ forget := { obj := λ x, x.alg, map := λ x y f, (forget _).map (subtype.val f : _) },
  forget_faithful := { } }

instance has_forget_to_Algebra : has_forget₂ (Cliff Q) (Algebra R) :=
{ forget₂ :=
  { obj := λ x, x.alg,
    map := λ x y f, f.val } }

instance (Y : Cliff Q) : unique (Cliff.of Q ⟨ι Q, ι_sq_scalar Q⟩ ⟶ Y) :=
{ default := ⟨clifford_algebra.lift Q Y.hom, let ⟨A, ι, hι⟩ := Y in ι_comp_lift ι hι⟩,
  uniq := λ f, subtype.ext begin
    obtain ⟨A, ι, hι⟩ := Y,
    exact (clifford_algebra.lift_unique _ hι f.val).mp f.prop,
  end }

end Cliff

/-- The clifford algebra is the initial obect in in `Cliff`. -/
def clifford_algebra.is_initial : limits.is_initial (Cliff.of Q ⟨ι Q, ι_sq_scalar Q⟩) :=
limits.is_initial.of_unique _
