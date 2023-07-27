import algebra.category.Algebra.basic
import linear_algebra.clifford_algebra.basic
import geometric_algebra.from_mathlib.basic
import for_mathlib.linear_algebra.quadratic_form.isometric_map

/-! # Category-theoretic interpretations of `clifford_algebra`

## Main definitions

* `QuadraticModule R`: the category of quadratic modules
* `CliffordAlgebra`: the functor from quadratic modules to algebras
* `Cliff.is_initial_clifford_algebra`: the clifford algebra is initial in the category of pairs
  `(A, clifford_hom Q A)`.

-/

open category_theory
open quadratic_form
open clifford_algebra

instance _root_.alg_hom.has_zero_of_subsingleton (R A B : Type*)
  [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B] [subsingleton A] :
  has_zero (B →ₐ[R] A) :=
{ zero :=
  { to_fun := 0,
    map_one' := subsingleton.elim _ _,
    map_mul' := λ _ _, subsingleton.elim _ _,
    commutes' := λ _, subsingleton.elim _ _,
    ..(0 : B →+ A) } }

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
{ hom      := λ M N, M.form →qᵢ N.form,
  id       := λ M, isometric_map.id M.form,
  comp     := λ A B C f g, g.comp f,
  id_comp' := λ X Y, isometric_map.id_comp,
  comp_id' := λ X Y, isometric_map.comp_id,
  assoc'   := λ W X Y Z f g h, isometric_map.comp_assoc h g f }

lemma comp_def {M N U : QuadraticModule.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
  f ≫ g = g.comp f := rfl

instance concrete_category : concrete_category.{v} (QuadraticModule.{v} R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_Module : has_forget₂ (QuadraticModule R) (Module R) :=
{ forget₂ :=
  { obj := λ M, Module.of R M,
    map := λ M₁ M₂, isometric_map.to_linear_map } }

instance (M N : QuadraticModule R) : linear_map_class (M ⟶ N) R M N :=
{ coe := λ f, f,
  .. isometric_map.semilinear_map_class }

end QuadraticModule

/-- The "clifford algebra" functor, sending a quadratic `R`-module `V` to the clifford algebra on
`V`.

This is `clifford_algebra.map` through the lens of category theory. -/
@[simps]
def CliffordAlgebra : QuadraticModule.{u} R ⥤ Algebra.{u} R :=
{ obj := λ M,
  { carrier := clifford_algebra M.form },
  map := λ M N f, clifford_algebra.map _ _ f.to_linear_map f.map_app,
  map_id' := λ X, clifford_algebra.map_id _,
  map_comp' := λ M N P f g, (clifford_algebra.map_comp_map _ _ _ _ _ _ _).symm }

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

/-- `clifford_algebra Q` as an element of `Cliff Q` -/
@[reducible] protected def clifford_algebra : Cliff Q := Cliff.of Q ⟨ι Q, ι_sq_scalar Q⟩

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

instance unique_from (Y : Cliff Q) : unique (Cliff.clifford_algebra Q ⟶ Y) :=
{ default := ⟨clifford_algebra.lift Q Y.hom, let ⟨A, ι, hι⟩ := Y in ι_comp_lift ι hι⟩,
  uniq := λ f, subtype.ext begin
    obtain ⟨A, ι, hι⟩ := Y,
    exact (clifford_algebra.lift_unique _ hι f.val).mp f.prop,
  end }

instance unique_to (X : Cliff Q) {A : Type v} [ring A] [algebra R A] [subsingleton A]
  (f : clifford_hom Q A):
  unique (X ⟶ Cliff.of Q f) :=
{ default := ⟨(0 : X.alg →ₐ[R] A), linear_map.ext $ λ x, @subsingleton.elim A _ _ _⟩,
  uniq := λ f, subtype.ext $ alg_hom.ext (λ x, @subsingleton.elim A _ _ _) }

/-- The clifford algebra is the initial object in `Cliff`. -/
def is_initial_clifford_algebra : limits.is_initial (Cliff.clifford_algebra Q) :=
limits.is_initial.of_unique _

/-- A trivial algebra is a terminal object in `Cliff`. -/
def is_terminal_of_subsingleton
  {A : Type v} [ring A] [algebra R A] [subsingleton A] :
  limits.is_terminal (Cliff.of Q (0 : clifford_hom _ A)) :=
limits.is_terminal.of_unique _

end Cliff
