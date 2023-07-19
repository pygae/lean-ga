import linear_algebra.quadratic_form.isometry

/-! # Isometric linear maps

Note that `quadratic_form.isometry` is already taken for isometric equivalences.
-/
set_option old_structure_cmd true

variables {ι R M M₁ M₂ M₃ : Type*}

namespace quadratic_form

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₁] [module R M₂] [module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_nonempty_instance] structure isometric_map
  (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) extends M₁ →ₗ[R] M₂ :=
(map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m)

namespace isometric_map

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

instance : semilinear_map_class (Q₁.isometric_map Q₂) (ring_hom.id R) M₁ M₂ :=
{ coe := λ f, f.to_linear_map,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := λ f, f.to_linear_map.map_add,
  map_smulₛₗ := λ f, f.to_linear_map.map_smul }

lemma to_linear_map_injective :
  function.injective (isometric_map.to_linear_map : (Q₁.isometric_map Q₂) → (M₁ →ₗ[R] M₂)) :=
λ f g h, fun_like.coe_injective (congr_arg fun_like.coe h : _)

@[ext] lemma ext ⦃f g : Q₁.isometric_map Q₂⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- See Note [custom simps projection]. -/
protected def simps.apply (f : Q₁.isometric_map Q₂) : M₁ → M₂ := f

initialize_simps_projections isometric_map (to_fun → apply)

@[simp] lemma map_app (f : Q₁.isometric_map Q₂) (m : M₁) : Q₂ (f m) = Q₁ m := f.map_app' m

@[simp] lemma coe_to_linear_map (f : Q₁.isometric_map Q₂) : ⇑f.to_linear_map = f := rfl

/-- The identity isometry from a quadratic form to itself. -/
@[simps]
def id (Q : quadratic_form R M) : Q.isometric_map Q :=
{ map_app' := λ m, rfl,
  .. linear_map.id  }

/-- The composition of two isometries between quadratic forms. -/
@[simps]
def comp (g : Q₂.isometric_map Q₃) (f : Q₁.isometric_map Q₂) : Q₁.isometric_map Q₃ :=
{ to_fun := λ x, g (f x),
  map_app' := by { intro m, rw [← f.map_app, ← g.map_app] },
  .. (g.to_linear_map : M₂ →ₗ[R] M₃).comp (f.to_linear_map : M₁ →ₗ[R] M₂) }

@[simp] lemma to_linear_map_comp (g : Q₂.isometric_map Q₃) (f : Q₁.isometric_map Q₂) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

/-- Isometries are isometric maps -/
@[simps]
def _root_.quadratic_form.isometry.to_isometric_map (g : Q₁.isometry Q₂) :
  Q₁.isometric_map Q₂ := { ..g }

/-- There is a zero map from any module with the zero form. -/
instance : has_zero ((0 : quadratic_form R M₁).isometric_map Q₂) :=
{ zero :=
  { map_app' := λ m, map_zero _,
    ..(0 : M₁ →ₗ[R] M₂) } }

/-- There is a zero map from the trivial module. -/
instance [subsingleton M₁] : has_zero (Q₁.isometric_map Q₂) :=
{ zero :=
  { map_app' := λ m, subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm,
    ..(0 : M₁ →ₗ[R] M₂) } }

/-- Maps into the zero module are trivial -/
instance [subsingleton M₂] : subsingleton (Q₁.isometric_map Q₂) :=
⟨λ f g, ext $ λ _, subsingleton.elim _ _⟩

end isometric_map

end quadratic_form
