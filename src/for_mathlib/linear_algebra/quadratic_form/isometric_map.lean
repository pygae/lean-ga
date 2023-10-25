import linear_algebra.quadratic_form.isometry

/-! # Isometric (semi)linear maps

Note that `quadratic_form.isometry` is already taken for isometric equivalences.
-/
set_option old_structure_cmd true

variables {ι R R₁ R₂ R₃ R₄ M₁ M₂ M₃ M₄ : Type*}

namespace quadratic_form

section semilinear

variables [semiring R₁] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [module R₁ M₁] [module R₂ M₂] [module R₃ M₃] [module R₄ M₄]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_nonempty_instance] structure isometric_map (σ : R₁ →+* R₂)
  (Q₁ : quadratic_form R₁ M₁) (Q₂ : quadratic_form R₂ M₂) extends M₁ →ₛₗ[σ] M₂ :=
(map_app' : ∀ m, Q₂ (to_fun m) = σ (Q₁ m))


notation Q₁ ` →qₛₗ[`:25 σ:25 `] `:0 Q₂:0 := isometric_map σ Q₁ Q₂
notation Q₁ ` →qᵢ `:25 Q₂:0 := isometric_map (ring_hom.id _) Q₁ Q₂

namespace isometric_map


variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₃₄ : R₃ →+* R₄}
variables {σ₁₃ : R₁ →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
variables {Q₁ : quadratic_form R₁ M₁} {Q₂ : quadratic_form R₂ M₂}
variables {Q₃ : quadratic_form R₃ M₃} {Q₄ : quadratic_form R₄ M₄}

instance : semilinear_map_class (Q₁ →qₛₗ[σ₁₂] Q₂) σ₁₂ M₁ M₂ :=
{ coe := λ f, f.to_linear_map,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := λ f, f.to_linear_map.map_add,
  map_smulₛₗ := λ f, f.to_linear_map.map_smulₛₗ }

lemma to_linear_map_injective :
  function.injective (isometric_map.to_linear_map : (Q₁ →qₛₗ[σ₁₂] Q₂) → (M₁ →ₛₗ[σ₁₂] M₂)) :=
λ f g h, fun_like.coe_injective (congr_arg fun_like.coe h : _)

@[ext] lemma ext ⦃f g : Q₁ →qₛₗ[σ₁₂] Q₂⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- See Note [custom simps projection]. -/
protected def simps.apply (f : Q₁ →qₛₗ[σ₁₂] Q₂) : M₁ → M₂ := f

initialize_simps_projections isometric_map (to_fun → apply)

@[simp] lemma map_appₛₗ (f : Q₁ →qₛₗ[σ₁₂] Q₂) (m : M₁) : Q₂ (f m) = σ₁₂ (Q₁ m) := f.map_app' m

@[simp] lemma coe_to_linear_map (f : Q₁ →qₛₗ[σ₁₂] Q₂) : ⇑f.to_linear_map = f := rfl

/-- The identity isometry from a quadratic form to itself. -/
@[simps]
def id (Q : quadratic_form R₁ M₁) : Q →qᵢ Q :=
{ map_app' := λ m, rfl,
  .. linear_map.id  }

/-- The composition of two isometries between quadratic forms. -/
@[simps]
def comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] (g : Q₂ →qₛₗ[σ₂₃] Q₃) (f : Q₁ →qₛₗ[σ₁₂] Q₂) : Q₁ →qₛₗ[σ₁₃] Q₃ :=
{ to_fun := λ x, g (f x),
  map_app' := λ m,
    by rw [←@ring_hom_comp_triple.comp_apply _ _ _ _ _ _ σ₁₂ σ₂₃ σ₁₃, ← f.map_appₛₗ, ← g.map_appₛₗ],
  .. (g.to_linear_map : M₂ →ₛₗ[σ₂₃] M₃).comp (f.to_linear_map : M₁ →ₛₗ[σ₁₂] M₂) }

@[simp] lemma to_linear_map_comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] (g : Q₂ →qₛₗ[σ₂₃] Q₃) (f : Q₁ →qₛₗ[σ₁₂] Q₂) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma id_comp (f : Q₁ →qₛₗ[σ₁₂] Q₂) : (id Q₂).comp f = f := ext $ λ _, rfl
@[simp] lemma comp_id (f : Q₁ →qₛₗ[σ₁₂] Q₂) : f.comp (id Q₁) = f := ext $ λ _, rfl
lemma comp_assoc
  [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₂₃ σ₃₄ σ₂₄]
  [ring_hom_comp_triple σ₁₂ σ₂₄ σ₁₄] [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄]
  (h : Q₃ →qₛₗ[σ₃₄] Q₄) (g : Q₂ →qₛₗ[σ₂₃] Q₃) (f : Q₁ →qₛₗ[σ₁₂] Q₂) :
  (h.comp g).comp f = h.comp (g.comp f) := ext $ λ _, rfl

/-- There is a zero map from any module with the zero form. -/
instance : has_zero ((0 : quadratic_form R₁ M₁) →qₛₗ[σ₁₂] Q₂) :=
{ zero :=
  { map_app' := λ m, (map_zero _).trans (_root_.map_zero _).symm,
    ..(0 : M₁ →ₛₗ[σ₁₂] M₂) } }

/-- There is a zero map from the trivial module. -/
instance has_zero_of_subsingleton [subsingleton M₁] : has_zero (Q₁ →qₛₗ[σ₁₂] Q₂) :=
{ zero :=
  { map_app' := λ m, subsingleton.elim 0 m ▸ (map_zero _).trans $
    (_root_.map_zero σ₁₂).symm.trans $ σ₁₂.congr_arg (map_zero _).symm,
    ..(0 : M₁ →ₛₗ[σ₁₂] M₂) } }

/-- Maps into the zero module are trivial -/
instance [subsingleton M₂] : subsingleton (Q₁ →qₛₗ[σ₁₂] Q₂) :=
⟨λ f g, ext $ λ _, subsingleton.elim _ _⟩

end isometric_map

end semilinear

section linear

namespace isometric_map

variables [semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [module R M₁] [module R M₂] [module R M₃] [module R M₄]

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂}

/-- Isometries are isometric maps -/
@[simps]
def _root_.quadratic_form.isometry.to_isometric_map (g : Q₁.isometry Q₂) :
  Q₁ →qᵢ Q₂ := { ..g }

@[simp] lemma map_app (f : Q₁ →qᵢ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m := f.map_app' m

end isometric_map

end linear

end quadratic_form
