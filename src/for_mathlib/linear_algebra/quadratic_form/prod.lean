import linear_algebra.quadratic_form.prod
import for_mathlib.linear_algebra.quadratic_form.isometric_map

/-! # Extra results using `isometric_map` about `quadratic_form`s on product types -/

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ N₁ N₂ : Type*} {Mᵢ Nᵢ : ι → Type*}
variables [semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid N₁] [add_comm_monoid N₂]
variables [module R M₁] [module R M₂] [module R N₁] [module R N₂]
variables [Π i, add_comm_monoid (Mᵢ i)] [Π i, add_comm_monoid (Nᵢ i)]
variables [Π i, module R (Mᵢ i)] [Π i, module R (Nᵢ i)]

open_locale big_operators

namespace quadratic_form

namespace isometric_map

section prod
variables [fintype ι] (QM₁ : quadratic_form R M₁) (QM₂ : quadratic_form R M₂)
variables (QN₁ : quadratic_form R N₁) (QN₂ : quadratic_form R N₂)

/-- `linear_map.inl` as an `isometric_map`. -/
@[simps] def inl [decidable_eq ι] (i : ι) : QM₁ →qᵢ QM₁.prod QM₂  :=
{ map_app' := λ x, by simp,
  .. linear_map.inl R M₁ M₂ }

/-- `linear_map.inl` as an `isometric_map`. -/
@[simps] def inr [decidable_eq ι] (i : ι) : QM₂ →qᵢ QM₁.prod QM₂  :=
{ map_app' := λ x, by simp,
  .. linear_map.inr R M₁ M₂ }

variables {QM₁ QM₂ QN₁ QN₂}

/-- `pi.prod` of two isometric maps. -/
@[simps]
def prod {fQM₁ gQM₁ : quadratic_form R M₁}
  (f : fQM₁ →qᵢ QN₁) (g : gQM₁ →qᵢ QN₂) :
  (fQM₁ + gQM₁) →qᵢ QN₁.prod QN₂ :=
{ to_fun := pi.prod f g,
  map_app' := λ x, congr_arg2 (+) (f.map_app _) (g.map_app _),
  .. linear_map.prod f.to_linear_map g.to_linear_map }

/-- `prod.map` of two isometric maps. -/
@[simps]
def prod_map (f : QM₁ →qᵢ QN₁) (g : QM₂ →qᵢ QN₂) :
  QM₁.prod QM₂ →qᵢ QN₁.prod QN₂ :=
{ map_app' := λ x, congr_arg2 (+) (f.map_app _) (g.map_app _),
  .. linear_map.prod_map f.to_linear_map g.to_linear_map }

end prod

section pi
variables [fintype ι] (QM₁ : ι → quadratic_form R M₁) (QMᵢ : Π i, quadratic_form R (Mᵢ i))

/-- `linear_map.single` as an `isometric_map`. -/
@[simps]
def single [decidable_eq ι] (i : ι) : QMᵢ i →qᵢ quadratic_form.pi QMᵢ :=
{ to_fun := pi.single i,
  map_app' := λ x, (pi_apply QMᵢ _).trans $ begin
    rw ring_hom.id_apply,
    refine (fintype.sum_eq_single i $ λ j hij, _).trans _,
    { rw [pi.single_eq_of_ne hij, map_zero] },
    { rw [pi.single_eq_same] }
  end,
  .. (linear_map.single i : Mᵢ i →ₗ[R] (Π i, Mᵢ i))}

/-- `linear_map.pi` for `isometric_map`. -/
def pi (f : Π i, QM₁ i →qᵢ QMᵢ i) :
  (∑ i, QM₁ i) →qᵢ quadratic_form.pi QMᵢ :=
{ to_fun := λ c i, f i c,
  map_app' := λ c, (pi_apply QMᵢ _).trans $
    by simp_rw [λ i, (f i).map_app, sum_apply, ring_hom.id_apply],
  .. linear_map.pi (λ i, (f i).to_linear_map) }

end pi

end isometric_map

end quadratic_form