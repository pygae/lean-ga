import ring_theory.tensor_product
import linear_algebra.dual

universes u v₁ v₂ v₃ v₄

open_locale tensor_product
open tensor_product

namespace tensor_product

variables {R A M N P Q : Type*}

/-!
### The `A`-module structure on `A ⊗[R] M`
-/

open linear_map
open _root_.algebra (lsmul)

namespace algebra_tensor_module


section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P] [module A P] [is_scalar_tower R A P]
variables [add_comm_monoid Q] [module R Q]

/-- Heterobasic `tensor_product.map`. -/
def map (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[A] P ⊗[R] Q :=
lift $ (show (Q →ₗ[R] P ⊗ Q) →ₗ[A] N →ₗ[R] P ⊗[R] Q,
  from{ to_fun := λ h, h ∘ₗ g,
  map_add' := λ h₁ h₂, linear_map.add_comp g h₂ h₁,
  map_smul' := λ c h, linear_map.smul_comp c h g }) ∘ₗ mk R A P Q ∘ₗ f

@[simp] theorem map_tmul (f : M →ₗ[A] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
  map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

lemma map_add_left (f₁ f₂ : M →ₗ[A] P) (g : N →ₗ[R] Q) : map (f₁ + f₂) g = map f₁ g + map f₂ g :=
begin
  ext,
  simp_rw [curry_apply, tensor_product.curry_apply, restrict_scalars_apply, add_apply, map_tmul,
    add_apply, add_tmul],
end

lemma map_add_right (f : M →ₗ[A] P) (g₁ g₂ : N →ₗ[R] Q) : map f (g₁ + g₂) = map f g₁ + map f g₂ :=
begin
  ext,
  simp_rw [curry_apply, tensor_product.curry_apply, restrict_scalars_apply, add_apply, map_tmul,
    add_apply, tmul_add],
end

lemma map_smul_left (r : A) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map (r • f) g = r • map f g :=
begin
  ext,
  simp_rw [curry_apply, tensor_product.curry_apply, restrict_scalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul'],
end

lemma map_smul_right (r : R) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g :=
begin
  ext,
  simp_rw [curry_apply, tensor_product.curry_apply, restrict_scalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul],
end

/-- Heterobasic `map_bilinear` -/
def map_bilinear : (M →ₗ[A] P) →ₗ[A] (N →ₗ[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
{ to_fun := λ f,
  { to_fun := λ g, map f g,
    map_add' := λ g₁ g₂, map_add_right _ _ _,
    map_smul' := λ c g, map_smul_right _ _ _, },
  map_add' := λ f₁ f₂, linear_map.ext $ λ g, map_add_left _ _ _,
  map_smul' := λ c f, linear_map.ext $ λ g, map_smul_left _ _ _, }

def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M ⊗[R] N) ≃ₗ[A] (P ⊗[R] Q) :=
linear_equiv.of_linear (map f g) (map f.symm g.symm)
  (ext $ λ m n, by simp; simp only [linear_equiv.apply_symm_apply])
  (ext $ λ m n, by simp; simp only [linear_equiv.symm_apply_apply])

@[simp] theorem congr_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
  congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

@[simp] theorem congr_symm_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
  (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
rfl

variables (R A M N P Q)

/- Heterobasic `tensor_product.rid` -/
def rid : A ⊗[R] R ≃ₗ[A] A :=
linear_equiv.of_linear
  (lift $ linear_map.flip $
    (algebra.lsmul A A : A →ₐ[A] _).to_linear_map.flip.restrict_scalars R ∘ₗ algebra.linear_map R A)
  ((mk R A A R).flip 1)
  (ext_ring $ show 1 * algebra_map R A 1 = 1, by simp)
  (ext $ λ x y, show (x * algebra_map R A y) ⊗ₜ[R] 1 = x ⊗ₜ[R] y,
    by rw [←algebra.commutes, ←_root_.algebra.smul_def, smul_tmul, smul_eq_mul, mul_one])
  
lemma rid_apply (a : A) (r : R) : rid R A (a ⊗ₜ r) = a * algebra_map R A r := rfl

/-- A tensor product analogue of `mul_left_comm`. -/
def left_comm : M ⊗[A] (P ⊗[R] Q) ≃ₗ[A] P ⊗[A] (M ⊗[R] Q) :=
let e₁ := (assoc R A M Q P).symm,
    e₂ := congr (tensor_product.comm A M P) (1 : Q ≃ₗ[R] Q),
    e₃ := (assoc R A P Q M) in
e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

open module (dual)

/- Heterobasic `tensor_product.hom_tensor_hom_map` -/
def hom_tensor_hom_map : ((M →ₗ[A] P) ⊗[R] (N →ₗ[R] Q)) →ₗ[A] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
lift map_bilinear

@[simp] lemma hom_tensor_hom_map_apply (f : M →ₗ[A] P) (g : N →ₗ[R] Q) :
  hom_tensor_hom_map R A M N P Q (f ⊗ₜ g) = map f g :=
rfl

/- Heterobasic `tensor_product.dual_distrib` -/
def dual_distrib : (dual A M) ⊗[R] (dual R N) →ₗ[A] dual A (M ⊗[R] N) :=
begin
  refine _ ∘ₗ hom_tensor_hom_map R A M N A R,
  exact comp_right (rid R A),
end

variables {R A M N P Q}

@[simp]
lemma dual_distrib_apply (f : dual A M) (g : dual R N) (m : M) (n : N) :
  dual_distrib R A M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * algebra_map R A (g n) :=
rfl


variables (R A M N P Q)

set_option pp.parens true
notation (name := tensor_product')
  M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N

-- -- assoc R A _ _ _ ≪≫ₗ begin
-- --   sorry
-- -- end
-- linear_equiv.of_linear
--   (lift _)
--   (lift _) _ _
-- let e₁ := (assoc R A M Q P).symm,
--     e₂ := congr (tensor_product.comm A M P) (1 : Q ≃ₗ[R] Q),
--     e₃ := (assoc R A P Q M) in
-- e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

#print tensor_product.assoc
#check curry

/-- Heterobasic version of `tensor_product.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps] def uncurry' : (N →ₗ[R] (Q →ₗ[R] P)) →ₗ[A] ((N ⊗[R] Q) →ₗ[R] P) :=
{ to_fun := lift,
  map_add' := λ f g, ext $ λ x y, by simp only [lift_tmul, add_apply],
  map_smul' := λ c f, ext $ λ x y, by simp only [lift_tmul, smul_apply, ring_hom.id_apply] }

/-- Heterobasic version of `tensor_product.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps] def lcurry' : ((N ⊗[R] Q) →ₗ[R] P) →ₗ[A] (N →ₗ[R] (Q →ₗ[R] P)) :=
{ to_fun := curry,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

/-- Heterobasic version of `tensor_product.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def assoc' : ((M ⊗[R] N) ⊗[R] Q) ≃ₗ[A] (M ⊗[R] (N ⊗[R] Q)) :=
linear_equiv.of_linear
    (lift $ lift $ lcurry' R A N _ Q ∘ₗ mk R A M (N ⊗[R] Q))  --  (lcurry R _ _ _ _)
    (lift $ (uncurry' R _ _ _ _) ∘ₗ (curry $ mk R A (M ⊗[R] N) Q))
    (curry_injective $ linear_map.ext $ λ m,
      curry_injective $ linear_map.ext $ λ n, linear_map.ext $ λ q,
        by exact eq.refl (m ⊗ₜ[R] (n ⊗ₜ[R] q)))
    (curry_injective $ ext $ λ m n, linear_map.ext $ λ q,
      by exact eq.refl ((m ⊗ₜ[R] n) ⊗ₜ[R] q))
.
instance : is_scalar_tower R A (P →ₗ[A] ((M ⊗[A] P) ⊗[R] Q)) := linear_map.is_scalar_tower
instance : linear_map.compatible_smul
    ((M ⊗[A] P) →ₗ[A] ((M ⊗[A] P) ⊗[R] Q))
    (M →ₗ[A] (P →ₗ[A] ((M ⊗[A] P) ⊗[R] Q)))
    R
    A := is_scalar_tower.compatible_smul

-- /-- A tensor product analogue of `mul_left_comm`. -/
def right_comm : (M ⊗[A] P) ⊗[R] Q ≃ₗ[A] (M ⊗[R] Q) ⊗[A] P :=
begin
  refine linear_equiv.of_linear
    (lift $ lift $ flip $ lcurry R A M Q _ ∘ₗ (mk A A (M ⊗[R] Q) P).flip)
    (lift $ lift $ flip $
      (tensor_product.lcurry A M P ((M ⊗[A] P) ⊗[R] Q)).restrict_scalars R
        ∘ₗ (mk R A (M ⊗[A] P) Q).flip)
    (curry_injective _)
    (curry_injective _),
  sorry,
  sorry,
end

/-- Heterobasic version of `tensor_tensor_tensor_comm`:



Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def tensor_tensor_tensor_comm :
  (M ⊗[R] N) ⊗[A] (P ⊗[R] Q) ≃ₗ[A] (M ⊗[A] P) ⊗[R] (N ⊗[R] Q) :=
(assoc R A _ _ _).symm ≪≫ₗ congr (right_comm R A _ _ _).symm 1 ≪≫ₗ assoc' R A _ _ _

@[simp] lemma tensor_tensor_tensor_comm_apply (m : M) (n : N) (p : P) (q : Q) :
  tensor_tensor_tensor_comm R A M N P Q ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q) :=
rfl

end comm_semiring

end algebra_tensor_module

end tensor_product
