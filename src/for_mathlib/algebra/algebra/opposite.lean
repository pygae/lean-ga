
import algebra.algebra.equiv
import algebra.module.opposites
import algebra.ring.opposite

/-!
# Algebra structures on the multiplicative opposite
-/

variables {R S A B : Type _}
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra R A] [algebra R B] [algebra S A] [smul_comm_class R S A]
variables [is_scalar_tower R S A]

open mul_opposite

namespace alg_hom

/-- An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def from_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) : Aᵐᵒᵖ →ₐ[R] B :=
{ to_fun := f ∘ unop, 
  commutes' := λ r, f.commutes r,
  .. f.to_ring_hom.from_opposite hf }

@[simp] lemma to_linear_map_from_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) :
  (f.from_opposite hf).to_linear_map = f.to_linear_map ∘ₗ (op_linear_equiv R).symm.to_linear_map :=
rfl

@[simp] lemma to_ring_hom_from_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) :
  (f.from_opposite hf).to_ring_hom = f.to_ring_hom.from_opposite hf :=
rfl

/-- An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def to_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) : A →ₐ[R] Bᵐᵒᵖ :=
{ to_fun := op ∘ f, 
  commutes' := λ r, unop_injective $ f.commutes r,
  .. f.to_ring_hom.to_opposite hf }

@[simp] lemma to_linear_map_to_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) :
  (f.to_opposite hf).to_linear_map = (op_linear_equiv R).to_linear_map ∘ₗ f.to_linear_map := rfl

@[simp] lemma to_ring_hom_to_opposite (f : A →ₐ[R] B) (hf : ∀ x y, commute (f x) (f y)) :
  (f.to_opposite hf).to_ring_hom = f.to_ring_hom.to_opposite hf :=
rfl

/-- An algebra hom `A →ₐ[R] B` can equivalently be viewed as an algebra hom `αᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
protected def op : (A →ₐ[R] B) ≃ (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) :=
{ to_fun := λ f,
  { commutes' := λ r, unop_injective $ f.commutes r,
    ..f.to_ring_hom.op },
  inv_fun := λ f,
  { commutes' := λ r, op_injective $ f.commutes r,
    ..f.to_ring_hom.unop},
  left_inv := λ f, alg_hom.ext $ λ a, rfl,
  right_inv := λ f, alg_hom.ext $ λ a, rfl }

/-- The 'unopposite' of an algebra hom `αᵐᵒᵖ →+* Bᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp]
protected def unop : (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) ≃ (A →ₐ[R] B) := alg_hom.op.symm

end alg_hom

/-- An algebra iso `A ≃ₐ[R] B` can equivalently be viewed as an algebra iso `αᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def alg_equiv.op : (A ≃ₐ[R] B) ≃ (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) :=
{ to_fun := λ f,
  { commutes' := λ r, mul_opposite.unop_injective $ f.commutes r,
    ..f.to_ring_equiv.op },
  inv_fun := λ f,
  { commutes' := λ r, mul_opposite.op_injective $ f.commutes r,
    ..f.to_ring_equiv.unop},
  left_inv := λ f, alg_equiv.ext $ λ a, rfl,
  right_inv := λ f, alg_equiv.ext $ λ a, rfl }

/-- The double opposite is isomorphic as an algebra to the original type. -/
@[simps]
def mul_opposite.op_op_alg_equiv : Aᵐᵒᵖᵐᵒᵖ ≃ₐ[R] A :=
alg_equiv.of_linear_equiv
  ((mul_opposite.op_linear_equiv _).trans (mul_opposite.op_linear_equiv _)).symm
  (λ x y, rfl)
  (λ r, rfl)

@[simps]
def alg_hom.op_comm : (A →ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ →ₐ[R] B) :=
(mul_opposite.op_op_alg_equiv.symm.arrow_congr alg_equiv.refl).trans alg_hom.op.symm
