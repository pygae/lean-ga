import for_mathlib.ring_theory.tensor_product
import for_mathlib.algebra.algebra.opposite

/-! # `MulOpposite` commutes with `⊗`

The main result in this file is:

* `algebra.tensor_product.op_alg_equiv : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ ≃ₐ[S] (A ⊗[R] B)ᵐᵒᵖ`
-/

variables {R S A B : Type _}
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra R A] [algebra R B] [algebra S A] [smul_comm_class R S A]
variables [is_scalar_tower R S A]

namespace algebra.tensor_product
open_locale tensor_product

open mul_opposite

variables (S)

/-- `MulOpposite` commutes with `TensorProduct`. -/
def op_alg_equiv : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ ≃ₐ[S] (A ⊗[R] B)ᵐᵒᵖ :=
alg_equiv.of_alg_hom
  (alg_hom_of_linear_map_tensor_product'
    (tensor_product.algebra_tensor_module.congr
          (op_linear_equiv S).symm
          (op_linear_equiv R).symm
        ≪≫ₗ op_linear_equiv S).to_linear_map
    (λ a₁ a₂ b₁ b₂, unop_injective rfl)
    (λ r, unop_injective $ rfl))
  (alg_hom.op_comm $ alg_hom_of_linear_map_tensor_product'
    (show A ⊗[R] B ≃ₗ[S] (Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ)ᵐᵒᵖ, from
      tensor_product.algebra_tensor_module.congr
      (op_linear_equiv S)
      (op_linear_equiv R) ≪≫ₗ op_linear_equiv S).to_linear_map
    (λ a₁ a₂ b₁ b₂, unop_injective $ rfl)
    (λ r, unop_injective $ rfl))
  (alg_hom.op.symm.injective $ by ext; refl)
  (by ext; refl)

lemma op_alg_equiv_apply (x : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ) :
  op_alg_equiv S x =
    op (tensor_product.map
      (op_linear_equiv R).symm.to_linear_map (op_linear_equiv R).symm.to_linear_map x) := rfl

@[simp] lemma op_alg_equiv_tmul (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ) :
  op_alg_equiv S (a ⊗ₜ[R] b) = op (a.unop ⊗ₜ b.unop) := rfl

@[simp] lemma op_alg_equiv_symm_tmul (a : A) (b : B) :
  (op_alg_equiv S).symm (op $ a ⊗ₜ[R] b) = op a ⊗ₜ op b := rfl

end algebra.tensor_product
