import linear_algebra.tensor_product

section semiring
variables {R : Type*} [comm_semiring R]
variables {R' : Type*} [monoid R']
variables {R'' : Type*} [semiring R'']
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
  [add_comm_monoid S]
variables [module R M] [module R N] [module R P] [module R Q] [module R S]
variables [distrib_mul_action R' M]
variables [module R'' M]
include R

variables {R'₂ : Type*} [monoid R'₂] [distrib_mul_action R'₂ M]
variables [smul_comm_class R R'₂ M]


open_locale tensor_product

variables [smul_comm_class R R' M]
variables [smul_comm_class R R'' M]

namespace tensor_product

/-- `smul_comm_class R' R'₂ M` implies `smul_comm_class R' R'₂ (M ⊗[R] N)` -/
instance smul_comm_class_left [smul_comm_class R' R'₂ M] : smul_comm_class R' R'₂ (M ⊗[R] N) :=
{ smul_comm := λ r' r'₂ x, tensor_product.induction_on x
    (by simp_rw tensor_product.smul_zero)
    (λ m n, by simp_rw [smul_tmul', smul_comm])
    (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy] }) }

end tensor_product

end semiring