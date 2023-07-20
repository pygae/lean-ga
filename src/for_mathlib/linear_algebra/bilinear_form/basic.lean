import linear_algebra.bilinear_form

namespace bilin_form

variables {α β R M : Type*}
variables [semiring R] [add_comm_monoid M] [module R M]
variables [monoid α] [monoid β] [distrib_mul_action α R] [distrib_mul_action β R]
variables [smul_comm_class α R R] [smul_comm_class β R R]

instance [smul_comm_class α β R] : smul_comm_class α β (bilin_form R M) :=
⟨λ a b B, ext $ λ x y, smul_comm _ _ _⟩

instance [has_smul α β] [is_scalar_tower α β R] : is_scalar_tower α β (bilin_form R M) :=
⟨λ a b B, ext $ λ x y, smul_assoc _ _ _⟩

end bilin_form