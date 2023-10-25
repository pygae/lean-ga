import linear_algebra.bilinear_form

namespace bilin_form

variables {α β R M : Type*}

section semiring
variables [semiring R] [add_comm_monoid M] [module R M]
variables [monoid α] [monoid β] [distrib_mul_action α R] [distrib_mul_action β R]
variables [smul_comm_class α R R] [smul_comm_class β R R]

instance [smul_comm_class α β R] : smul_comm_class α β (bilin_form R M) :=
⟨λ a b B, ext $ λ x y, smul_comm _ _ _⟩

instance [has_smul α β] [is_scalar_tower α β R] : is_scalar_tower α β (bilin_form R M) :=
⟨λ a b B, ext $ λ x y, smul_assoc _ _ _⟩

end semiring

section comm_semiring
variables [comm_semiring R] [add_comm_monoid M] [module R M]

@[simp]
lemma linear_map.to_bilin_apply (l : M →ₗ[R] M →ₗ[R] R)  (v w : M) : l.to_bilin v w = l v w := rfl

end comm_semiring

end bilin_form