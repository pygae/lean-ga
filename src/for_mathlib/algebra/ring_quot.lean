import algebra.ring_quot

variables {S R A : Type*} [comm_semiring S] [comm_semiring R] [semiring A] [algebra S A]
  [algebra R A] (r : A → A → Prop)

instance [has_smul R S] [is_scalar_tower R S A] : is_scalar_tower R S (ring_quot r) :=
⟨λ r s ⟨a⟩, quot.induction_on a $ λ a',
  by simpa only [ring_quot.smul_quot] using congr_arg (quot.mk _) (smul_assoc r s a' : _)⟩

instance [smul_comm_class R S A] : smul_comm_class R S (ring_quot r) :=
⟨λ r s ⟨a⟩, quot.induction_on a $ λ a',
  by simpa only [ring_quot.smul_quot] using congr_arg (quot.mk _) (smul_comm r s a' : _)⟩
