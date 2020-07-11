import geometric_algebra.nursery.chisolm

namespace geometric_algebra

section r_blades

parameters
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

namespace Bᵣ
  variables {r : ℕ}

  lemma all_G₀_is_rblade0 (k : G₀) : is_rblade 0 (fₛ k) := begin
    use [k, list.pairwise.nil],
    unfold vector.nil subtype.val list.map,
    rw list.prod_nil,
    simp,
  end
  lemma all_G₁_is_rblade1 (a : G₁) : is_rblade 1 (fᵥ a) := begin
    use 1,
    use ⟨(vector.cons a vector.nil), list.pairwise_singleton _ a⟩,
    unfold vector.cons vector.nil subtype.val list.map,
    rw [list.prod_cons, list.prod_nil],
    simp,
  end

  instance has_coe_from_G₀ : has_coe G₀ (Bᵣ 0) := { coe := λ k, ⟨fₛ k, all_G₀_is_rblade0 k⟩}
  instance has_coe_from_G₁ : has_coe G₁ (Bᵣ 1) := { coe := λ a, ⟨fᵥ a, all_G₁_is_rblade1 a⟩}

  -- these are trivial, but maybe still needed
  instance has_coe_to_G : has_coe (Bᵣ r) G := { coe := subtype.val }
  @[simp]
  lemma coe_is_rblade (b : Bᵣ r) : is_rblade r b := b.property

  /- todo: do we want this? -/
  -- instance has_zero : has_zero (Bᵣ r) := {
  --   zero := ⟨(0 : G), begin
  --     use [0, zero_pairwise_ortho_vector r],
  --     simp,
  --   end⟩ 
  -- }

  /- scalar multiple of an element of Bᵣ is also in Bᵣ -/
  lemma smul_mem_Bᵣ {b : G} {k : G₀} (hb : is_rblade r b) : (is_rblade r ((fₛ k) * b)) := begin
    exact exists.elim hb begin
      intros a ha,
      use k*a,
      exact exists.elim ha begin
        intros a_1 ha_1,
        use a_1,
        rw ha_1,
        rw ring_hom.map_mul,
        rw mul_assoc
      end
    end
  end

  /- now show via trivial proofs that Bᵣ is a mul_action and has_neg -/
  def smul (k : G₀) (b : Bᵣ r) : Bᵣ r := ⟨(fₛ k) * b.val, smul_mem_Bᵣ b.property⟩ 
  instance has_scalar (r : ℕ) : has_scalar G₀ (Bᵣ r) := { smul := smul }
  
  def one_smul (b : Bᵣ r) : smul (1 : G₀) b = b := by simp [smul]
  def mul_smul (k1 k2 : G₀) (b : Bᵣ r) : smul (k1 * k2) b =  smul k1 (smul k2 b) := by simp [smul, mul_assoc]
  instance mul_action : mul_action G₀ (Bᵣ r) := {one_smul := one_smul, mul_smul := mul_smul, ..has_scalar r}

  def neg (b : Bᵣ r) : Bᵣ r := smul (-1 : G₀) b
  instance has_neg (r : ℕ) : has_neg (Bᵣ r) := { neg := neg}

end Bᵣ

end r_blades

end geometric_algebra