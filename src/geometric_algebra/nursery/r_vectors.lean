import geometric_algebra.nursery.r_blades

namespace geometric_algebra

section r_vectors

parameters
{G₀ : Type*} [field G₀]
{G₁ : Type*} [add_comm_group G₁] [vector_space G₀ G₁]
{G : Type*} [ring G] [algebra G₀ G] [geometric_algebra G₀ G₁ G]

namespace Gᵣ
  variables {r : ℕ}

  -- this is trivial, but maybe needed
  -- instance has_coe_from_Bᵣ : has_coe (Bᵣ r) (Gᵣ r) := { coe := λ b, ⟨b.val, add_subgroup.subset_closure b.property⟩ }

  -- scalar multiple of an element of Gᵣ is also in Gᵣ
  lemma smul_mem_Gᵣ {v : G} {k : G₀} (hv : v ∈ Gᵣ r) : ((fₛ k) * v) ∈ Gᵣ r := begin
    apply add_subgroup.closure_induction hv,
    {
      intros x hx,
      apply add_subgroup.subset_closure,
      exact Bᵣ.smul_mem_Bᵣ hx,
    },
    {
      rw mul_zero,
      exact (0 : Gᵣ r).property,
    },
    {
      intros a b,
      rw mul_add,
      exact add_subgroup.add_mem (Gᵣ r)
    },
    {
      intros a,
      rw ← neg_mul_eq_mul_neg,
      exact add_subgroup.neg_mem (Gᵣ r)
    }
  end

  -- now show via trivial proofs that Gᵣ is a semimodule (basically a vector space)
  def smul (k : G₀) (v : Gᵣ r) : Gᵣ r := ⟨fₛ k * v, smul_mem_Gᵣ v.property⟩
  instance has_scalar (r : ℕ) : has_scalar G₀ (Gᵣ r) := { smul := smul }
  
  def one_smul (v : Gᵣ r) : smul (1 : G₀) v = v := by simp [smul]
  def mul_smul (k1 k2 : G₀) (v : Gᵣ r) : smul (k1 * k2) v =  smul k1 (smul k2 v) := by simp [smul, mul_assoc]
  instance mul_action : mul_action G₀ (Gᵣ r) := {one_smul := one_smul, mul_smul := mul_smul, ..has_scalar r}

  def smul_add (k : G₀) (x y : Gᵣ r) : smul k (x + y) = smul k x + smul k y := by {simp [smul, mul_add], refl}
  def smul_zero (k : G₀) : smul k (0 : Gᵣ r) = 0 := by {simp [smul], refl}
  instance distrib_mul_action : distrib_mul_action G₀ (Gᵣ r) := { smul_add := smul_add, smul_zero := smul_zero, ..mul_action }
    
  def add_smul (k1 k2 : G₀) (v : Gᵣ r) : smul (k1 + k2) v = smul k1 v + smul k2 v := by {simp [smul, add_mul], refl}
  def zero_smul (v : Gᵣ r) : smul (0 : G₀) v = 0 := by {simp [smul], refl}
  instance semimodule (r : ℕ) : semimodule G₀ (Gᵣ r) := {add_smul := add_smul, zero_smul := zero_smul, ..distrib_mul_action }
end Gᵣ

lemma grade_iff {r : ℕ} {a : Mᵣ r} {g : ℕ} : a ∈ Gᵣ g ↔ a = grade_select a g := sorry
lemma grade_add {r : ℕ} {a b : Mᵣ r} {g : ℕ} : grade_select (a + b) g = grade_select a g + grade_select b g:= sorry
lemma grade_scale {r : ℕ} {a : Mᵣ r} {k : G₀} {g : ℕ} : grade_select (k*a) g = k * grade_select a g := sorry
lemma grade_compose {r : ℕ} {a : Mᵣ r} {g1 : ℕ} {g2 : ℕ} : grade_select (grade_select a g1) g2 = if g1 = g2 then grade_select a g1 else 0 := sorry

/-
  Symmetrised product of two vectors must be a scalar
-/
lemma vec_sym_prod_scalar (a b : G₁) : is_scalar (a *₊ᵥ b) :=
have h1 : (a + b)²ᵥ = a²ᵥ + b²ᵥ + a *₊ᵥ b, from begin
  unfold square_vec sym_prod_vec prod_vec,
  rw add_monoid_hom.map_add fᵥ a b,
  rw left_distrib,
  repeat {rw right_distrib},
  abel,
end,
have vec_sq_scalar : ∀ v : G₁, ∃ k : G₀, v²ᵥ = fₛ k, from
  λ v, geometric_algebra.vec_sq_scalar(v),
exists.elim (vec_sq_scalar (a + b))
(
  assume kab,
  exists.elim (vec_sq_scalar a)
  (
    assume ka,
    exists.elim (vec_sq_scalar b)
    (
      assume kb,
      begin
        intros hb ha hab,
        rw [hb, ha, hab] at h1,
        have h2 : (fₛ (kab - ka - kb : G₀) : G) = sym_prod_vec a b, by {
          repeat {rw ring_hom.map_sub},
          rw h1,
          abel,
        },
        rw ← h2,
        rw is_scalar,
        apply Bᵣ.all_G₀_is_rblade0, -- this feels clumsy, can I make this automatic?
      end
    )
  )
)

end r_vectors

end geometric_algebra
