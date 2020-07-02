-- Definition of a graded algebra, with no other operations defined
import algebra.group
import linear_algebra.tensor_product
import tactic.ring

universes u

open_locale big_operators
open_locale classical
open finset

class graded_module_components
  -- a type for each grade.
  (A : ℤ → Type u)
:= 
  -- (A 0) is the scalar type
  [zc: comm_ring (A 0)]

  -- all the types form commutative vector spaces
  [b: ∀ r, add_comm_group (A r)]
  [c: ∀ r, module (A 0) (A r)]

attribute [instance] graded_module_components.zc
attribute [instance] graded_module_components.b
attribute [instance] graded_module_components.c

namespace graded_module_components
  variables {A : ℤ → Type u}
  /-- objects are coercible only if they have the same grade-/
  instance has_coe (r s : ℕ) (h: r = s) : has_coe (A r) (A s) := { coe := by {subst h, exact id}}
end graded_module_components

-- needed for the definition of `select`
attribute [instance] dfinsupp.to_semimodule

/-- Grade selection maps from objects in G to a finite set of components of substituent grades -/
class has_grade_select
  (A : ℤ → Type u) (G: Type u)
  [graded_module_components A]
  [add_comm_group G]
  [module (A 0) G] :=
(select : G →ₗ[A 0] (Π₀ r, A r))

/- TODO: check precedence -/
notation `⟨`:0 g`⟩_`:0 r:100 := has_grade_select.select g r

-- introducing these needs types which restrict the domain of A to `{z // z : ℤ, z %2 == 0}`
-- notation `⟨`:0 g`⟩₊`:0 := has_grade_select.select_even
-- notation `⟨`:0 g`⟩₋`:0 := has_grade_select.select_odd

/-- A module divisible into disjoint graded modules, where the grade selectio
    operator is a complete and independent set of projections -/
class graded_module
  (A : ℤ → Type u) (G: Type u)
  [graded_module_components A]
  [add_comm_group G]
  [module (A 0) G]
  extends has_grade_select A G :=
(to_fun : ∀{r}, A r →ₗ[A 0] G)
(is_complete : ∀ g : G, ∀ f, f = select g ↔ g = f.sum (λ r, to_fun))


namespace graded_module
  variables {A : ℤ → Type u} {G: Type u}
  variables [graded_module_components A] [add_comm_group G] [module (A 0) G]
  variables [graded_module A G]

  /-- convert from r-vectors to multi-vectors -/
  instance has_coe (r : ℤ) : has_coe (A r) G := { coe := to_fun }

  /-- An r-vector has only a single grade
      Discussed at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Expressing.20a.20sum.20with.20finitely.20many.20nonzero.20terms/near/202657281-/
  lemma select_coe_is_single {r : ℤ} (v : A r) : has_grade_select.select (to_fun v : G) = dfinsupp.single r v := begin
    symmetry,
    rw is_complete (to_fun v : G) (dfinsupp.single r v),
    symmetry,
    apply dfinsupp.sum_single_index,
    exact linear_map.map_zero _,
  end

  def is_r_vector (r : ℤ) (a : G) := to_fun (⟨a⟩_r : A r) = a
  
  /-- Chisholm 6a, ish.
      This says A = ⟨A}_r for r-vectors.
      Chisholm aditionally wants proof that A != ⟨A}_r for non-rvectors -/
  lemma r_grade_of_coe {r : ℤ} (v : A r) : ⟨(to_fun v : G)⟩_r = v := begin
    rw select_coe_is_single,
    rw dfinsupp.single_apply,
    simp,
  end

  /-- to_fun is injective -/
  lemma to_fun_inj (r : ℤ) : function.injective (to_fun : A r → G) := begin
    intros a b h,
    rw ← r_grade_of_coe a,
    rw ← r_grade_of_coe b,
    rw h,
  end
  
  /-- Chisholm 6b -/
  lemma grade_of_sum (r : ℤ) (a b : G) : (⟨a + b⟩_r : A r) = ⟨a⟩_r + ⟨b⟩_r := by simp

  /-- Chisholm 6c -/
  lemma grade_smul (r : ℤ) (k : A 0) (a : G) : (⟨k • a⟩_r : A r) = k • ⟨a⟩_r := by simp

  /-- chisholm 6d. This is super awkward to express due to all the casting -/
  lemma grade_grade (r s : ℤ) (a : G) :
    (to_fun (⟨ (to_fun (⟨a⟩_r : A r) : G) ⟩_s : A s) : G) = if r = s then to_fun (⟨a⟩_r : A r) else 0
  := begin
    rw select_coe_is_single,
    rw dfinsupp.single_apply,
    split_ifs,
    {
      cases h with s,
      simp,
    },
    simp,
  end

  /-- chisholm 6e. The phrasing is made a little awkward by the construction of the finite decomposition of select --/
  lemma grade_sum (g : G) : g = (has_grade_select.select g).sum (λ r, (to_fun : A r → G)) := begin
    apply (is_complete g (has_grade_select.select g)).1,
    simp,
  end

end graded_module
