-- Definition of a graded algebra, with no other operations defined
import algebra.group
import linear_algebra.tensor_product
import linear_algebra.dfinsupp
import tactic.ring

universes u

-- TODO: open_locale only under namespace, never globally
open_locale big_operators
open_locale classical
open finset

-- TODO: should this have a shorter name like graded and places it under a namespace?
class graded_module_components
  -- a type for each grade.
  -- TODO do we need ℤ or we can simply use ℕ
  -- the inductive definition of ℤ is based on ℕ 
  -- and may add unwanted complexity to proof
  (A : ℤ → Type u)
:= 
  -- (A 0) is the scalar type
  -- TODO what does zc stand for?
  [zc: comm_ring (A 0)]

  -- all the types form commutative vector spaces
  -- TODO change to meaningful names
  [b: ∀ r, add_comm_monoid (A r)]
  [c: ∀ r, module (A 0) (A r)]

attribute [instance] graded_module_components.zc
attribute [instance] graded_module_components.b
attribute [instance] graded_module_components.c

-- namespace graded_module_components
--   -- TODO should always open a section before using variables
--   variables {A : ℤ → Type u}
--   /-- objects are coercible only if they have the same grade-/
--   -- TODO did it work? should we remove it?
--   instance has_coe (r s : ℕ) (h: r = s) : has_coe (A r) (A s) := { coe := by {subst h, exact id}}
-- end graded_module_components


/-- Grade selection maps from objects in G to a finite set of components of substituent grades -/
-- TODO how about place it under namespace graded and name it has_select
class has_grade_select
  (A : ℤ → Type u) (G: Type u)
  [graded_module_components A]
  [add_comm_group G]
  [module (A 0) G] :=
-- TODO better find a way to avoid A 0 everywhere
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
  -- TODO: we should avoid the plague of [] parameters, by bundling them?
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

  /-- locally bind the notation above to our A and G-/
  -- TODO I have a feeling that this notation would not survive very long
  local notation `⟨`:0 g`⟩_`:0 r:100 := @has_grade_select.select A G _ _ _ _ g r

  /-- convert from r-vectors to multi-vectors -/
  instance has_coe (r : ℤ) : has_coe (A r) G := { coe := to_fun }

  @[simp]
  lemma coe_def {r : ℤ} (v : A r) : (v : G) = to_fun v := rfl

  /-- An r-vector has only a single grade
      Discussed at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Expressing.20a.20sum.20with.20finitely.20many.20nonzero.20terms/near/202657281-/
  lemma select_coe_is_single {r : ℤ} (v : A r) :
  has_grade_select.select (v : G) = dfinsupp.single r v := begin
    symmetry,
    rw is_complete (v : G) (dfinsupp.single r v),
    symmetry,
    apply dfinsupp.sum_single_index,
    exact linear_map.map_zero _,
  end

  def is_r_vector (r : ℤ) (a : G) := (⟨a⟩_r : G) = a
  
  /-- Chisholm 6a, ish.
      This says A = ⟨A}_r for r-vectors.
      Chisholm aditionally wants proof that A != ⟨A}_r for non-rvectors -/
  lemma r_grade_of_coe {r : ℤ} (v : A r) : ⟨v⟩_r = v := begin
    rw select_coe_is_single,
    rw dfinsupp.single_apply,
    rw [dif_pos],
    refl,
  end

  /-- to_fun is injective -/
  lemma to_fun_inj (r : ℤ) : function.injective (to_fun : A r → G) := begin
    intros a b h,
    rw ← r_grade_of_coe a,
    rw ← r_grade_of_coe b,
    simp only [coe_def],
    rw h,
    apply_instance,
  end
  
  /-- Chisholm 6b -/
  lemma grade_of_sum (r : ℤ) (a b : G) :
  ⟨a + b⟩_r = ⟨a⟩_r + ⟨b⟩_r :=
  by simp only [dfinsupp.add_apply, linear_map.map_add]

  /-- Chisholm 6c -/
  lemma grade_smul (r : ℤ) (k : A 0) (a : G) :
  ⟨k • a⟩_r = k • ⟨a⟩_r :=
  by simp only [dfinsupp.smul_apply, linear_map.map_smul]

  /-- chisholm 6d. Modifid to use `_s` instead of `_r` on the right, to keep the statement cast-free -/
  lemma grade_grade (r s : ℤ) (a : G) : ⟨⟨a⟩_r⟩_s = if r = s then ⟨a⟩_s else 0
  := begin
    rw select_coe_is_single,
    rw dfinsupp.single_apply,
    split_ifs,
    {
      cases h with s,
      simp only [],
    },
    simp only [eq_self_iff_true],
  end

  /-- chisholm 6e. The phrasing is made a little awkward by the construction of the finite decomposition of select --/
  lemma grade_sum (g : G) : g = (has_grade_select.select g).sum (λ r, (to_fun : A r → G)) := begin
    apply (is_complete g (has_grade_select.select g)).1,
    refl,
  end

end graded_module
