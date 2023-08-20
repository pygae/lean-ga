/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.field.basic
import algebra.module.prod
import algebra.punit_instances
import data.finset.sort
import data.vector
import tactic

/-!
# Derived from "A Formalization of Grassmann-Cayley Algebra in Coq and Its Application to Theorem Proving in Projective Geometry"

by Laurent Fuchs and Laurent Théry
-/

namespace laurent

variables (α : Type) [field α]

-- vectors
def Kₙ : ℕ → Type
| 0 := unit
| (n + 1) := α × Kₙ n
-- addition and scalar multiplication
instance : Π (n : ℕ), add_comm_group (Kₙ α n)
| 0 := by {dunfold Kₙ, apply_instance}
| (n + 1) := by {dunfold Kₙ, haveI := Kₙ.add_comm_group n, apply_instance}
instance : Π n, module α (Kₙ α n)
| 0 := by {dunfold Kₙ, apply_instance}
| (n + 1) := by {dunfold Kₙ, haveI := Kₙ.module n, apply_instance}

-- multivectors
def Gₙ : ℕ → Type
| 0 := α
| (n + 1) := Gₙ n × Gₙ n
-- addition
instance : Π n, add_comm_group (Gₙ α n)
| 0 := by {unfold Gₙ, apply_instance}
| (n + 1) := by {unfold Gₙ, haveI := Gₙ.add_comm_group n, apply_instance}

variables {α}

-- coercions
def coe_α : Π {n}, α → Gₙ α n
| 0 k := k
| (n + 1) k := (coe_α 0, coe_α k)
instance has_coe_α : Π n, has_coe α (Gₙ α n) := λ n, ⟨coe_α⟩
def coe_Kₙ : Π {n}, Kₙ α n → Gₙ α n
| 0 k := 0
| (n + 1) ⟨x₁, x₂⟩ := (x₁, coe_Kₙ x₂)
instance has_coe_Kₙ : Π n, has_coe (Kₙ α n) (Gₙ α n) := λ n, ⟨coe_Kₙ⟩

-- conjugation
def conj : Π {n}, Gₙ α n → Gₙ α n
| 0 x := x
| (n + 1) ⟨x₁, x₂⟩ := (-conj x₁, conj x₂)
def conj_d : Π {n}, Gₙ α n → Gₙ α n
| 0 x := x
| (n + 1) ⟨x₁, x₂⟩ := (conj_d x₁, -conj_d x₂)
prefix (name := laurent.conj) `̅`:max := conj  -- this unicode is probably a bad idea...
notation (name := laurent.conj_d) `̅`:max x `ᵈ` := conj_d x -- this unicode is definitly a bad idea!

-- vee and wedge
reserve infix `⋏`:70
def wedge : Π {n}, Gₙ α n → Gₙ α n → Gₙ α n
| 0 x y := (x * y : α)
| (n + 1) ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := let infix ` ⋏ ` := wedge in
    (x₁ ⋏ y₂ + ̅x₂ ⋏ y₁, x₂ ⋏ y₂)
infix (name := laurent.wedge) ` ⋏ ` := wedge
reserve infix `⋎`:70
def vee : Π {n}, Gₙ α n → Gₙ α n → Gₙ α n
| 0 x y := (x * y : α)
| (n + 1) ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := let infix ` ⋎ ` := vee in
    (x₂ ⋎ y₂, x₁ ⋎ y₂ + x₂ ⋎ ̅y₁ᵈ)
infix (name := laurent.vee) ` ⋎ ` := vee

instance {n} : has_one (Gₙ α n):= ⟨(1 : α)⟩

section theorems

lemma conj_zero : Π {n}, conj (0 : Gₙ α n) = 0
| 0 := rfl
| (n + 1) := prod.ext
  ((congr_arg has_neg.neg conj_zero).trans neg_zero)
  conj_zero

lemma conj_add : Π {n} (x y : Gₙ α n), conj (x + y) = conj x + conj y
| 0 (x : α) y := rfl
| (n + 1) (x₁, x₂) (y₁, y₂) := prod.ext
  ((congr_arg _ $ conj_add x₁ y₁).trans $ neg_add _ _)
  (conj_add x₂ y₂)

lemma conj_d_zero : Π {n}, conj_d (0 : Gₙ α n) = 0
| 0 := rfl
| (n + 1) := prod.ext
  conj_d_zero
  ((congr_arg has_neg.neg conj_d_zero).trans neg_zero)

lemma conj_d_add : Π {n} (x y : Gₙ α n), conj_d (x + y) = conj_d x + conj_d y
| 0 (x : α) y := rfl
| (n + 1) (x₁, x₂) (y₁, y₂) := prod.ext
  (conj_d_add x₁ y₁)
  ((congr_arg _ $ conj_d_add x₂ y₂).trans $ neg_add _ _)

lemma wedge_add : Π {n} (x y z : Gₙ α n), x ⋏ (y + z) = x ⋏ y + x ⋏ z
| 0 (x : α) y z := mul_add x y z
| (n + 1) (x₁, x₂) (y₁, y₂) (z₁, z₂) := prod.ext
  ((congr_arg2 (+) (wedge_add _ _ _) (wedge_add _ _ _)).trans (add_add_add_comm _ _ _ _))
  (wedge_add _ _ _)

lemma add_wedge : Π {n} (x y z : Gₙ α n), (x + y) ⋏ z = x ⋏ z + y ⋏ z
| 0 (x : α) y z := add_mul x y z
| (n + 1) (x₁, x₂) (y₁, y₂) (z₁, z₂) := prod.ext
  ((congr_arg2 (+) (add_wedge _ _ _) $
    eq.trans (by rw [conj_add]) (add_wedge _ _ _)).trans (add_add_add_comm _ _ _ _))
  (add_wedge _ _ _)

lemma vee_add : Π {n} (x y z : Gₙ α n), x ⋎ (y + z) = x ⋎ y + x ⋎ z
| 0 (x : α) y z := mul_add x y z
| (n + 1) (x₁, x₂) (y₁, y₂) (z₁, z₂) := prod.ext
  (vee_add _ _ _)
  ((congr_arg2 (+) (vee_add _ _ _) $
    (congr_arg _ (conj_d_add _ _)).trans (vee_add _ _ _)).trans (add_add_add_comm _ _ _ _))

lemma add_vee : Π {n} (x y z : Gₙ α n), (x + y) ⋎ z = x ⋎ z + y ⋎ z
| 0 (x : α) y z := add_mul x y z
| (n + 1) (x₁, x₂) (y₁, y₂) (z₁, z₂) := prod.ext
  (add_vee _ _ _)
  (eq.trans (congr_arg2 (+) (add_vee _ _ _) (add_vee _ _ _)) (add_add_add_comm _ _ _ _))

lemma wedge_zero : Π {n} (x : Gₙ α n), x ⋏ 0 = 0
| 0 (x : α) := mul_zero x
| (n + 1) (x₁, x₂) := prod.ext
  ((congr_arg2 _ (wedge_zero _) (wedge_zero _)).trans $ add_zero _) (wedge_zero _)

lemma zero_wedge : Π {n} (x : Gₙ α n), 0 ⋏ x = 0
| 0 (x : α) := zero_mul x
| (n + 1) (x₁, x₂) := prod.ext
  ((congr_arg2 (+) (zero_wedge _)
    (by rw [conj_zero, zero_wedge])).trans $ add_zero _) (zero_wedge _)

lemma wedge_one : Π {n} (x : Gₙ α n), x ⋏ 1 = x
| 0 (x : α) := mul_one x
| (n + 1) (x₁, x₂) := prod.ext (show x₁ ⋏ 1 + _ ⋏ _ = _, by rw [wedge_one]; sorry) (wedge_one _)

lemma wedge_assoc : Π {n} (x y z : Gₙ α n), (x ⋏ y) ⋏ z = x ⋏ (y ⋏ z)
| 0 (x : α) y z := mul_assoc x y z
| (n + 1) (x₁, x₂) (y₁, y₂) (z₁, z₂) := prod.ext
  (by {
    simp_rw [wedge, add_wedge, wedge_add, ←wedge_assoc, add_assoc],
    congr' 2,
    sorry })
  (wedge_assoc _ _ _)

end theorems

def Gₙ.coeff : Π {n}, Gₙ α n → finset (fin n) → α
| 0 x s := x
| (n + 1) (xi, yi) s :=
    let s' : finset (fin n) := s.bUnion (λ i : fin n.succ, fin.cases ∅ singleton i) in
    (if (0 : fin n.succ) ∈ s then xi else yi).coeff s'

instance has_repr [has_repr α] {n} : has_repr (Gₙ α n) :=
{ repr := λ x,
    let basis : list (finset (fin n)) :=
      (list.range (n + 1)).bind (λ k,
        ((list.fin_range n).sublists_len k).map list.to_finset) in
    let parts := basis.filter_map $ λ s,
      let c := repr (x.coeff s) in
      if c = "0" then
        none
      else
        some $ c ++
          if s.card = 0 then
            ""
          else
            "•e" ++ string.join ((s.sort (≤)).map repr) in
    match parts with
    | [] := "0"
    | _ := string.intercalate " + " parts
    end }

section example_3d

def x : Kₙ ℚ 3 := (1, 0, 0, ())
def y : Kₙ ℚ 3 := (0, 1, 0, ())
def z : Kₙ ℚ 3 := (0, 0, 1, ())

#eval (0 : Gₙ ℚ 3)
#eval [(x : Gₙ ℚ 3), (y : Gₙ ℚ 3), (z : Gₙ ℚ 3)]
#eval [(x ⋏ y : Gₙ ℚ 3), (y ⋏ z : Gₙ ℚ 3), (x ⋏ z : Gₙ ℚ 3)]
#eval [(x ⋎ y : Gₙ ℚ 3), (y ⋎ z : Gₙ ℚ 3), (x ⋎ z : Gₙ ℚ 3)]
#eval [((x ⋏ y) ⋏ z : Gₙ ℚ 3), (x ⋏ (y ⋏ z) : Gₙ ℚ 3)]
#eval [((x ⋏ y) ⋏ z : Gₙ ℚ 3), (x ⋏ (y ⋏ z) : Gₙ ℚ 3)]
#eval [((x ⋎ y) ⋎ z : Gₙ ℚ 3), (x ⋎ (y ⋎ z) : Gₙ ℚ 3)]
#eval show Gₙ ℚ 3, from (x + y) ⋎ (x ⋏ y)

end example_3d

end laurent
