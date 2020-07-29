import geometric_algebra.nursery.tensor_algebra
import geometric_algebra.nursery.tensor_algebra_ring
import ring_theory.ideals
import linear_algebra.quadratic_form

open tensor_algebra

universes u

-- produce the setoid corresponding to the ideal of a subalgebra
def setoid_ideal_of_subalgebra
  {R : Type u} {A : Type u} [comm_ring R] [ring A] [algebra R A]
  (s : subalgebra R A) : setoid A
:= {
  r := λ a b, a - b ∈ s,
  iseqv := ⟨
    λ a, by {rw sub_self, exact subalgebra.zero_mem _},
    λ a b h, by {rw ←neg_sub, exact subalgebra.neg_mem _ h},
    λ a b c hab hbc, by {
      have hac := subalgebra.add_mem _ hab hbc,
      rw [add_sub, sub_add, sub_self, sub_zero] at hac,
      exact hac,
    }⟩}

namespace clifford_algebra

variables {R : Type u} [comm_ring R]
variables {M : Type u} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

-- tensor parametrized by the quadratic form, just so we have a unique type
include Q
def pre := tensor_algebra R M
omit Q
namespace pre
  instance : ring (pre Q) := tensor_algebra.ring R M
  instance : algebra R (pre Q) := tensor_algebra.algebra R M
end pre

-- produce the setoid corresponding to the ideal of a subalgebra
def setoid_ideal_of_subalgebra
  {R : Type u} {A : Type u} [comm_ring R] [ring A] [algebra R A]
  (s : subalgebra R A) : setoid A
:= {
  r := λ a b, a - b ∈ s,
  iseqv := ⟨
    λ a, by {rw sub_self, exact subalgebra.zero_mem _},
    λ a b h, by {rw ←neg_sub, exact subalgebra.neg_mem _ h},
    λ a b c hab hbc, by {
      have hac := subalgebra.add_mem _ hab hbc,
      rw [add_sub, sub_add, sub_self, sub_zero] at hac,
      exact hac,
    }⟩}

-- we can't use the builtin idea, as that requires commutativity
def ga_ideal : subalgebra R (pre Q) := algebra.adjoin R {
  i | ∃ v, univ R M v * univ R M v - algebra_map R (pre Q) (Q v) = i
}

-- declare e
instance : setoid (pre Q) := setoid_ideal_of_subalgebra (ga_ideal Q)

end clifford_algebra

#check ideal

@[reducible]
def clifford_algebra
  {R : Type u} [comm_ring R]
  {M : Type u} [add_comm_group M] [module R M]
  (Q : quadratic_form R M) :=
quotient (clifford_algebra.setoid Q)

namespace clifford_algebra
variables {R : Type u} [comm_ring R]
variables {M : Type u} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

instance : has_scalar R (clifford_algebra Q) := {
  smul := λ k v, quotient.lift_on v
    (λ v, ⟦has_scalar.smul k v⟧)
    $ λ _ _ H, quotient.sound
    $ begin
      change _ ∈ _,
      rw ← smul_sub,
      refine subalgebra.smul_mem _ H _,
    end}

-- exercises left to reader...
instance : ring (clifford_algebra Q) := {
  zero := ⟦0⟧,
  add := quotient.map₂ (+) (λ a a' ha b b' hb, begin
    change _ ∈ _,
    convert subalgebra.add_mem _ ha hb using 1,
    abel,
  end),
  neg := quotient.map (has_neg.neg) (λ a a' ha, begin
    change _ ∈ _,
    convert subalgebra.neg_mem _ ha,
    abel,
  end),
  -- these are very tedious
  add_assoc := by {
    rintros ⟨⟩ ⟨⟩ ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    simp only [add_assoc, sub_self],
    exact subalgebra.zero_mem _,
  },
  zero_add := by {
    rintros ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    simp only [zero_add, sub_self],
    exact subalgebra.zero_mem _,
  },
  add_zero := by {
    rintros ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    simp only [add_zero, sub_self],
    exact subalgebra.zero_mem _,
  },
  add_left_neg := by {
    rintros ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    simp only [add_left_neg, sub_self],
    exact subalgebra.zero_mem _,
  },
  add_comm := by {
    rintros ⟨⟩ ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    simp only [add_comm, sub_self],
    exact subalgebra.zero_mem _,
  },

  -- this stuff doesn't seem possible yet
  one := ⟦1⟧,
  mul := quotient.map₂ (*) (λ a a' ha b b' hb, begin
    change _ ∈ _,
    change _ ∈ _ at ha,
    change _ ∈ _ at hb,
    have h := subalgebra.mul_mem _ ha hb,
    simp only [mul_sub, sub_mul] at h,
    sorry,
    -- this looks unprovable
  end),
  mul_assoc := by {
    rintros ⟨⟩ ⟨⟩ ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    sorry
  },
  one_mul := by {
    rintros ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    sorry
  },
  mul_one := by {
    rintros ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    sorry
  },
  left_distrib := by {
    rintros ⟨⟩ ⟨⟩ ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    sorry
  },
  right_distrib := by {
    rintros ⟨⟩ ⟨⟩ ⟨⟩,
    change quotient.mk _ = quotient.mk _,
    apply quotient.sound,
    change _ ∈ _,
    sorry
  }}

instance : algebra R (clifford_algebra Q) := {
  to_fun := λ r, ⟦algebra_map R (pre Q) r⟧,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry,
  commutes' := sorry,
  smul_def' := sorry }

-- lemma vector_square_scalar

end clifford_algebra
