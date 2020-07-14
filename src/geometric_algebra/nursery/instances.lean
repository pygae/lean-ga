import geometric_algebra.nursery.chisolm
import data.complex.module

instance field_ga (K : Type*) [field K] : geometric_algebra K K K := {
  f₁ := {
    to_fun := id,
    map_zero' := rfl,
    map_add' := begin
      simp only [forall_const, id.def, eq_self_iff_true]
    end
  },
  vec_sq_scalar := begin
    intro v,
    use v * v,
    simp only [algebra.id.map_eq_self, add_monoid_hom.coe_mk, id.def],
  end
}

noncomputable instance rrc_ga : geometric_algebra ℝ ℝ ℂ := {
  f₁ := {
    to_fun := λx, x,
    map_zero' := rfl,
    map_add' := begin
      intros x y,
      norm_cast,
    end
  },
  vec_sq_scalar := begin
    intro v,
    use v * v,
    simp only [add_monoid_hom.coe_mk, ring_hom.map_mul],
    refl,
  end
}

noncomputable instance rcc_ga : geometric_algebra ℝ ℂ ℂ := {
  f₁ := {
    to_fun := id,
    map_zero' := rfl,
    map_add' := by simp,
  },
  vec_sq_scalar := sorry /- mathematically false due to the wrong mul equiped with ? -/
}