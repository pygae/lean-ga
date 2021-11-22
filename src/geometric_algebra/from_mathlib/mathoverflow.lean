import data.mv_polynomial.comm_ring
import linear_algebra.finsupp
import linear_algebra.clifford_algebra
import data.zmod.basic
import data.matrix.notation
import field_theory.mv_polynomial
import tactic.induction
import algebra.char_p.quotient
import data.nat.prime
import algebra.char_p.pi

/-!
An attempt to formalize https://mathoverflow.net/questions/60596/clifford-pbw-theorem-for-quadratic-form/87958#87958

Some Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.F0.9D.94.BD.E2.82.82.5B.CE.B1.2C.20.CE.B2.2C.20.CE.B3.5D.20.2F.20.28.CE.B1.C2.B2.2C.20.CE.B2.C2.B2.2C.20.CE.B3.C2.B2.29/near/222716333.
-/

noncomputable theory

section for_mathlib

lemma ideal.comap_span_le {R : Type*} {S : Type*} [semiring R] [semiring S] (f : S →+* R)
  (g : R →+* S) (h : function.left_inverse g f) (s : set R) :
  ideal.comap f (ideal.span s) ≤ ideal.span (g '' s) :=
begin
  rintros x (hx : f x ∈ ideal.span s),
  have := ideal.apply_coe_mem_map g _ ⟨_, hx⟩,
  rw [ideal.map_span, subtype.coe_mk, h x] at this,
  exact this,
end

/-- `char_p.quotient'` as an `iff`. -/
lemma char_p.quotient_iff' (R : Type*) [comm_ring R] (n : ℕ) [char_p R n] (I : ideal R) :
  char_p I.quotient n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 :=
begin
  refine ⟨λ (i : char_p I.quotient n) x hx, _, char_p.quotient' n I⟩,
  resetI,
  have := char_p.cast_eq_zero_iff I.quotient n,
  rw char_p.cast_eq_zero_iff R n,
  refine (this _).mp _,
  convert (submodule.quotient.mk_eq_zero I).mpr hx,
  simp,
end

lemma ideal.span_le_bot {R : Type*} [semiring R] (s : set R) : ideal.span s ≤ ⊥ ↔ s ≤ {0} :=
submodule.span_le

/-- `char_p.quotient'` as an `iff`. -/
lemma char_p.quotient_iff'' (R : Type*) [comm_ring R] (n : ℕ) [char_p R n] (I : ideal R) :
  char_p I.quotient n ↔ I.comap (nat.cast_ring_hom _) ≤ (nat.cast_ring_hom R).ker :=
(char_p.quotient_iff' _ _ _).trans begin
  rw ring_hom.ker_eq_comap_bot,
  exact iff.rfl,
end

lemma ring_hom.comap_ker {R S T : Type*} [semiring R] [semiring S] [semiring T] (f : S →+* R)
  (g : T →+* S) : f.ker.comap g = (f.comp g).ker :=
by rw [ring_hom.ker_eq_comap_bot, ideal.comap_comap, ring_hom.ker_eq_comap_bot]

end for_mathlib

namespace q60596

open mv_polynomial

def k_ideal := ideal.span { x : mv_polynomial (fin 3) (zmod 2) | ∃ i, x = X i * X i }

-- 𝔽₂[α, β, γ] / (α², β², γ²)
@[derive [comm_ring, comm_semiring, ring, semiring, add_comm_group, add_comm_monoid]]
def k := k_ideal.quotient

instance : fact (nat.prime 2) := ⟨nat.prime_two⟩

instance : fact (0 < 2) := ⟨zero_lt_two⟩

lemma comap_C_span_le_bot :
  k_ideal.comap C ≤ ⊥ :=
begin
  refine (ideal.comap_span_le _ _ constant_coeff_C _).trans _,
  refine (ideal.span_le_bot _).2 _,
  rintro x ⟨_, ⟨i, rfl⟩, rfl⟩,
  rw [ring_hom.map_mul, constant_coeff_X, mul_zero, set.mem_singleton_iff],
end

/-- `k` has characteristic 2. -/
instance k.char_p : char_p k 2 :=
begin
  dunfold k,
  rw char_p.quotient_iff'',
  have : (nat.cast_ring_hom (mv_polynomial (fin 3) (zmod 2))) = C.comp (nat.cast_ring_hom _),
  { ext1 r, exact (C.map_nat_cast r).symm, },
  rw [this, ←ideal.comap_comap, ←ring_hom.comap_ker],
  apply ideal.comap_mono,
  refine comap_C_span_le_bot.trans bot_le,
end

lemma two_eq_zero : (2 : k) = 0 :=
by simpa only [nat.cast_bit0, nat.cast_one] using char_p.cast_eq_zero k 2

abbreviation α : k := ideal.quotient.mk _ (mv_polynomial.X 0)
abbreviation β : k := ideal.quotient.mk _ (mv_polynomial.X 1)
abbreviation γ : k := ideal.quotient.mk _ (mv_polynomial.X 2)

/-- The elements above square to zero -/
@[simp] lemma X_sq (i : fin 3) :
  ideal.quotient.mk _ (mv_polynomial.X i) * ideal.quotient.mk _ (mv_polynomial.X i) = (0 : k) :=
begin
  change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
  apply quotient.sound',
  dunfold submodule.quotient_rel setoid.r,
  simp only [sub_zero, ideal.span],
  apply submodule.subset_span,
  refine ⟨i, rfl⟩,
end

@[simps]
def L_func : (fin 3 → k) →ₗ[k] k :=
α • linear_map.proj 0 - β • linear_map.proj 1 - γ • linear_map.proj 2

/-- The quotient of k^3 by the specified relation-/
@[derive [add_comm_group, module k]]
def L := (L_func.ker).quotient

-- local attribute [irreducible] k

def sq {ι R : Type*} [comm_ring R] (i : ι) : quadratic_form R (ι → R) :=
begin
  let a := _,
  refine quadratic_form.lin_mul_lin a a,
  exact @linear_map.proj _ _ _ (λ _, R) _ _ i
end

lemma char_two_neg {R} [ring R] [char_p R 2] (x : R) : -x = x :=
by rw [neg_eq_iff_add_eq_zero, ←two_smul ℕ x, nsmul_eq_smul_cast R 2 x, char_p.cast_eq_zero,
  zero_smul]

lemma char_two_sub {R} [ring R] [char_p R 2] (x y : R) : x - y = x + y :=
by rw [sub_eq_add_neg, char_two_neg]

lemma sq_map_add_char_two {ι R : Type*} [comm_ring R] [char_p R 2] (i : ι) (a b : ι → R) :
  sq i (a + b) = sq i a + sq i b :=
begin
  dsimp [sq],
  rw [add_mul, mul_add, mul_add, ←char_two_neg (b i * a i)],
  ring
end

lemma sq_map_sub_char_two {ι R : Type*} [comm_ring R] [char_p R 2] (i : ι) (a b : ι → R) :
  sq i (a - b) = sq i a - sq i b :=
begin
  haveI : nonempty ι := ⟨i⟩,
  rw [char_two_sub, char_two_sub, sq_map_add_char_two]
end

open_locale big_operators

def Q' : quadratic_form k (fin 3 → k) :=
∑ i, sq i


def Q'_add (x y : fin 3 → k) : Q' (x + y) = Q' x + Q' y :=
by simp only [Q', quadratic_form.sum_apply, sq_map_add_char_two, finset.sum_add_distrib]

def Q'_sub (x y : fin 3 → k) : Q' (x - y) = Q' x - Q' y :=
by simp only [Q', quadratic_form.sum_apply, sq_map_sub_char_two, finset.sum_sub_distrib]

lemma Q'_apply (a : fin 3 → k) : Q' a = a 0 * a 0 + a 1 * a 1 + a 2 * a 2 :=
calc Q' a = a 0 * a 0 + (a 1 * a 1 + (a 2 * a 2 + 0)) : rfl
      ... = _ : by ring

lemma sq_zero_of_αβγ_mul {x : k}  : α * β * γ * x = 0 → x*x = 0 :=
begin
  induction x using quotient.induction_on',
  change quotient.mk' _ = quotient.mk' _ → quotient.mk' _ = quotient.mk' _,
  rw [quotient.eq', quotient.eq'],
  dunfold submodule.quotient_rel setoid.r,
  dsimp,
  rw [sub_zero, sub_zero, k_ideal],
  intro h,
  sorry,
end

lemma Q'_zero_under_ideal (v : fin 3 → k) (hv : v ∈ L_func.ker) : Q' v = 0 := begin
  rw [linear_map.mem_ker, L_func_apply, char_two_sub, char_two_sub] at hv,
  have h0 : α * β * γ * v 0 = 0,
  { have := congr_arg ((*) (β * γ)) hv,
    simp only [mul_zero, mul_add, ←mul_assoc] at this,
    rw [mul_comm (β * γ) α, ←mul_assoc, mul_right_comm β γ β, mul_assoc β γ γ, X_sq, X_sq] at this,
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this },
  have h1 : α * β * γ * v 1 = 0,
  { have := congr_arg ((*) (α * γ)) hv,
    simp only [mul_zero, mul_add, ←mul_assoc] at this,
    rw [mul_right_comm α γ α, mul_assoc α γ γ, mul_right_comm α γ β, X_sq, X_sq] at this,
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this },
  have h2 : α * β * γ * v 2 = 0,
  { have := congr_arg ((*) (α * β)) hv,
    simp only [mul_zero, mul_add, ←mul_assoc] at this,
    rw [mul_right_comm α β α, mul_assoc α β β, X_sq, X_sq] at this,
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using this },
  rw [Q'_apply, sq_zero_of_αβγ_mul h0, sq_zero_of_αβγ_mul h1, sq_zero_of_αβγ_mul h2,
    add_zero, add_zero],
end

/-- The quadratic form (metric) is just euclidean -/
@[simps]
def Q : quadratic_form k L :=
{ to_fun := λ x, quotient.lift_on' x Q' $ λ a b h, begin
    dunfold submodule.quotient_rel setoid.r at h,
    suffices : Q' (a - b) = 0,
    { rwa [Q'_sub, sub_eq_zero] at this, },
    apply Q'_zero_under_ideal (a - b) h,
  end,
  to_fun_smul := λ a x, begin
    induction x using quotient.induction_on,
    exact Q'.to_fun_smul a x,
  end,
  polar_add_left' := by { rintros ⟨x⟩ ⟨x'⟩ ⟨y⟩, exact Q'.polar_add_left' x x' y },
  polar_smul_left' := by { rintros c ⟨x⟩ ⟨y⟩, exact Q'.polar_smul_left' c x y },
  polar_add_right' := by { rintros ⟨x⟩ ⟨y⟩ ⟨y'⟩, exact Q'.polar_add_right' x y y' },
  polar_smul_right' := by { rintros c ⟨x⟩ ⟨y⟩, exact Q'.polar_smul_right' c x y }, }

open clifford_algebra

/-! Shorthand for basis vectors in the cliford algebra -/
abbreviation x' : clifford_algebra Q := ι Q $ submodule.quotient.mk ![1, 0, 0]
abbreviation y' : clifford_algebra Q := ι Q $ submodule.quotient.mk ![0, 1, 0]
abbreviation z' : clifford_algebra Q := ι Q $ submodule.quotient.mk ![0, 0, 1]

/-- The basis vectors square to one -/
@[simp] lemma x_mul_x : x' * x' = 1 :=
begin
  dunfold x', simp, dsimp only [←submodule.quotient.mk'_eq_mk, quotient.lift_on'_mk'],
  simp [Q'_apply],
end

/-- By virtue of the quotient, terms of this form are zero -/
lemma quot_obv : α • x' - β • y' - γ • z' = 0 :=
begin
  dunfold x' y' z',
  simp only [←linear_map.map_smul, ←linear_map.map_sub, ←submodule.quotient.mk_smul, ←submodule.quotient.mk_sub],
  convert linear_map.map_zero _ using 2,
  apply quotient.sound',
  dunfold submodule.quotient_rel setoid.r,
  simp [sub_zero, ideal.span],
end

/-- The core of the proof - scaling `1` by `α * β * γ` gives zero -/
lemma αβγ_smul_eq_zero : (α * β * γ) • (1 : clifford_algebra Q) = 0 :=
begin
  suffices : α • 1 - β • (y' * x') - γ • (z' * x') = 0,
  { have := congr_arg (λ x, (β * γ) • x) this,
    simpa [smul_sub, smul_smul, mul_assoc β γ γ, mul_right_comm β γ β, mul_right_comm β γ α, mul_comm β α] using this,
  },
  have : (α • x' - β • y' - γ • z') * x' = α • 1 - β • (y' * x') - γ • (z' * x'),
  { simp [-Q_to_fun, sub_mul], },
  rw ← this,
  rw [quot_obv, zero_mul],
end

/-- Even though `α * β * γ` is not zero -/
lemma αβγ_ne_zero : α * β * γ ≠ 0 :=
begin
  intro h,
  replace h := quotient.exact' h,
  dunfold submodule.quotient_rel setoid.r at h,
  simp [sub_zero, ideal.span, k_ideal] at h,
  sorry,
end

/-- Our final result -/
lemma algebra_map_not_injective : ¬function.injective (algebra_map k $ clifford_algebra Q) :=
λ h, αβγ_ne_zero $ h begin
  rw [algebra.algebra_map_eq_smul_one, ring_hom.map_zero, αβγ_smul_eq_zero],
end

end q60596

-- open mv_polynomial

-- #print degree_of

-- example :
--   let s := ideal.span {x : mv_polynomial (fin 3) (zmod 2) | ∃ (i : fin 3), x = X i * X i} in
--   (X 0 * X 1 * X 2 : mv_polynomial (fin 3) (zmod 2)) ∉  s :=
-- begin
--   intros,
--   let s' := submodule.span (zmod 2) {x : mv_polynomial (fin 3) (zmod 2) | ∃ f r i, x = monomial f r ∧ 2 ≤ f i},
--   have hXii : ∀ i, (X i * X i : mv_polynomial (fin 3) (zmod 2)) = monomial (finsupp.single i 2) 1,
--   { intro i, simp [X], congr, sorry /- trivial -/},
--   have : ∀ x, x ∈ s ↔ x ∈ s',
--   begin
--     intro x,
--     split;
--     intro h,
--     { refine submodule.span_induction h _ s'.zero_mem (λ x y, s'.add_mem) _,
--       { rintros x ⟨i, rfl⟩,
--         refine submodule.subset_span ⟨finsupp.single i 2, 1, i, hXii i, le_of_eq _⟩,
--         simp, },
--       { rintros x y hy,
--         rw smul_eq_mul,
--         sorry -- tricky
--         },},
--     { refine submodule.span_induction h _ s.zero_mem (λ x y, s.add_mem) _,
--       { rintros x ⟨f, r, i, rfl, hx⟩,
--         have : monomial f r = monomial (f - finsupp.single i 2) r * monomial (finsupp.single i 2) 1 :=
--         begin
--           simp,
--           congr,
--           ext,
--           by_cases h : a = i; [simp [h], simp [finsupp.single_eq_of_ne (ne.symm h)]],
--           rw nat.sub_add_cancel hx,
--         end,
--         rw this,
--         refine s.mul_mem_left _ (submodule.subset_span ⟨i, (hXii i).symm⟩), },
--       { rintros x y hy,
--         rw algebra.smul_def,
--         exact s.mul_mem_left _ hy, }, },
--   end,
--   intro h,
--   rw this at h,
--   sorry,
-- end

-- variables {R : Type*} {σ : Type*} [comm_semiring R]

-- lemma degrees_mul_of_disjoint {p q : mv_polynomial σ R} (h : multiset.disjoint p.degrees q.degrees) :
--   (p * q).degrees = p.degrees + q.degrees :=
-- begin
--   apply le_antisymm,
--   { apply degrees_mul },
--   { apply multiset.add_le
--     { apply le_degrees_add h },
--     { rw add_comm, apply le_degrees_add h.symm } }
-- end

-- lemma foo {α β : Type*} [has_zero β] (a :α) (b : β) (h : b ≠ 0): (finsupp.single a b).support = {a} := finsupp.support_single_ne_zero h

-- lemma degrees_X (n : σ) [nontrivial R] : degrees (X n : mv_polynomial σ R) = {n} :=
-- (degrees_monomial_eq _ _ one_ne_zero).trans (finsupp.to_multiset_single _ _)

-- -- by simp [degrees, X, monomial, finsupp.support_single_ne_zero (one_ne_zero)]

-- #check finsupp.support_mul

-- def quotient.mk.alg {R : Type*} [comm_ring R] (I : ideal R) : R → I.quotient := begin
--   have := I.quotient.mk _,

-- end

-- •
