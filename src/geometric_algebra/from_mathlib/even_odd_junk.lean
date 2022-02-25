
#check 1

open_locale pointwise

lemma _root_.set.Union_mul {ι α} [has_mul α] (s : ι → set α) (t : set α) :
  (⋃ i, s i) * t = ⋃ i, (s i * t) :=
set.image2_Union_left _ _ _

lemma _root_.set.mul_Union {ι α} [has_mul α] (s : set α) (t : ι → set α) :
  s * (⋃ i, t i) = ⋃ i, (s * t i) :=
set.image2_Union_right _ _ _


lemma even_odd_mul_eq (i j : zmod 2) : even_odd Q i * even_odd Q j = even_odd Q (i + j) :=
begin
  simp_rw even_odd,
  simp_rw submodule.supr_eq_span,
  rw submodule.span_mul_span,
  congr' 1,
  simp_rw [set.mul_Union, set.Union_mul],
  sorry
end

#check zmod.val_add

lemma even_disjoint_odd : disjoint (even_odd Q 0) (even_odd Q 1) :=
begin
  rintro x ⟨he, ho⟩,
  simp only [even_odd, set_like.mem_coe] at *,
  rw submodule.mem_bot,
  haveI : fact (1 < 2) := ⟨one_lt_two⟩,
  simp_rw [zmod.val_one, pow_add, pow_one] at ho,
  simp_rw [zmod.val_zero, add_zero] at he,
  obtain ⟨fe, he⟩ := (submodule.mem_supr_iff_exists_dfinsupp _ _).mp he,
  obtain ⟨fo, ho⟩ := (submodule.mem_supr_iff_exists_dfinsupp _ _).mp ho,
  sorry,
  -- rw submodule.mem_inf,
end

lemma even_to_submodule_mul : (even Q).to_submodule * (ι Q).range = even_odd Q 1 :=
begin
  ext,
  simp [even_odd],
end

#exit

lemma even_odd_add (i j : zmod 2) : even_odd Q (i + j) = even_odd Q i * even_odd Q j :=
begin
  fin_cases i,
end

lemma even_is_compl_odd : is_compl (even_odd Q 0) (even_odd Q 1) :=
begin
  dunfold is_compl,
end

-- #check 1

-- lemma _root_.submodule.mul_supr {ι : Type*} {A : Type*} [semiring A] [algebra R A]
--   (s : ι → submodule R A) (t : submodule R A) :
--   t * (⨆ i, s i) = ⨆ i, (t * s i) :=
-- begin
--   dsimp [(*)],
--   rw supr_comm,
--   congr' 1,
--   ext tx: 1,
--   rw submodule.comap_supr
--   -- refine supr_subtype.trans _,
--   -- change _ = ⨆ i (x : subtype (∈ s i)), _,
--   -- simp_rw supr_subtype,
--   -- dsimp only [subtype.coe_mk],
--   -- rw supr_comm,
--   -- haveI := classical.dec_eq ι,
--   -- have := @submodule.mem_supr_iff_exists_dfinsupp ι R A _ _ _ _ s,
--   -- simp_rw this,
--   -- sorry,
--   -- simp,
--   -- simp_rw supr_subtype,
-- end

-- #exit


-- lemma _root_.submodule.supr_mul {ι : Type*} {A : Type*} [semiring A] [algebra R A]
--   (s : ι → submodule R A) (t : submodule R A) :
--   (⨆ i, s i) * t = ⨆ i, (s i * t) :=
-- begin
--   dsimp [(*)],
--   refine supr_subtype.trans _,
--   change _ = ⨆ i (x : subtype (∈ s i)), _,
--   simp_rw supr_subtype,
--   dsimp only [subtype.coe_mk],
--   rw supr_comm,
--   haveI := classical.dec_eq ι,
--   have := @submodule.mem_supr_iff_exists_dfinsupp ι R A _ _ _ _ s,
--   simp_rw this,
--   sorry,
--   -- simp,
--   -- simp_rw supr_subtype,
-- end


-- lemma _root_.submodule.mul_Union {ι α} [has_mul α] (s : submodule α) (t : ι → submodule α) :
--   s * (⋃ i, t i) = ⋃ i, (s * t i) :=
-- submodule.image2_Union_right _ _ _
