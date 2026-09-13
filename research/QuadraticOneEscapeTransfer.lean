import research.QuadraticTranslateRigidity

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A subset missing at most one coordinate contains every coordinate except
one specified exception; this also covers the full subset. -/
theorem exists_exception_of_large_index_set {n : ℕ} (hn : 0 < n)
    (B : Finset (Fin n)) (hB : n-1 ≤ B.card) :
    ∃ a : Fin n, ∀ i, i ≠ a → i ∈ B := by
  classical
  have hc : (Finset.univ \ B).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  by_cases h : ∃ a, a ∉ B
  · obtain ⟨a,ha⟩ := h
    refine ⟨a,fun i hia ↦ ?_⟩
    by_contra hi
    exact hia ((Finset.card_le_one.mp hc) i
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩) a
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩))
  · push Not at h
    exact ⟨⟨0,hn⟩,fun i _ ↦ h i⟩

/-- At least n-1 hits of an outside quadratic translate, for n>=5, give
one-escape affine doubling closure in the forward direction. -/
theorem one_escape_of_large_quadratic_translate {n N : ℕ} [NeZero N]
    (hn : 5 ≤ n) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : ∀ i, t ≠ g i)
    (hlarge : n-1 ≤ (quadraticTranslateHits g t).card) :
    ∃ a : Fin n, ∀ i, i ≠ a → ∃ j, g j=2 • g i-t := by
  classical
  let H := quadraticTranslateHits g t
  have hex (i : Fin n) : ∃ j : Fin n, i ∈ H → g i+t=2 • g j := by
    by_cases hi : i ∈ H
    · obtain ⟨j,hj⟩ := quadratic_translate_hit_is_double_of_four_hits g hg t ht
        (by omega) i (Finset.mem_filter.mp hi).2
      exact ⟨j,fun _ ↦ hj⟩
    · exact ⟨i,fun hh ↦ (hi hh).elim⟩
  let f : Fin n → Fin n := fun i ↦ Classical.choose (hex i)
  have hf (i : Fin n) (hi : i ∈ H) : g i+t=2 • g (f i) :=
    Classical.choose_spec (hex i) hi
  have hinj : Set.InjOn f H := by
    intro i hi j hj he
    apply validTuple_injective g hg
    apply add_right_cancel (b := t)
    rw [hf i hi,hf j hj,he]
  have hc : n-1 ≤ (H.image f).card := by
    rw [Finset.card_image_iff.mpr hinj]
    exact hlarge
  obtain ⟨a,ha⟩ := exists_exception_of_large_index_set (by omega) (H.image f) hc
  refine ⟨a,fun i hia ↦ ?_⟩
  obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp (ha i hia)
  refine ⟨j,?_⟩
  have he := hf j hj
  rw [hji] at he
  exact eq_sub_of_add_eq he

/-- Excluding one-escape affine closure at the corresponding offset forces
at least two quadratic-translate escapes. The exclusion remains explicit. -/
theorem two_quadratic_escapes_of_one_escape_exclusion {n N : ℕ} [NeZero N]
    (hn : 5 ≤ n) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : ∀ i, t ≠ g i)
    (hno : ∀ a : Fin n, ¬ (∀ i, i ≠ a → ∃ j, g j=2 • g i-t)) :
    ∃ i j : Fin n, i ≠ j ∧ g i+t ∉ actualFibreCoinCover g 2 ∧
      g j+t ∉ actualFibreCoinCover g 2 := by
  classical
  have hsmall : (quadraticTranslateHits g t).card < n-1 := by
    by_contra h
    obtain ⟨a,ha⟩ := one_escape_of_large_quadratic_translate hn g hg t ht (by omega)
    exact hno a ha
  have hc : 1 < (Finset.univ \ quadraticTranslateHits g t).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  refine ⟨i,j,hij,?_,?_⟩
  · simpa [quadraticTranslateHits] using (Finset.mem_sdiff.mp hi).2
  · simpa [quadraticTranslateHits] using (Finset.mem_sdiff.mp hj).2

end MinModulus.Research
