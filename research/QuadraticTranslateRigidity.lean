import research.RepeatedCoinGrowth

set_option autoImplicit false

/-! Outside translates of the quadratic coin cover force affine doubling. -/
namespace MinModulus.Research
open Finset

/-- Coordinates whose translate is a two-coin sum. -/
noncomputable def quadraticTranslateHits {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (t : ZMod N) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ g i+t ∈ actualFibreCoinCover g 2)

/-- One squarefree representation of an outside translate confines every hit
to its three involved coordinates. -/
theorem quadratic_translate_hit_mem_triple {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) (j b c : Fin n) (hbc : b ≠ c)
    (he : g j+t=g b+g c) (a : Fin n)
    (ha : g a+t ∈ actualFibreCoinCover g 2) : a ∈ ({j,b,c} : Finset (Fin n)) := by
  classical
  have hjb : j ≠ b := by
    intro h
    subst b
    exact ht c (add_left_cancel he)
  have hjc : j ≠ c := by
    intro h
    subst c
    exact ht b (add_left_cancel (he.trans (add_comm _ _)))
  by_contra hnot
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hnot
  obtain ⟨haj,hab,hac⟩ := hnot
  obtain ⟨s,hs,hsv⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨u,v,rfl⟩ := Multiset.card_eq_two.mp hs
  have he' : g a+t=g u+g v := by simpa using hsv.symm
  let S : Finset (Fin n) := {a,b,c}
  have hsum : g j+g u+g v=g a+g b+g c := by linear_combination he - he'
  have hm : (j ::ₘ u ::ₘ ({v} : Multiset (Fin n)))=S.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg S _
    · simp [S,hab,hac,hbc]
    · simpa [S,hab,hac,hbc,add_assoc] using hsum
  have hj : j ∈ S.val := by rw [← hm]; simp
  change j ∈ S at hj
  simpa [S,Ne.symm haj,hjb,hjc] using hj

/-- A squarefree hit permits at most three translated coordinates in C_2. -/
theorem quadratic_translate_hits_le_three_of_squarefree_hit {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) (j b c : Fin n) (hbc : b ≠ c)
    (he : g j+t=g b+g c) : (quadraticTranslateHits g t).card ≤ 3 := by
  classical
  have hh : quadraticTranslateHits g t ⊆ ({j,b,c} : Finset (Fin n)) := by
    intro a ha
    exact quadratic_translate_hit_mem_triple g hg t ht j b c hbc he a
      (Finset.mem_filter.mp ha).2
  have hc := Finset.card_le_card hh
  have h1 := Finset.card_insert_le j ({b,c} : Finset (Fin n))
  have h2 := Finset.card_insert_le b ({c} : Finset (Fin n))
  simp only [Finset.card_singleton] at h2
  omega

/-- Four translated hits force each of them to be a doubled coordinate. -/
theorem quadratic_translate_hit_is_double_of_four_hits {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) (hfour : 4 ≤ (quadraticTranslateHits g t).card)
    (a : Fin n) (ha : g a+t ∈ actualFibreCoinCover g 2) :
    ∃ b : Fin n, g a+t=2 • g b := by
  classical
  obtain ⟨s,hs,hsv⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨b,c,rfl⟩ := Multiset.card_eq_two.mp hs
  have he : g a+t=g b+g c := by simpa using hsv.symm
  by_cases hbc : b=c
  · subst c
    exact ⟨b,by simpa only [two_nsmul] using he⟩
  · have hc := quadratic_translate_hits_le_three_of_squarefree_hit g hg t ht a b c hbc he
    omega

/-- A complete outside translate of C_1 inside C_2 is a cover by doubles. -/
theorem double_cover_of_full_quadratic_translate {n N : ℕ} [NeZero N]
    (hn : 4 ≤ n) (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) (hcover : ∀ i, g i+t ∈ actualFibreCoinCover g 2) :
    ∀ i, ∃ j, g i+t=2 • g j := by
  classical
  have he : quadraticTranslateHits g t=Finset.univ := by
    ext i
    simp [quadraticTranslateHits,hcover]
  have hf : 4 ≤ (quadraticTranslateHits g t).card := by simpa [he] using hn
  intro i
  exact quadratic_translate_hit_is_double_of_four_hits g hg t ht hf i (hcover i)

/-- A cover by doubles gives the repeated-sum inequality in every positive degree. -/
theorem repeated_coin_growth_of_double_cover {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (t : ZMod N)
    (hcover : ∀ i, ∃ j, g i+t=2 • g j) :
    (actualFibreCoinCover g (k+1)).card ≤ (repeatedCoinCover g (k+2)).card := by
  classical
  have hsub : (actualFibreCoinCover g (k+1)).image (fun x ↦ x+t) ⊆
      repeatedCoinCover g (k+2) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s,hs,hsy⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨i,hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < s.card)
    obtain ⟨r,rfl⟩ := Multiset.exists_cons_of_mem hi
    obtain ⟨j,hj⟩ := hcover i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,j ::ₘ j ::ₘ r,?_,?_,by simp⟩
    · simp only [Multiset.card_cons] at hs ⊢
      omega
    · simp only [Multiset.map_cons,Multiset.sum_cons] at hsy ⊢
      rw [← add_assoc,← two_nsmul,← hj]
      rw [← hsy]
      abel
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ (fun _ _ h ↦ add_right_cancel h)] at hc

/-- Complete outside quadratic translation already proves the sharp odd bound. -/
theorem odd_lower_bound_of_full_quadratic_translate {n N : ℕ} [NeZero N]
    (hn : 4 ≤ n) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : ∀ i, t ≠ g i)
    (hcover : ∀ i, g i+t ∈ actualFibreCoinCover g 2) : 2^n-1 ≤ N := by
  have hd := double_cover_of_full_quadratic_translate hn g hg t ht hcover
  have hh : HigherRepeatedCoinGrowth g := by
    intro k _ _
    exact repeated_coin_growth_of_double_cover g t hd
  exact odd_modulus_lower_bound_of_halfDegreeCoinGrowth (by omega) hN g hg
    ((halfDegreeCoinGrowth_iff_higherRepeatedCoinGrowth hN g hg).mpr hh)

/-- In a hypothetical odd counterexample, every outside translate misses C_2. -/
theorem exists_quadratic_translate_escape_of_odd_counterexample {n N : ℕ} [NeZero N]
    (hn : 4 ≤ n) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2^n-1) (t : ZMod N) (ht : ∀ i, t ≠ g i) :
    ∃ i, g i+t ∉ actualFibreCoinCover g 2 := by
  by_contra h
  push Not at h
  have hb := odd_lower_bound_of_full_quadratic_translate hn hN g hg t ht h
  omega

/-- Every distinct pair in a hypothetical counterexample has a repeated quartic
sum outside the doubled two-coin baseline. -/
theorem exists_repeated_quartic_outside_doubled_pairs {n N : ℕ} [NeZero N]
    (hn : 4 ≤ n) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2^n-1) (b c : Fin n) (hbc : b ≠ c) :
    ∃ a, 2 • g a+g b+g c ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x) := by
  classical
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro x y h
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using h
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective hd) (g b+g c)
  change 2 • t=g b+g c at ht
  have hout : ∀ i, t ≠ g i := by
    intro i hi
    have he : g b+g c=g i+g i := by simpa only [hi,two_nsmul] using ht.symm
    rcases pair_sum_eq_or_diagonal_of_validTuple g hg b c i i he with h | ⟨h,_⟩
    · rcases h with ⟨hb,hc⟩ | ⟨hb,hc⟩ <;> exact hbc (hb.trans hc.symm)
    · exact hbc h
  obtain ⟨a,ha⟩ := exists_quadratic_translate_escape_of_odd_counterexample hn hN g hg hsmall t hout
  refine ⟨a,?_⟩
  intro h
  obtain ⟨y,hy,hey⟩ := Finset.mem_image.mp h
  have he : g a+t=y := hd (by
    change 2 • (g a+t)=2 • y
    rw [nsmul_add,ht]
    simpa only [add_assoc] using hey.symm)
  exact ha (he.symm ▸ hy)

end MinModulus.Research
