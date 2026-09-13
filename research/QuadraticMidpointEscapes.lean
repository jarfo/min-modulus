import research.QuadraticTranslateRigidity

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A midpoint of distinct coordinates has at most three quadratic hits.
No parity or near-extremal modulus assumption is needed for this statement. -/
theorem quadratic_midpoint_hits_le_three {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b c : Fin n) (hbc : b ≠ c)
    (t : ZMod N) (ht : 2 • t = g b + g c) :
    (quadraticTranslateHits g t).card ≤ 3 := by
  classical
  have hout : ∀ i, t ≠ g i := by
    intro i hi
    have he : g b+g c=g i+g i := by simpa only [hi,two_nsmul] using ht.symm
    rcases pair_sum_eq_or_diagonal_of_validTuple g hg b c i i he with h | ⟨h,_⟩
    · rcases h with ⟨hb,hc⟩ | ⟨hb,hc⟩ <;> exact hbc (hb.trans hc.symm)
    · exact hbc h
  by_contra h
  have hfour : 4 ≤ (quadraticTranslateHits g t).card := by omega
  let K := quadraticTranslateHits g t \ {b,c}
  have hK : 1 < K.card := by
    have hsum := Finset.card_sdiff_add_card_inter (quadraticTranslateHits g t) {b,c}
    have hle := Finset.card_le_card (Finset.inter_subset_right :
      quadraticTranslateHits g t ∩ {b,c} ⊆ ({b,c} : Finset (Fin n)))
    rw [Finset.card_pair hbc] at hle
    dsimp only [K]
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hK
  have hiH := (Finset.mem_sdiff.mp hi).1
  have hjH := (Finset.mem_sdiff.mp hj).1
  have hibc := (Finset.mem_sdiff.mp hi).2
  have hjbc := (Finset.mem_sdiff.mp hj).2
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hibc hjbc
  obtain ⟨a,ha⟩ := quadratic_translate_hit_is_double_of_four_hits g hg t hout hfour i
    (Finset.mem_filter.mp hiH).2
  obtain ⟨d,hd⟩ := quadratic_translate_hit_is_double_of_four_hits g hg t hout hfour j
    (Finset.mem_filter.mp hjH).2
  let S : Finset (Fin n) := {i,j,b,c}
  have hsum : g a+g a+(g d+g d)=g i+g j+(g b+g c) := by
    simp only [two_nsmul] at ha hd ht
    linear_combination -ha - hd + ht
  have he : (a ::ₘ a ::ₘ d ::ₘ ({d} : Multiset (Fin n))) = S.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg S _
    · simp [S,hij,hibc.1,hibc.2,hjbc.1,hjbc.2,hbc]
    · simpa [S,hij,hibc.1,hibc.2,hjbc.1,hjbc.2,hbc,add_assoc] using hsum
  have hnot : ¬ (a ::ₘ a ::ₘ d ::ₘ ({d} : Multiset (Fin n))).Nodup := by simp
  rw [he] at hnot
  exact hnot S.nodup

/-- At odd order, each distinct coordinate pair has at least n-3 anchors
whose repeated quartic value escapes the doubled two-coin cover. -/
theorem repeated_quartic_escape_count_ge_pred_three {n N : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b c : Fin n) (hbc : b ≠ c) :
    n-3 ≤ (Finset.univ.filter (fun a : Fin n ↦
      2 • g a+g b+g c ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x))).card := by
  classical
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro x y h
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using h
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective hd) (g b+g c)
  change 2 • t=g b+g c at ht
  have hmem (a : Fin n) :
      2 • g a+g b+g c ∈ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x) ↔
        g a+t ∈ actualFibreCoinCover g 2 := by
    have he : 2 • (g a+t)=2 • g a+g b+g c := by rw [nsmul_add,ht,add_assoc]
    rw [← he]
    exact Finset.mem_image.trans ⟨fun ⟨y,hy,he⟩ ↦ hd he ▸ hy,
      fun hy ↦ ⟨g a+t,hy,rfl⟩⟩
  have heq : Finset.univ.filter (fun a : Fin n ↦
      2 • g a+g b+g c ∉ (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)) =
      Finset.univ \ quadraticTranslateHits g t := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
      quadraticTranslateHits,hmem]
  rw [heq,Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,Fintype.card_fin]
  have hh := quadratic_midpoint_hits_le_three g hg b c hbc t ht
  omega

end MinModulus.Research
