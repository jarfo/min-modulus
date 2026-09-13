import research.QuadraticOneEscapeTransfer

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Once an outside quadratic translate has four hits, its hit count equals
that of forward affine doubling with offset minus the translate. -/
theorem quadratic_hit_card_eq_affine_hit_card_of_four_hits
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) (hfour : 4 ≤ (quadraticTranslateHits g t).card) :
    (quadraticTranslateHits g t).card =
      (Finset.univ.filter (fun j ↦ ∃ i, g i=2 • g j-t)).card := by
  classical
  let H := quadraticTranslateHits g t
  let F := Finset.univ.filter (fun j ↦ ∃ i, g i=2 • g j-t)
  have hex (i : Fin n) : ∃ j : Fin n, i ∈ H → g i+t=2 • g j := by
    by_cases hi : i ∈ H
    · obtain ⟨j,hj⟩ := quadratic_translate_hit_is_double_of_four_hits g hg t ht hfour
        i (Finset.mem_filter.mp hi).2
      exact ⟨j,fun _ ↦ hj⟩
    · exact ⟨i,fun hh ↦ (hi hh).elim⟩
  let f : Fin n → Fin n := fun i ↦ Classical.choose (hex i)
  have hf (i : Fin n) (hi : i ∈ H) : g i+t=2 • g (f i) := Classical.choose_spec (hex i) hi
  have hinj : Set.InjOn f H := by
    intro i hi j hj he
    apply validTuple_injective g hg
    apply add_right_cancel (b := t)
    rw [hf i hi,hf j hj,he]
  have heq : H.image f=F := by
    ext j
    constructor
    · intro hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,eq_sub_of_add_eq (hf i hi)⟩
    · intro hj
      obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hj).2
      have hv : g i+t=2 • g j := eq_sub_iff_add_eq.mp hi
      have hiH : i ∈ H := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          j ::ₘ j ::ₘ (0 : Multiset (Fin n)),by simp,?_⟩⟩
        simpa only [Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,
          Multiset.sum_zero,add_zero,two_nsmul] using hv.symm
      have hfj : f i=j := by
        apply validTuple_injective g hg
        apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
        have hdouble := (hf i hiH).symm.trans hv
        simpa only [nsmul_eq_mul,Nat.cast_ofNat] using hdouble
      exact Finset.mem_image.mpr ⟨i,hiH,hfj⟩
  change H.card=F.card
  rw [← heq,Finset.card_image_of_injOn hinj]

/-- Every outside quadratic translate has at least the smaller of n-3
and the number of forward affine-doubling escapes. This holds uniformly
in the tuple length, including translates with fewer than four hits. -/
theorem quadratic_escape_count_ge_min_affine_escapes
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : ∀ i, t ≠ g i) :
    min (n-3) (Finset.univ.filter (fun j ↦ ¬ ∃ i, g i=2 • g j-t)).card ≤
      n-(quadraticTranslateHits g t).card := by
  classical
  by_cases hfour : 4 ≤ (quadraticTranslateHits g t).card
  · have heq := quadratic_hit_card_eq_affine_hit_card_of_four_hits hN g hg t ht hfour
    have htotal := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun j ↦ ∃ i, g i=2 • g j-t)
    simp only [Finset.card_univ,Fintype.card_fin] at htotal
    have hle := Nat.min_le_right (n-3)
      (Finset.univ.filter (fun j ↦ ¬ ∃ i, g i=2 • g j-t)).card
    omega
  · have hle := Nat.min_le_left (n-3)
      (Finset.univ.filter (fun j ↦ ¬ ∃ i, g i=2 • g j-t)).card
    omega

end MinModulus.Research
