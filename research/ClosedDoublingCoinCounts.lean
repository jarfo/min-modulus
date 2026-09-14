import research.RepeatedCoinGrowth

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Every positive-degree coin value is an entry plus a lower-degree coin value. -/
theorem coinCover_succ_eq_coordinate_translates {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    actualFibreCoinCover g (k+1) = Finset.univ.biUnion
      (fun i ↦ (actualFibreCoinCover g k).image (fun x ↦ g i+x)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
    have hn : s ≠ 0 := by intro h; simp [h] at hc
    have hd : s=0 ∨ ∃ i t, s=i ::ₘ t :=
      Multiset.induction_on s (Or.inl rfl) (fun i t _ ↦ Or.inr ⟨i,t,rfl⟩)
    obtain ⟨i,t,rfl⟩ := hd.resolve_left hn
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨(t.map g).sum,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,by simpa using hc,rfl⟩
    · simpa using hs
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hi
    obtain ⟨t,hc,hs⟩ := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i ::ₘ t,by simp [hc],by simpa [hs] using he⟩

/-- If doubling the coordinate set is a translate of itself, the full repeated
cover is a translate of the previous coin cover, including every multiplicity. -/
theorem repeatedCoinCover_eq_previous_translate_of_doubling_image
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N)
    (hclosed : (Finset.univ.image (fun i ↦ 2 • g i)) =
      Finset.univ.image (fun i ↦ g i+b)) :
    repeatedCoinCover g (k+2) = (actualFibreCoinCover g (k+1)).image (fun x ↦ x+b) := by
  classical
  rw [repeatedCoinCover_eq_doubled_translates,coinCover_succ_eq_coordinate_translates]
  ext x
  constructor
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hi
    have hi : 2 • g i ∈ Finset.univ.image (fun j ↦ g j+b) := by
      rw [← hclosed]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hi
    refine Finset.mem_image.mpr ⟨g j+y,?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩
    · rw [← he,← hj]; abel
  · intro hx
    obtain ⟨z,hz,hzx⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hj
    have hj : g j+b ∈ Finset.univ.image (fun i ↦ 2 • g i) := by
      rw [hclosed]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,?_⟩⟩
    rw [hi,← hzx,← he]; abel

/-- Affine closure under doubling gives the full repeated-growth equality. -/
theorem repeatedCoinCover_card_eq_previous_of_doubling_image
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N)
    (hclosed : (Finset.univ.image (fun i ↦ 2 • g i)) =
      Finset.univ.image (fun i ↦ g i+b)) :
    (repeatedCoinCover g (k+2)).card = (actualFibreCoinCover g (k+1)).card := by
  classical
  rw [repeatedCoinCover_eq_previous_translate_of_doubling_image g b hclosed]
  exact Finset.card_image_of_injective _ (fun x y h ↦ add_right_cancel h)

/-- Every positive-degree coin cover in a valid affine-doubling-closed tuple
has the exact cumulative binomial size; no central-degree restriction is needed. -/
theorem coinCover_card_exact_of_doubling_image
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : (Finset.univ.image (fun i ↦ 2 • g i)) =
      Finset.univ.image (fun i ↦ g i+b)) (k : ℕ) :
    (actualFibreCoinCover g (k+1)).card+1 = ∑ j ∈ Finset.range (k+2), n.choose j := by
  induction k with
  | zero => simp [one_coin_card_eq g hg,Finset.sum_range_succ,add_comm]
  | succ k ih =>
    rw [coinCover_card_eq_choose_add_repeated g hg,
      repeatedCoinCover_card_eq_previous_of_doubling_image g b hclosed]
    rw [Finset.sum_range_succ]
    simp only [Nat.add_assoc,Nat.reduceAdd] at *
    omega

/-- The absolute repeated-cover target is attained exactly in every positive
degree for any valid tuple whose doubled coordinate set is a translate of itself. -/
theorem repeatedCoinCover_card_exact_of_doubling_image
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : (Finset.univ.image (fun i ↦ 2 • g i)) =
      Finset.univ.image (fun i ↦ g i+b)) (k : ℕ) :
    (repeatedCoinCover g (k+1)).card+1 = ∑ j ∈ Finset.range (k+1), n.choose j := by
  have h := coinCover_card_exact_of_doubling_image g hg b hclosed k
  rw [coinCover_card_eq_choose_add_repeated g hg,Finset.sum_range_succ] at h
  omega

end MinModulus.Research
