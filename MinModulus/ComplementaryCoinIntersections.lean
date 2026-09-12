import MinModulus.OddThreeSums

set_option autoImplicit false

/-! Exact intersections of complementary coin sumsets. -/
namespace MinModulus.Research
open Finset

/-- Sums of r distinct coordinates from a specified subset. -/
noncomputable def subsetCoinSums {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (S : Finset (Fin n)) (r : ℕ) : Finset (ZMod N) := by
  classical
  exact (S.powersetCard r).image (fun U ↦ ∑ i ∈ U, g i)

/-- Validity makes every fixed-size subset-sum parametrization injective. -/
theorem subsetCoinSums_card {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S : Finset (Fin n)) (r : ℕ) :
    (subsetCoinSums g S r).card = S.card.choose r := by
  classical
  dsimp [subsetCoinSums]
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard r S
  · intro U hU V hV he
    apply Finset.val_injective
    exact multiset_eq_finset_of_validTuple_card_sum g hg V U.val
      (by change U.card = V.card; rw [(mem_powersetCard.mp hU).2,
        (mem_powersetCard.mp hV).2]) he

/-- A split of the sum of a subset is forced to be a partition of that subset. -/
theorem coinCover_inter_reflection_eq {n N r s : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S : Finset (Fin n))
    (hsize : r+s = S.card) :
    actualFibreCoinCover g r ∩
      (actualFibreCoinCover g s).image (fun x ↦ (∑ i ∈ S, g i)-x) =
      subsetCoinSums g S r := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxr,hxs⟩ := Finset.mem_inter.mp hx
    obtain ⟨u,hu,huv⟩ := (Finset.mem_filter.mp hxr).2
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hxs
    obtain ⟨v,hv,hvv⟩ := (Finset.mem_filter.mp hy).2
    have huvS : u+v = S.val := by
      apply multiset_eq_finset_of_validTuple_card_sum g hg S (u+v)
      · simpa only [Multiset.card_add,hu,hv] using hsize
      · simp only [Multiset.map_add,Multiset.sum_add,huv,hvv]
        rw [← hyx]
        exact sub_add_cancel _ _
    have hule : u ≤ S.val := by rw [← huvS]; exact Multiset.le_add_right u v
    have hun : u.Nodup := Multiset.nodup_of_le hule S.nodup
    let U : Finset (Fin n) := ⟨u,hun⟩
    apply Finset.mem_image.mpr
    refine ⟨U,Finset.mem_powersetCard.mpr ⟨?_,hu⟩,huv⟩
    intro i hi
    exact Multiset.mem_of_le hule hi
  · intro hx
    obtain ⟨U,hU,hUx⟩ := Finset.mem_image.mp hx
    obtain ⟨hUS,hUr⟩ := Finset.mem_powersetCard.mp hU
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,U.val,hUr,hUx⟩
    · apply Finset.mem_image.mpr
      refine ⟨∑ i ∈ S\U, g i,?_,?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,(S\U).val,?_,rfl⟩
        change (S\U).card = s
        rw [Finset.card_sdiff_of_subset hUS,hUr,← hsize]
        omega
      · have hs := Finset.sum_sdiff hUS (f := g)
        rw [← hs,hUx]
        abel

/-- The intersection size is exactly a binomial coefficient. -/
theorem coinCover_inter_reflection_card {n N r s : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S : Finset (Fin n))
    (hsize : r+s = S.card) :
    (actualFibreCoinCover g r ∩
      (actualFibreCoinCover g s).image (fun x ↦ (∑ i ∈ S, g i)-x)).card =
      (r+s).choose r := by
  rw [coinCover_inter_reflection_eq g hg S hsize,subsetCoinSums_card g hg, hsize]

/-- Complementary coin sumsets fit in the group with exactly the prescribed overlap. -/
theorem coinCover_card_add_le_modulus_add_choose {n N r s : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsize : r+s ≤ n) :
    (actualFibreCoinCover g r).card + (actualFibreCoinCover g s).card ≤
      N + (r+s).choose r := by
  classical
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (show r+s ≤ (Finset.univ : Finset (Fin n)).card by simpa using hsize)
  let B := (actualFibreCoinCover g s).image (fun x ↦ (∑ i ∈ S, g i)-x)
  have hB : B.card = (actualFibreCoinCover g s).card :=
    Finset.card_image_of_injective _ (fun _ _ h ↦ sub_right_injective h)
  have hU : (actualFibreCoinCover g r ∪ B).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (actualFibreCoinCover g r ∪ B)
  have hI : (actualFibreCoinCover g r ∩ B).card = (r+s).choose r :=
    coinCover_inter_reflection_card g hg S hS.symm
  have h := Finset.card_union_add_card_inter (actualFibreCoinCover g r) B
  rw [hB,hI] at h
  omega

/-- A uniform cubic modulus bound, obtained from two reflected three-coin sumsets. -/
theorem twice_three_coin_lower_bound_le_modulus_add_twenty {n N : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (hn : 6 ≤ n) :
    2 * (n.choose 3 + (n+1).choose 2) ≤ N+20 := by
  have hC := choose_three_add_choose_two_le_three_coin_card hN g hg
  have hP := coinCover_card_add_le_modulus_add_choose (r := 3) (s := 3) g hg hn
  norm_num [Nat.choose] at hP
  omega

/-- Any valid seven-tuple at odd order has modulus at least 107. -/
theorem odd_modulus_ge_one_hundred_seven_of_valid_seven {N : ℕ}
    (hN : Odd N) (g : Fin 7 → ZMod N) (hg : ValidTuple g) : 107 ≤ N := by
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have h := twice_three_coin_lower_bound_le_modulus_add_twenty hN g hg (by decide)
  norm_num [Nat.choose] at h
  obtain ⟨k,hk⟩ := hN
  omega

/-- The remaining possible odd counterexample moduli in dimension seven. -/
theorem valid_seven_small_odd_modulus_cases {N : ℕ}
    (hN : Odd N) (g : Fin 7 → ZMod N) (hg : ValidTuple g) (hsmall : N < 127) :
    N = 107 ∨ N = 109 ∨ N = 111 ∨ N = 113 ∨ N = 115 ∨
      N = 117 ∨ N = 119 ∨ N = 121 ∨ N = 123 ∨ N = 125 := by
  have h := odd_modulus_ge_one_hundred_seven_of_valid_seven hN g hg
  obtain ⟨k,hk⟩ := hN
  omega

end MinModulus.Research
