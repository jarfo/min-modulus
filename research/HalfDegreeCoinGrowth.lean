import research.ComplementaryCoinIntersections
import MinModulus.GlobalRoadmap

set_option autoImplicit false

/-! A conditional route to the full odd-stratum bound using only half the coin degrees. -/
namespace MinModulus.Research
open Finset

/-- The growth needed between positive coin degrees up to half the tuple length. -/
def HalfDegreeCoinGrowth {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 * (k+1) ≤ n+1 →
    (actualFibreCoinCover g k).card + n.choose (k+1) ≤
      (actualFibreCoinCover g (k+1)).card

/-- Every squarefree coin sum is a coin sum of the same degree. -/
theorem subsetCoinSums_subset_coinCover {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (S : Finset (Fin n)) :
    subsetCoinSums g S k ⊆ actualFibreCoinCover g k := by
  classical
  intro x hx
  obtain ⟨U,hU,hUx⟩ := Finset.mem_image.mp hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,U.val,(Finset.mem_powersetCard.mp hU).2,hUx⟩

/-- Validity supplies the binomial number of squarefree sums at each degree. -/
theorem choose_le_coinCover_card {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    n.choose k ≤ (actualFibreCoinCover g k).card := by
  classical
  have h := Finset.card_le_card
    (subsetCoinSums_subset_coinCover (k := k) g Finset.univ)
  rw [subsetCoinSums_card g hg] at h
  simpa using h

/-- Complementary partial rows of Pascal's triangle overlap at one coefficient. -/
theorem complementary_partial_choose_sums (r s : ℕ) :
    (∑ j ∈ Finset.range (r+1), (r+s).choose j) +
      (∑ j ∈ Finset.range (s+1), (r+s).choose j) =
      2^(r+s) + (r+s).choose r := by
  have hsym :
      (∑ j ∈ Finset.range s, (r+s).choose ((r+s)-j)) =
        ∑ j ∈ Finset.range s, (r+s).choose j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.choose_symm (by have := Finset.mem_range.mp hj; omega)
  have htail :
      (∑ j ∈ Finset.Ico (r+1) (r+s+1), (r+s).choose j) =
        ∑ j ∈ Finset.range s, (r+s).choose j := by
    calc
      _ = ∑ j ∈ Finset.Ico 0 s, (r+s).choose ((r+s)-j) := by
        have h := Finset.sum_Ico_reflect (fun j ↦ (r+s).choose j) 0
          (m := s) (n := r+s) (by omega)
        have he : r+s+1-s=r+1 := by omega
        simpa only [he,Nat.sub_zero] using h.symm
      _ = _ := by simpa using hsym
  have hfull := Finset.sum_range_add_sum_Ico
    (fun j ↦ (r+s).choose j) (by omega : r+1 ≤ r+s+1)
  rw [htail,Nat.sum_range_choose] at hfull
  have hlast := Finset.sum_range_succ (fun j ↦ (r+s).choose j) s
  have hc : (r+s).choose s = (r+s).choose r := by
    have h := Nat.choose_symm (by omega : r ≤ r+s)
    simpa using h
  rw [hc] at hlast
  omega

/-- The assumed growth yields the cumulative binomial bound at every required degree. -/
theorem partial_choose_sum_le_coinCover_card_add_one {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hGrowth : HalfDegreeCoinGrowth g) :
    ∀ k : ℕ, 1 ≤ k → 2*k ≤ n+1 →
      (∑ j ∈ Finset.range (k+1), n.choose j) ≤
        (actualFibreCoinCover g k).card+1 := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hhalf
    cases k with
    | zero =>
      have h := choose_le_coinCover_card (k := 1) g hg
      simp [Finset.sum_range_succ, Nat.choose] at h ⊢
      omega
    | succ j =>
      have hp := ih (by omega) (by omega)
      have hs := hGrowth (j+1) (by omega) hhalf
      rw [Finset.sum_range_succ]
      simp only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.reduceAdd] at hp hs ⊢
      omega

/-- Balanced complementary coin degrees already imply the sharp odd bound. -/
theorem odd_modulus_lower_bound_of_halfDegreeCoinGrowth
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hGrowth : HalfDegreeCoinGrowth g) :
    2^n-1 ≤ N := by
  let r := n/2
  let s := n-r
  have hrs : r+s=n := by dsimp [r,s]; omega
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : 1 ≤ s := by dsimp [r,s]; omega
  have hhr : 2*r ≤ n+1 := by dsimp [r]; omega
  have hhs : 2*s ≤ n+1 := by dsimp [r,s]; omega
  have hCr := partial_choose_sum_le_coinCover_card_add_one g hg hGrowth r hr hhr
  have hCs := partial_choose_sum_le_coinCover_card_add_one g hg hGrowth s hs hhs
  have hP := coinCover_card_add_le_modulus_add_choose (r := r) (s := s) g hg (by omega)
  have hB := complementary_partial_choose_sums r s
  rw [hrs] at hB hP
  have hp : 2^n ≤ N+2 := by omega
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ] at hp
  obtain ⟨q,hq⟩ := hN
  omega

/-- A proof of half-degree growth for every valid odd tuple would prove all of G2. -/
theorem oddStratumLowerBound_of_halfDegreeCoinGrowth
    (hGrowth : ∀ {n N : ℕ} [NeZero N], Odd N →
      ∀ g : Fin n → ZMod N, ValidTuple g → HalfDegreeCoinGrowth g) :
    OddStratumLowerBound := by
  intro n N hN hv
  obtain ⟨g,hg⟩ := hv
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  by_cases hn : 2 ≤ n
  · exact odd_modulus_lower_bound_of_halfDegreeCoinGrowth hn hN g hg (hGrowth hN g hg)
  · have hcases : n=0 ∨ n=1 := by omega
    rcases hcases with rfl | rfl
    · simp
    · have h := hN.pos
      norm_num
      omega

end MinModulus.Research
