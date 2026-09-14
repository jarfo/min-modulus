import research.ClosedDoublingCoinCounts
import MinModulus.CycleThinCover
import MinModulus.UniqueSums
import MinModulus.G1OddPrimarySingletonComplement

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- The coordinate set of every positive-length Mersenne power tuple is fixed
by doubling, including the cyclic last-to-first carry. -/
theorem mersenne_doubled_coordinate_image (n : ℕ) (hn : 1 ≤ n) [NeZero (2^n-1)] :
    let g : Fin n → ZMod (2^n-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^n-1))
    (Finset.univ.image (fun i ↦ 2 • g i)) = Finset.univ.image g := by
  classical
  dsimp only
  let g : Fin n → ZMod (2^n-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^n-1))
  have hsub : Finset.univ.image g ⊆ Finset.univ.image (fun i ↦ 2 • g i) := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj⟩ := mersenne_power_doubling_predecessor (by omega : 0 < n) i
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
  have hc : (Finset.univ.image (fun i ↦ 2 • g i)).card ≤ (Finset.univ.image g).card := by
    have he : Finset.univ.image (fun i ↦ 2 • g i) =
        (Finset.univ.image g).image (fun x ↦ 2 • x) := by simp only [Finset.image_image,Function.comp_def]
    rw [he]
    exact Finset.card_image_le
  exact (Finset.eq_of_subset_of_card_le hsub hc).symm

/-- The valid sharp Mersenne family attains the full cumulative binomial
coin-cover and repeated-cover counts at every positive degree. -/
theorem mersenne_exact_coin_and_repeated_counts
    (n : ℕ) (hn : 1 ≤ n) [NeZero (2^n-1)] :
    let g : Fin n → ZMod (2^n-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^n-1))
    ValidTuple g ∧ ∀ k : ℕ,
      ((actualFibreCoinCover g (k+1)).card+1 = ∑ j ∈ Finset.range (k+2), n.choose j) ∧
      ((repeatedCoinCover g (k+1)).card+1 = ∑ j ∈ Finset.range (k+1), n.choose j) := by
  classical
  dsimp only
  let g : Fin n → ZMod (2^n-1) := fun i ↦ ((2^i.val : ℕ) : ZMod (2^n-1))
  have hg : ValidTuple g := by
    by_cases hn2 : 2 ≤ n
    ·
      have hbase : ValidTuple (fun i : Fin n ↦ (a i.val : ZMod (2^n-1))) :=
        validTuple_fixed_of_valid (by
          simpa using valid_gap (n:=n) (t:=0) hn2 (by simpa using hn))
      have ht := validTuple_sub_const _ hbase (-1)
      have hp (i : Fin n) : (a i.val : ZMod (2^n-1))-(-1)=g i := by
        rw [a,Nat.cast_sub Nat.one_le_two_pow,Nat.cast_one]
        dsimp only [g]
        abel
      simpa only [hp] using ht
    · have hn1 : n=1 := by omega
      subst n
      intro c hc _ i
      fin_cases i
      simpa using hc
  have hc : Finset.univ.image (fun i ↦ 2 • g i) = Finset.univ.image (fun i ↦ g i+0) := by
    simpa only [add_zero] using mersenne_doubled_coordinate_image n hn
  exact ⟨hg,fun k ↦ ⟨coinCover_card_exact_of_doubling_image g hg 0 hc k,
    repeatedCoinCover_card_exact_of_doubling_image g hg 0 hc k⟩⟩

end MinModulus.Research
