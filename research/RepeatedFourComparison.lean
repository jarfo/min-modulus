import MinModulus.AbelianMin
import MinModulus.ActualFibreSumsetPacking

/-!
A valid odd-order tuple can have more three-coin sums than repeated
four-coin sums. This refutes a proposed comparison used to extend the
three-coin counting argument; it is not a counterexample to G2.
-/
namespace MinModulus.Research
open Finset

def repeatedFourControl : Fin 4 → ZMod 15 := ![0,11,8,6]

private theorem repeatedFourControl_bounded :
    ∀ k : Fin 4 → Fin 5, (∑ i, (k i).val)=4 →
      (∑ i, (k i).val • repeatedFourControl i)=(∑ i, repeatedFourControl i) →
      ∀ i, (k i).val=1 := by
  decide +kernel

theorem repeatedFourControl_valid : ValidTuple repeatedFourControl := by
  intro k hcount hsum
  have hb (i : Fin 4) : k i < 5 := by
    have h := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [hcount] at h
    omega
  exact repeatedFourControl_bounded (fun i ↦ ⟨k i,hb i⟩) hcount hsum

/-- Every four-coin sum containing a repeated index has this form. -/
def repeatedFourControlSums : Finset (ZMod 15) :=
  Finset.univ.image (fun t : Fin 3 → Fin 4 ↦
    2 • repeatedFourControl (t 0) + repeatedFourControl (t 1) + repeatedFourControl (t 2))

theorem repeatedFourControlSums_card : repeatedFourControlSums.card=14 := by
  decide +kernel

theorem repeatedFourControl_three_coin_full :
    actualFibreCoinCover repeatedFourControl 3=Finset.univ := by
  have h : ∀ x : ZMod 15, ∃ i j k : Fin 4,
      repeatedFourControl i+repeatedFourControl j+repeatedFourControl k=x := by
    decide +kernel
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨i,j,k,hijk⟩ := h x
  simp only [actualFibreCoinCover, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨i ::ₘ j ::ₘ {k}, by simp, ?_⟩
  simpa only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
    Multiset.sum_singleton, add_assoc] using hijk

theorem repeatedFourControl_three_coin_card :
    (actualFibreCoinCover repeatedFourControl 3).card=15 := by
  rw [repeatedFourControl_three_coin_full]
  decide

theorem repeatedFourControl_comparison_fails :
    ¬ (actualFibreCoinCover repeatedFourControl 3).card ≤ repeatedFourControlSums.card := by
  rw [repeatedFourControl_three_coin_card, repeatedFourControlSums_card]
  omega

end MinModulus.Research
