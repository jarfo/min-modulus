import MinModulus.AbelianMin

/-! The proper-subset SDR proposal fails already in dimension seven.
Two different six-element subsets can have the same sole anchored value.
This is a counterexample to the SDR proposal, not to the G2 modulus bound. -/
namespace MinModulus.Research
open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Values available to a subset when its anchor must lie outside it. -/
def anchoredSubsetValues {n N : ℕ} (g : Fin n → ZMod N)
    (S : Finset (Fin n)) : Finset (ZMod N) :=
  (univ \ S).image (fun k ↦ ∑ j ∈ S, (g j - g k))

/-- Distinct representatives for all proper subsets, with an external anchor. -/
def HasAnchoredSubsetSDR {n N : ℕ} (g : Fin n → ZMod N) : Prop :=
  ∃ f : {S : Finset (Fin n) // S ≠ univ} → ZMod N,
    Function.Injective f ∧ ∀ S, f S ∈ anchoredSubsetValues g S.val

def anchoredSDRSevenControl : Fin 7 → ZMod 329 := ![0,41,97,107,110,215,251]

private theorem anchoredSDRSevenControl_certificate :
    ∀ k ∈ Finset.Nat.antidiagonalTuple 7 7,
      (∑ i, k i • anchoredSDRSevenControl i) = (∑ i, anchoredSDRSevenControl i) →
      ∀ i, k i = 1 := by
  decide +kernel

/-- Full validity, checked over every multiplicity vector of total weight seven. -/
theorem anchoredSDRSevenControl_valid : ValidTuple anchoredSDRSevenControl := by
  intro k hcount hsum
  exact anchoredSDRSevenControl_certificate k
    (Finset.Nat.mem_antidiagonalTuple.mpr hcount) hsum

theorem anchoredSDRSevenControl_omit_four :
    anchoredSubsetValues anchoredSDRSevenControl (univ.erase 4) = {51} := by
  decide +kernel

theorem anchoredSDRSevenControl_omit_six :
    anchoredSubsetValues anchoredSDRSevenControl (univ.erase 6) = {51} := by
  decide +kernel

/-- Two distinct proper subsets have the same single available value. -/
theorem anchoredSDRSevenControl_no_sdr : ¬ HasAnchoredSubsetSDR anchoredSDRSevenControl := by
  rintro ⟨f, hf, hvalues⟩
  let S : {S : Finset (Fin 7) // S ≠ univ} := ⟨univ.erase 4, by decide⟩
  let T : {S : Finset (Fin 7) // S ≠ univ} := ⟨univ.erase 6, by decide⟩
  have hs : f S = 51 := by
    have h := hvalues S
    change f S ∈ anchoredSubsetValues anchoredSDRSevenControl (univ.erase 4) at h
    simpa only [anchoredSDRSevenControl_omit_four, mem_singleton] using h
  have ht : f T = 51 := by
    have h := hvalues T
    change f T ∈ anchoredSubsetValues anchoredSDRSevenControl (univ.erase 6) at h
    simpa only [anchoredSDRSevenControl_omit_six, mem_singleton] using h
  have he := congrArg Subtype.val (hf (hs.trans ht.symm))
  exact (by decide : (univ.erase (4 : Fin 7)) ≠ univ.erase 6) he

/-- Counterexample within the live dimension-seven-and-higher range. -/
theorem anchored_sdr_counterexample_seven :
    ∃ g : Fin 7 → ZMod 329, ValidTuple g ∧ ¬ HasAnchoredSubsetSDR g := by
  exact ⟨anchoredSDRSevenControl, anchoredSDRSevenControl_valid,
    anchoredSDRSevenControl_no_sdr⟩

end MinModulus.Research
