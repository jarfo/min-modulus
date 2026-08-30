/-
# Normalized five-coordinate SHC exclusions

The first strict-window case, order 33, follows analytically from the bottom
wedge.  The remaining cases are generated certificates: their shards cover
every sorted normalized tuple by a subset-sum collision or a head-2 relation,
with all coverage checks reduced by Lean's kernel.
-/
import MinModulus.Generated.SHCFiveN35
import MinModulus.Generated.SHCFiveN37
import MinModulus.Generated.SHCFiveN39
import MinModulus.Generated.SHCFiveN41
import MinModulus.Generated.SHCFiveN43
import MinModulus.Generated.SHCFiveN45
import MinModulus.Generated.SHCFiveN47
import MinModulus.Generated.SHCFiveN49
import MinModulus.Generated.SHCFiveN51
import MinModulus.Generated.SHCFiveN53
import MinModulus.Generated.SHCFiveN55
import MinModulus.Generated.SHCFiveN57
import MinModulus.Generated.SHCFiveN59
import MinModulus.Generated.SHCFiveN61

namespace MinModulus

open SHCFiveCertificate

/-- There is no normalized five-coordinate SHC family in `ZMod 35`. -/
theorem normalized_shc_five_excluded_thirty_five : NormalizedSHCExcluded 4 35 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate35

/-- There is no normalized five-coordinate SHC family in `ZMod 37`. -/
theorem normalized_shc_five_excluded_thirty_seven : NormalizedSHCExcluded 4 37 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate37

/-- There is no normalized five-coordinate SHC family in `ZMod 39`. -/
theorem normalized_shc_five_excluded_thirty_nine : NormalizedSHCExcluded 4 39 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate39

/-- There is no normalized five-coordinate SHC family in `ZMod 41`. -/
theorem normalized_shc_five_excluded_forty_one : NormalizedSHCExcluded 4 41 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate41

/-- There is no normalized five-coordinate SHC family in `ZMod 43`. -/
theorem normalized_shc_five_excluded_forty_three : NormalizedSHCExcluded 4 43 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate43

/-- There is no normalized five-coordinate SHC family in `ZMod 45`. -/
theorem normalized_shc_five_excluded_forty_five : NormalizedSHCExcluded 4 45 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate45

/-- There is no normalized five-coordinate SHC family in `ZMod 47`. -/
theorem normalized_shc_five_excluded_forty_seven : NormalizedSHCExcluded 4 47 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate47

/-- There is no normalized five-coordinate SHC family in `ZMod 49`. -/
theorem normalized_shc_five_excluded_forty_nine : NormalizedSHCExcluded 4 49 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate49

/-- There is no normalized five-coordinate SHC family in `ZMod 51`. -/
theorem normalized_shc_five_excluded_fifty_one : NormalizedSHCExcluded 4 51 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate51

/-- There is no normalized five-coordinate SHC family in `ZMod 53`. -/
theorem normalized_shc_five_excluded_fifty_three : NormalizedSHCExcluded 4 53 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate53

/-- There is no normalized five-coordinate SHC family in `ZMod 55`. -/
theorem normalized_shc_five_excluded_fifty_five : NormalizedSHCExcluded 4 55 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate55

/-- There is no normalized five-coordinate SHC family in `ZMod 57`. -/
theorem normalized_shc_five_excluded_fifty_seven : NormalizedSHCExcluded 4 57 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate57

/-- There is no normalized five-coordinate SHC family in `ZMod 59`. -/
theorem normalized_shc_five_excluded_fifty_nine : NormalizedSHCExcluded 4 59 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate59

/-- There is no normalized five-coordinate SHC family in `ZMod 61`. -/
theorem normalized_shc_five_excluded_sixty_one : NormalizedSHCExcluded 4 61 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate61

/-- The normalized five-coordinate exclusion in the first five odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_forty_one {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 41) :
    NormalizedSHCExcluded 4 N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 33 ∨ N = 35 ∨ N = 37 ∨ N = 39 ∨ N = 41 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact normalized_shc_five_excluded_thirty_three
  · exact normalized_shc_five_excluded_thirty_five
  · exact normalized_shc_five_excluded_thirty_seven
  · exact normalized_shc_five_excluded_thirty_nine
  · exact normalized_shc_five_excluded_forty_one

/-- The normalized five-coordinate exclusion in the first eight odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_forty_seven {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 47) :
    NormalizedSHCExcluded 4 N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 33 ∨ N = 35 ∨ N = 37 ∨ N = 39 ∨ N = 41 ∨ N = 43 ∨
      N = 45 ∨ N = 47 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact normalized_shc_five_excluded_thirty_three
  · exact normalized_shc_five_excluded_thirty_five
  · exact normalized_shc_five_excluded_thirty_seven
  · exact normalized_shc_five_excluded_thirty_nine
  · exact normalized_shc_five_excluded_forty_one
  · exact normalized_shc_five_excluded_forty_three
  · exact normalized_shc_five_excluded_forty_five
  · exact normalized_shc_five_excluded_forty_seven

/-- The normalized five-coordinate exclusion in the first eleven odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_fifty_three {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 53) :
    NormalizedSHCExcluded 4 N := by
  by_cases hsmall : N ≤ 47
  · exact normalized_shc_five_excluded_of_odd_window_le_forty_seven
      hodd hlower hsmall
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 49 ∨ N = 51 ∨ N = 53 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact normalized_shc_five_excluded_forty_nine
  · exact normalized_shc_five_excluded_fifty_one
  · exact normalized_shc_five_excluded_fifty_three

/-- The normalized five-coordinate exclusion through the penultimate odd case
of the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_fifty_nine {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 59) :
    NormalizedSHCExcluded 4 N := by
  by_cases hsmall : N ≤ 53
  · exact normalized_shc_five_excluded_of_odd_window_le_fifty_three
      hodd hlower hsmall
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 55 ∨ N = 57 ∨ N = 59 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact normalized_shc_five_excluded_fifty_five
  · exact normalized_shc_five_excluded_fifty_seven
  · exact normalized_shc_five_excluded_fifty_nine

/-- Every odd modulus in the five-coordinate strict window satisfies the
normalized SHC exclusion. -/
theorem normalized_shc_five_excluded_of_odd_window {N : ℕ} (hodd : Odd N)
    (hlower : 33 ≤ N) (hupper : N ≤ 61) : NormalizedSHCExcluded 4 N := by
  by_cases hsmall : N ≤ 59
  · exact normalized_shc_five_excluded_of_odd_window_le_fifty_nine
      hodd hlower hsmall
  have hN : N = 61 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  subst N
  exact normalized_shc_five_excluded_sixty_one

/-- There is no five-coordinate SHC family in an odd `ZMod` of order between
33 and 61. -/
theorem not_exists_shc_fin_five_zmod_of_odd_window {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 61) :
    ¬ ∃ h : Fin 5 → ZMod N, SHC h := by
  letI : NeZero N := ⟨by omega⟩
  apply not_exists_shc_of_normalized
  · exact shc_hasGeneratorCoordinate_zmod_five_of_odd_window hodd hlower hupper
  · simpa only [Nat.card_zmod] using
      normalized_shc_five_excluded_of_odd_window hodd hlower hupper

/-- **Five-coordinate cyclic SHC base case.** Every SHC family with five
coordinates in a finite odd cyclic group forces the Mersenne lower bound 63. -/
theorem cyclicSHCOddLowerBound_five : CyclicSHCOddLowerBound 5 := by
  intro K _ _ _ hodd h hs
  by_contra hnot
  have hlt : Fintype.card K < 63 := Nat.lt_of_not_ge hnot
  have h32 : 32 ≤ Fintype.card K := by
    have hc := Fintype.card_le_of_injective
      (fun S : Finset (Fin 5) ↦ ∑ j ∈ S, h j) hs.dis
    simpa using hc
  obtain ⟨q, hq⟩ := hodd
  have hlower' : 33 ≤ Fintype.card K := by omega
  have hupper' : Fintype.card K ≤ 61 := by omega
  have hlower : 33 ≤ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hlower'
  have hupper : Nat.card K ≤ 61 := by
    simpa [Nat.card_eq_fintype_card] using hupper'
  have hodd' : Odd (Nat.card K) := by
    exact ⟨q, by simpa [Nat.card_eq_fintype_card] using hq⟩
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := K)
  let e : ZMod (Nat.card K) ≃+ K := zmodAddEquivOfGenerator hg rfl
  apply not_exists_shc_fin_five_zmod_of_odd_window hodd' hlower hupper
  exact ⟨e.symm ∘ h, hs.map_addEquiv h e.symm⟩

/-- **The odd stratum for `n = 6`:** every valid six-tuple modulo an odd
`N` forces `N ≥ 2^6 - 1 = 63`. -/
theorem odd_min_six {N : ℕ} (hN : Odd N) (g : Fin 6 → ZMod N)
    (hg : ValidTuple g) : 63 ≤ N := by
  letI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  have hs : SHC (diff g) := shc_diff_of_valid g hg (add_self_injective_zmod hN)
  have hodd : Odd (Fintype.card (ZMod N)) := by
    simpa [ZMod.card] using hN
  have hbound := cyclicSHCOddLowerBound_five (ZMod N) hodd (diff g) hs
  simpa [ZMod.card] using hbound

/-- **Unconditional six-coordinate saturation through the strict window.**
In an odd cyclic group of order at most 125, deleting any coordinate of a
six-coordinate SHC family leaves a tuple that spans the whole group. -/
theorem shc_six_deleted_span_eq_top {K : Type*} [AddCommGroup K]
    [Fintype K] [IsAddCyclic K] (hodd : Odd (Fintype.card K))
    (hupper : Fintype.card K ≤ 125) (h : Fin 6 → K) (hs : SHC h) (x : Fin 6) :
    AddSubgroup.closure (Set.range fun i : Fin 5 ↦ h (x.succAbove i)) = ⊤ := by
  apply shc_deleted_span_eq_top cyclicSHCOddLowerBound_five hodd ?_ h hs x
  norm_num
  exact hupper

end MinModulus
