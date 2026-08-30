/-
# Structural generator reduction in the six-coordinate SHC window

This file uses the newly proved five-coordinate cyclic SHC bound 63 to show
that a six-coordinate SHC family has a generator coordinate at every odd
order from 65 through 125 except 75, 99, 105, and 117.  At each composite
order, nonunits are covered by prime-factor annihilator subgroups.  The
known 15, 31, and 63 SHC thresholds (and the dissociation floor at order 3)
bound the number of coordinates in those subgroups.

The four exceptions are exactly the cases where these cardinality bounds are
tight: two subgroup classes can still cover six coordinates at 75, 99, and
117, while order 105 has three relevant prime-factor classes.
-/
import MinModulus.SHCFiveBaseCases

namespace MinModulus

open Finset

set_option maxRecDepth 100000

private abbrev annihilatorSubgroupSix (N c : ℕ) : AddSubgroup (ZMod N) :=
  (nsmulAddMonoidHom c).ker

private noncomputable def sixCoordinateIndex {N : ℕ} [NeZero N]
    (h : Fin 6 → ZMod N) (H : AddSubgroup (ZMod N)) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter fun i => h i ∈ H

private theorem generator_of_two_index_bounds {N a b : ℕ} [NeZero N]
    (h : Fin 6 → ZMod N) (H J : AddSubgroup (ZMod N))
    (hcover : ∀ z : ZMod N, ¬ IsUnit z → z ∈ H ∨ z ∈ J)
    (hab : a + b ≤ 7)
    (hA : (sixCoordinateIndex h H).card < a)
    (hB : (sixCoordinateIndex h J).card < b) :
    HasGeneratorCoordinate h := by
  classical
  apply hasGeneratorCoordinate_of_index_cover (m := 6) (a := a) (b := b)
    h (sixCoordinateIndex h H) (sixCoordinateIndex h J)
      (hab := hab) (hA := hA) (hB := hB)
  intro i hi
  rcases hcover (h i) hi with hiH | hiJ
  · exact Or.inl (by simp [sixCoordinateIndex, hiH])
  · exact Or.inr (by simp [sixCoordinateIndex, hiJ])

private theorem generator_of_one_index_bound {N a : ℕ} [NeZero N]
    (h : Fin 6 → ZMod N) (H : AddSubgroup (ZMod N))
    (hcover : ∀ z : ZMod N, ¬ IsUnit z → z ∈ H)
    (ha : a ≤ 6) (hA : (sixCoordinateIndex h H).card < a) :
    HasGeneratorCoordinate h := by
  classical
  apply hasGeneratorCoordinate_of_index_cover (m := 6) (a := a) (b := 1)
    h (sixCoordinateIndex h H) ∅
      (hab := by omega) (hA := hA) (hB := by simp)
  intro i hi
  exact Or.inl (by simp [sixCoordinateIndex, hcover (h i) hi])

private theorem sixCoordinateIndex_card_lt_of_cyclic_lower_bound
    {N k : ℕ} [NeZero N] (H : AddSubgroup (ZMod N))
    [Fintype H] [IsAddCyclic H] (hind : CyclicSHCOddLowerBound.{0} k)
    (hodd : Odd (Fintype.card H)) (hsmall : Fintype.card H < 2 ^ (k + 1) - 1)
    (h : Fin 6 → ZMod N) (hs : SHC h) : (sixCoordinateIndex h H).card < k := by
  apply shc_index_card_lt_of_cyclic_lower_bound H hind hodd hsmall h hs
  intro i hi
  simpa [sixCoordinateIndex] using hi

private theorem sixCoordinateIndex_card_lt_of_dissociation
    {N k : ℕ} [NeZero N] (H : AddSubgroup (ZMod N)) [Fintype H]
    (hsmall : Fintype.card H < 2 ^ k) (h : Fin 6 → ZMod N) (hs : SHC h) :
    (sixCoordinateIndex h H).card < k := by
  apply shc_index_card_lt_of_dissociation H hsmall h hs
  intro i hi
  simpa [sixCoordinateIndex] using hi

/-- At a prime modulus, any six-coordinate SHC family has a generator
coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_prime_six {p : ℕ} (hp : p.Prime)
    (h : Fin 6 → ZMod p) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨0, zmod_generator_of_isUnit (h 0) ?_⟩
  exact isUnit_iff_ne_zero.mpr (hs.ne_zero h 0)

/-- Generator-coordinate existence for six-coordinate SHC at order 65. -/
theorem shc_hasGeneratorCoordinate_zmod_six_sixty_five
    (h : Fin 6 → ZMod 65) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 65 13
  let J := annihilatorSubgroupSix 65 5
  have hHcard : Fintype.card H = 13 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  apply generator_of_two_index_bounds (a := 3) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_three <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 69. -/
theorem shc_hasGeneratorCoordinate_zmod_six_sixty_nine
    (h : Fin 6 → ZMod 69) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 69 23
  let J := annihilatorSubgroupSix 69 3
  have hHcard : Fintype.card H = 23 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 2) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_dissociation (hs := hs) J
    rw [hJcard]
    norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 77. -/
theorem shc_hasGeneratorCoordinate_zmod_six_seventy_seven
    (h : Fin 6 → ZMod 77) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 77 11
  let J := annihilatorSubgroupSix 77 7
  have hHcard : Fintype.card H = 11 := by decide
  have hJcard : Fintype.card J = 7 := by decide
  apply generator_of_two_index_bounds (a := 3) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_three <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 81. -/
theorem shc_hasGeneratorCoordinate_zmod_six_eighty_one
    (h : Fin 6 → ZMod 81) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 81 27
  have hHcard : Fintype.card H = 27 := by decide
  apply generator_of_one_index_bound (a := 4) h H
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 85. -/
theorem shc_hasGeneratorCoordinate_zmod_six_eighty_five
    (h : Fin 6 → ZMod 85) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 85 17
  let J := annihilatorSubgroupSix 85 5
  have hHcard : Fintype.card H = 17 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 87. -/
theorem shc_hasGeneratorCoordinate_zmod_six_eighty_seven
    (h : Fin 6 → ZMod 87) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 87 29
  let J := annihilatorSubgroupSix 87 3
  have hHcard : Fintype.card H = 29 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 2) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_dissociation (hs := hs) J
    rw [hJcard]
    norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 91. -/
theorem shc_hasGeneratorCoordinate_zmod_six_ninety_one
    (h : Fin 6 → ZMod 91) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 91 13
  let J := annihilatorSubgroupSix 91 7
  have hHcard : Fintype.card H = 13 := by decide
  have hJcard : Fintype.card J = 7 := by decide
  apply generator_of_two_index_bounds (a := 3) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_three <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 93. -/
theorem shc_hasGeneratorCoordinate_zmod_six_ninety_three
    (h : Fin 6 → ZMod 93) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 93 31
  let J := annihilatorSubgroupSix 93 3
  have hHcard : Fintype.card H = 31 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  apply generator_of_two_index_bounds (a := 5) (b := 2) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_five <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_dissociation (hs := hs) J
    rw [hJcard]
    norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 95. -/
theorem shc_hasGeneratorCoordinate_zmod_six_ninety_five
    (h : Fin 6 → ZMod 95) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 95 19
  let J := annihilatorSubgroupSix 95 5
  have hHcard : Fintype.card H = 19 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 111. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_eleven
    (h : Fin 6 → ZMod 111) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 111 37
  let J := annihilatorSubgroupSix 111 3
  have hHcard : Fintype.card H = 37 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  apply generator_of_two_index_bounds (a := 5) (b := 2) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_five <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_dissociation (hs := hs) J
    rw [hJcard]
    norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 115. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_fifteen
    (h : Fin 6 → ZMod 115) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 115 23
  let J := annihilatorSubgroupSix 115 5
  have hHcard : Fintype.card H = 23 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 119. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_nineteen
    (h : Fin 6 → ZMod 119) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 119 17
  let J := annihilatorSubgroupSix 119 7
  have hHcard : Fintype.card H = 17 := by decide
  have hJcard : Fintype.card J = 7 := by decide
  apply generator_of_two_index_bounds (a := 4) (b := 3) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) J
      cyclicSHCOddLowerBound_three <;> rw [hJcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 121. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_one
    (h : Fin 6 → ZMod 121) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 121 11
  have hHcard : Fintype.card H = 11 := by decide
  apply generator_of_one_index_bound (a := 3) h H
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_three <;> rw [hHcard] <;> norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 123. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_three
    (h : Fin 6 → ZMod 123) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 123 41
  let J := annihilatorSubgroupSix 123 3
  have hHcard : Fintype.card H = 41 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  apply generator_of_two_index_bounds (a := 5) (b := 2) h H J
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_five <;> rw [hHcard] <;> norm_num
  · apply sixCoordinateIndex_card_lt_of_dissociation (hs := hs) J
    rw [hJcard]
    norm_num

/-- Generator-coordinate existence for six-coordinate SHC at order 125. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_five
    (h : Fin 6 → ZMod 125) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroupSix 125 25
  have hHcard : Fintype.card H = 25 := by decide
  apply generator_of_one_index_bound (a := 4) h H
  · intro z hz; revert z; decide
  · norm_num
  · apply sixCoordinateIndex_card_lt_of_cyclic_lower_bound (hs := hs) H
      cyclicSHCOddLowerBound_four <;> rw [hHcard] <;> norm_num

/-- Away from the four tight subgroup-cover moduli, every six-coordinate SHC
family in the odd strict window has a generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_exceptions
    {N : ℕ} (hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 125)
    (h75 : N ≠ 75) (h99 : N ≠ 99) (h105 : N ≠ 105) (h117 : N ≠ 117)
    (h : Fin 6 → ZMod N) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have hcases :
      N = 65 ∨ N = 67 ∨ N = 69 ∨ N = 71 ∨ N = 73 ∨ N = 75 ∨
      N = 77 ∨ N = 79 ∨ N = 81 ∨ N = 83 ∨ N = 85 ∨ N = 87 ∨
      N = 89 ∨ N = 91 ∨ N = 93 ∨ N = 95 ∨ N = 97 ∨ N = 99 ∨
      N = 101 ∨ N = 103 ∨ N = 105 ∨ N = 107 ∨ N = 109 ∨ N = 111 ∨
      N = 113 ∨ N = 115 ∨ N = 117 ∨ N = 119 ∨ N = 121 ∨ N = 123 ∨
      N = 125 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shc_hasGeneratorCoordinate_zmod_six_sixty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_sixty_nine h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact (h75 rfl).elim
  · exact shc_hasGeneratorCoordinate_zmod_six_seventy_seven h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_eighty_one h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_eighty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_eighty_seven h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_ninety_one h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_ninety_three h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_ninety_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact (h99 rfl).elim
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact (h105 rfl).elim
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_eleven h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_six (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_fifteen h hs
  · exact (h117 rfl).elim
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_nineteen h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_one h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_three h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_twenty_five h hs

end MinModulus
