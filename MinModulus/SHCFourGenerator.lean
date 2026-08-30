/-
# Generator coordinates and the four-coordinate cyclic SHC bound

This file closes the generator-coordinate half of the first open SHC window.
For prime moduli, every nonzero coordinate is a generator.  For orders 25 and
27, unconditional deletion spanning forces a unit coordinate by an
annihilator argument.  At order 21, a kernel-checked search over the eight
nonunits shows that no sorted dissociated four-tuple exists.

Combining generator normalization with the finite exclusions in
`SHCFourBaseCases.lean` proves the unconditional four-coordinate odd cyclic
SHC lower bound 31.  Subtuple rigidity then gives unconditional deletion
spanning for five-coordinate SHC families through order 61.
-/
import MinModulus.SHCFourBaseCases

namespace MinModulus

/-- A unit in `ZMod N` generates its whole additive group. -/
theorem zmod_generator_of_isUnit {N : ℕ} [NeZero N] (a : ZMod N) (ha : IsUnit a) :
    ∀ y, y ∈ AddSubgroup.zmultiples a := by
  have ha' : IsUnit (a.val : ZMod N) := by simpa using ha
  have hcop : N.Coprime a.val := ((ZMod.isUnit_iff_coprime a.val N).mp ha').symm
  have hord : addOrderOf a = N := by
    rw [← ZMod.natCast_zmod_val a, ZMod.addOrderOf_coe a.val (NeZero.ne N),
      hcop.gcd_eq_one]
    simp
  have htop : AddSubgroup.zmultiples a = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, Nat.card_zmod]
  rw [htop]
  simp

/-- At a prime modulus, any four-coordinate SHC family has a generator
coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_prime {p : ℕ} (hp : p.Prime)
    (h : Fin 4 → ZMod p) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨0, zmod_generator_of_isUnit (h 0) ?_⟩
  exact isUnit_iff_ne_zero.mpr (hs.ne_zero h 0)

/-- If a scalar annihilates every nonunit but not `1`, then a spanning family
in `ZMod N` contains a unit. -/
theorem exists_isUnit_of_span_eq_top {N c m : ℕ} [NeZero N]
    (hann : ∀ a : ZMod N, ¬ IsUnit a → c • a = 0)
    (hc : c • (1 : ZMod N) ≠ 0) (h : Fin m → ZMod N)
    (hspan : AddSubgroup.closure (Set.range h) = ⊤) : ∃ i, IsUnit (h i) := by
  by_contra hno
  push Not at hno
  let K : AddSubgroup (ZMod N) := (nsmulAddMonoidHom c).ker
  have hrange : Set.range h ⊆ K := by
    rintro _ ⟨i, rfl⟩
    exact hann (h i) (hno i)
  have hle : AddSubgroup.closure (Set.range h) ≤ K :=
    (AddSubgroup.closure_le K).2 hrange
  have hone : (1 : ZMod N) ∈ K := by
    rw [hspan] at hle
    exact hle trivial
  exact hc hone

private theorem five_nsmul_eq_zero_of_not_isUnit (a : ZMod 25) (ha : ¬ IsUnit a) :
    5 • a = 0 := by
  have hnot25 : ¬ a.val.Coprime 25 := by
    intro hcop
    apply ha
    have : IsUnit (a.val : ZMod 25) :=
      (ZMod.isUnit_iff_coprime a.val 25).mpr hcop
    simpa using this
  have hnot5 : ¬ a.val.Coprime 5 := by
    intro hcop
    apply hnot25
    have hp : a.val.Coprime (5 ^ 2) :=
      (Nat.coprime_pow_right_iff (by omega) a.val 5).mpr hcop
    norm_num at hp
    exact hp
  have hdiv : 5 ∣ a.val := by
    by_contra hn
    apply hnot5
    exact (Nat.prime_five.coprime_iff_not_dvd.mpr hn).symm
  obtain ⟨b, hb⟩ := hdiv
  rw [← ZMod.natCast_zmod_val a, hb]
  calc
    5 • ((5 * b : ℕ) : ZMod 25) =
        (5 : ZMod 25) * (5 : ZMod 25) * (b : ZMod 25) := by
      rw [nsmul_eq_mul]
      simp only [Nat.cast_mul]
      ring
    _ = 0 := by
      have hz : (5 : ZMod 25) * 5 = 0 := by
        norm_num only [← Nat.cast_mul]
        exact ZMod.natCast_self 25
      rw [hz, zero_mul]

private theorem nine_nsmul_eq_zero_of_not_isUnit (a : ZMod 27) (ha : ¬ IsUnit a) :
    9 • a = 0 := by
  have hnot27 : ¬ a.val.Coprime 27 := by
    intro hcop
    apply ha
    have : IsUnit (a.val : ZMod 27) :=
      (ZMod.isUnit_iff_coprime a.val 27).mpr hcop
    simpa using this
  have hnot3 : ¬ a.val.Coprime 3 := by
    intro hcop
    apply hnot27
    have hp : a.val.Coprime (3 ^ 3) :=
      (Nat.coprime_pow_right_iff (by omega) a.val 3).mpr hcop
    norm_num at hp
    exact hp
  have hdiv : 3 ∣ a.val := by
    by_contra hn
    apply hnot3
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr hn).symm
  obtain ⟨b, hb⟩ := hdiv
  rw [← ZMod.natCast_zmod_val a, hb]
  calc
    9 • ((3 * b : ℕ) : ZMod 27) =
        (9 : ZMod 27) * (3 : ZMod 27) * (b : ZMod 27) := by
      rw [nsmul_eq_mul]
      simp only [Nat.cast_mul]
      ring
    _ = 0 := by
      have hz : (9 : ZMod 27) * 3 = 0 := by
        norm_num only [← Nat.cast_mul]
        exact ZMod.natCast_self 27
      rw [hz, zero_mul]

/-- Every four-coordinate SHC family in `ZMod 25` has a generator
coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_twenty_five
    (h : Fin 4 → ZMod 25) (hs : SHC h) : HasGeneratorCoordinate h := by
  have hspan := shc_four_deleted_span_eq_top (K := ZMod 25)
    (by norm_num) (by norm_num) h hs 0
  obtain ⟨i, hi⟩ := exists_isUnit_of_span_eq_top
    (N := 25) (c := 5) five_nsmul_eq_zero_of_not_isUnit
    (by decide) (fun i : Fin 3 => h ((0 : Fin 4).succAbove i)) hspan
  exact ⟨(0 : Fin 4).succAbove i, zmod_generator_of_isUnit _ hi⟩

/-- Every four-coordinate SHC family in `ZMod 27` has a generator
coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_twenty_seven
    (h : Fin 4 → ZMod 27) (hs : SHC h) : HasGeneratorCoordinate h := by
  have hspan := shc_four_deleted_span_eq_top (K := ZMod 27)
    (by norm_num) (by norm_num) h hs 0
  obtain ⟨i, hi⟩ := exists_isUnit_of_span_eq_top
    (N := 27) (c := 9) nine_nsmul_eq_zero_of_not_isUnit
    (by decide) (fun i : Fin 3 => h ((0 : Fin 4).succAbove i)) hspan
  exact ⟨(0 : Fin 4).succAbove i, zmod_generator_of_isUnit _ hi⟩

private abbrev Nonunit21 := {a : ZMod 21 // ¬ IsUnit a}

/-- Executable dissociation checker on four nonunits of `ZMod 21`. -/
private def checkDissociatedFour21 (h : Fin 4 → Nonunit21) : Bool :=
  decide (∀ S T : Finset (Fin 4),
    (∑ j ∈ S, (h j : ZMod 21)) = ∑ j ∈ T, (h j : ZMod 21) → S = T)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_nonunit_dissociated_twenty_one :
    ¬ ∃ h : Fin 4 → Nonunit21,
      Monotone (fun i => (h i).1.val) ∧ checkDissociatedFour21 h = true := by
  decide

/-- Every four-coordinate SHC family in `ZMod 21` has a generator coordinate.
The finite certificate searches only the eight nonunits. -/
theorem shc_hasGeneratorCoordinate_zmod_twenty_one
    (h : Fin 4 → ZMod 21) (hs : SHC h) : HasGeneratorCoordinate h := by
  by_contra hno
  have hnonunit : ∀ i, ¬ IsUnit (h i) := by
    intro i hi
    apply hno
    exact ⟨i, zmod_generator_of_isUnit _ hi⟩
  let p : Fin 4 ≃ Fin 4 := Tuple.sort (fun i => (h i).val)
  let h' : Fin 4 → ZMod 21 := h ∘ p
  have hsh' : SHC h' := hs.reindex_equiv h p
  have hmono : Monotone (fun i => (h' i).val) := by
    exact Tuple.monotone_sort (fun i => (h i).val)
  let hnu : Fin 4 → Nonunit21 := fun i => ⟨h' i, hnonunit (p i)⟩
  apply no_sorted_nonunit_dissociated_twenty_one
  refine ⟨hnu, ?_, ?_⟩
  · simpa [hnu] using hmono
  · simp only [checkDissociatedFour21, decide_eq_true_eq]
    intro S T hST
    apply hsh'.dis
    simpa [hnu] using hST

/-- Every four-coordinate SHC family over an odd `ZMod` in the strict window
17 through 29 has a generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_of_odd_window {N : ℕ}
    (hodd : Odd N) (hlower : 17 ≤ N) (hupper : N ≤ 29)
    (h : Fin 4 → ZMod N) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 17 ∨ N = 19 ∨ N = 21 ∨ N = 23 ∨ N = 25 ∨ N = 27 ∨ N = 29 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shc_hasGeneratorCoordinate_zmod_prime (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_twenty_one h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_twenty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_twenty_seven h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime (by norm_num) h hs

/-- There is no four-coordinate SHC family in an odd `ZMod` of order between
17 and 29. -/
theorem not_exists_shc_fin_four_zmod_of_odd_window {N : ℕ}
    (hodd : Odd N) (hlower : 17 ≤ N) (hupper : N ≤ 29) :
    ¬ ∃ h : Fin 4 → ZMod N, SHC h := by
  letI : NeZero N := ⟨by omega⟩
  apply not_exists_shc_of_normalized
  · exact shc_hasGeneratorCoordinate_zmod_of_odd_window hodd hlower hupper
  · simpa only [Nat.card_zmod] using
      normalized_shc_four_excluded_of_odd_window hodd hlower hupper

/-- **Four-coordinate cyclic SHC base case.** Every SHC family with four
coordinates in a finite odd cyclic group forces the Mersenne lower bound 31. -/
theorem cyclicSHCOddLowerBound_four : CyclicSHCOddLowerBound 4 := by
  intro K _ _ _ hodd h hs
  by_contra hnot
  have hlt : Fintype.card K < 31 := Nat.lt_of_not_ge hnot
  have h16 : 16 ≤ Fintype.card K := by
    have hc := Fintype.card_le_of_injective
      (fun S : Finset (Fin 4) ↦ ∑ j ∈ S, h j) hs.dis
    simpa using hc
  obtain ⟨q, hq⟩ := hodd
  have hlower' : 17 ≤ Fintype.card K := by omega
  have hupper' : Fintype.card K ≤ 29 := by omega
  have hlower : 17 ≤ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hlower'
  have hupper : Nat.card K ≤ 29 := by
    simpa [Nat.card_eq_fintype_card] using hupper'
  have hodd' : Odd (Nat.card K) := by
    exact ⟨q, by simpa [Nat.card_eq_fintype_card] using hq⟩
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := K)
  let e : ZMod (Nat.card K) ≃+ K := zmodAddEquivOfGenerator hg rfl
  apply not_exists_shc_fin_four_zmod_of_odd_window hodd' hlower hupper
  exact ⟨e.symm ∘ h, hs.map_addEquiv h e.symm⟩

/-- **The odd stratum for `n = 5`:** every valid five-tuple modulo an odd
`N` forces `N ≥ 2^5 - 1 = 31`. -/
theorem odd_min_five {N : ℕ} (hN : Odd N) (g : Fin 5 → ZMod N)
    (hg : ValidTuple g) : 31 ≤ N := by
  letI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  have hs : SHC (diff g) := shc_diff_of_valid g hg (add_self_injective_zmod hN)
  have hodd : Odd (Fintype.card (ZMod N)) := by
    simpa [ZMod.card] using hN
  have hbound := cyclicSHCOddLowerBound_four (ZMod N) hodd (diff g) hs
  simpa [ZMod.card] using hbound

/-- **Unconditional five-coordinate saturation through the strict window.**
In an odd cyclic group of order at most 61, deleting any coordinate of a
five-coordinate SHC family leaves a tuple that spans the whole group. -/
theorem shc_five_deleted_span_eq_top {K : Type*} [AddCommGroup K]
    [Fintype K] [IsAddCyclic K] (hodd : Odd (Fintype.card K))
    (hupper : Fintype.card K ≤ 61) (h : Fin 5 → K) (hs : SHC h) (x : Fin 5) :
    AddSubgroup.closure (Set.range fun i : Fin 4 ↦ h (x.succAbove i)) = ⊤ := by
  apply shc_deleted_span_eq_top cyclicSHCOddLowerBound_four hodd ?_ h hs x
  norm_num
  exact hupper

end MinModulus
