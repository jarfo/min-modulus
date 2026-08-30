/-
# Structural generator reduction in the five-coordinate SHC window

This file proves that a five-coordinate SHC family has a generator coordinate
at every odd order from 33 through 61 except 45.  At composite orders, every
nonunit lies in one of two proper cyclic annihilator subgroups.  The
three- and four-coordinate SHC lower bounds limit how many coordinates can
lie in either subgroup, and the two bounds together cannot cover five
coordinates.  Prime orders are immediate because every nonzero element is a
unit.

Order 45 is the unique tight subgroup-cover case: three coordinates may lie
in its order-15 subgroup and two in its order-9 subgroup.  It is deliberately
left as the sole remaining generator-coordinate case for the next finite
certificate.
-/
import MinModulus.SHCFourGenerator
import Mathlib.Data.Finset.Sort

namespace MinModulus

open Finset

universe u

/-- If a subgroup is smaller than the assumed `k`-coordinate cyclic SHC
threshold, it contains fewer than `k` coordinates of an SHC family. -/
theorem shc_index_card_lt_of_cyclic_lower_bound {m k : ℕ}
    {G : Type u} [AddCommGroup G] (H : AddSubgroup G) [Fintype H] [IsAddCyclic H]
    (hind : CyclicSHCOddLowerBound.{u} k) (hodd : Odd (Fintype.card H))
    (hsmall : Fintype.card H < 2 ^ (k + 1) - 1)
    (h : Fin m → G) (hs : SHC h) (S : Finset (Fin m))
    (hmem : ∀ i ∈ S, h i ∈ H) : S.card < k := by
  by_contra hnot
  have hk : k ≤ S.card := Nat.le_of_not_gt hnot
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  let f : Fin k ↪ Fin m := (T.orderEmbOfFin hTcard).toEmbedding
  let hd : Fin k → G := h ∘ f
  have hsd : SHC hd := hs.comp_embedding h f
  have hdmem : ∀ i, hd i ∈ H := by
    intro i
    exact hmem (f i) (hTS (T.orderEmbOfFin_mem hTcard i))
  let hH : Fin k → H := fun i => ⟨hd i, hdmem i⟩
  have hsH : SHC hH := hsd.subtype H hd hdmem
  have hlower := hind H hodd hH hsH
  omega

/-- The dissociation floor alone limits the number of SHC coordinates inside
a subgroup whose cardinality is below `2^k`. -/
theorem shc_index_card_lt_of_dissociation {m k : ℕ}
    {G : Type u} [AddCommGroup G] (H : AddSubgroup G) [Fintype H]
    (hsmall : Fintype.card H < 2 ^ k)
    (h : Fin m → G) (hs : SHC h) (S : Finset (Fin m))
    (hmem : ∀ i ∈ S, h i ∈ H) : S.card < k := by
  by_contra hnot
  have hk : k ≤ S.card := Nat.le_of_not_gt hnot
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  let f : Fin k ↪ Fin m := (T.orderEmbOfFin hTcard).toEmbedding
  let hd : Fin k → G := h ∘ f
  have hsd : SHC hd := hs.comp_embedding h f
  have hdmem : ∀ i, hd i ∈ H := by
    intro i
    exact hmem (f i) (hTS (T.orderEmbOfFin_mem hTcard i))
  let hH : Fin k → H := fun i => ⟨hd i, hdmem i⟩
  have hsH : SHC hH := hsd.subtype H hd hdmem
  have hlower := Fintype.card_le_of_injective
    (fun T : Finset (Fin k) => ∑ j ∈ T, hH j) hsH.dis
  simp only [Fintype.card_finset, Fintype.card_fin] at hlower
  omega

/-- If every nonunit coordinate lies in one of two index classes that are too
small to cover all coordinates, the family has a generator coordinate. -/
theorem hasGeneratorCoordinate_of_index_cover {m N a b : ℕ} [NeZero N]
    (h : Fin m → ZMod N) (A B : Finset (Fin m))
    (hcover : ∀ i, ¬ IsUnit (h i) → i ∈ A ∨ i ∈ B)
    (hab : a + b ≤ m + 1) (hA : A.card < a) (hB : B.card < b) :
    HasGeneratorCoordinate h := by
  by_contra hno
  have hnonunit : ∀ i, ¬ IsUnit (h i) := by
    intro i hi
    apply hno
    exact ⟨i, zmod_generator_of_isUnit _ hi⟩
  have hcover' : (Finset.univ : Finset (Fin m)) ⊆ A ∪ B := by
    intro i hi
    rcases hcover i (hnonunit i) with hiA | hiB
    · exact Finset.mem_union_left B hiA
    · exact Finset.mem_union_right A hiB
  have hcard : m ≤ A.card + B.card := by
    have hle := Finset.card_le_card hcover'
    have hu := Finset.card_union_le A B
    simpa using (hle.trans hu)
  omega

private abbrev annihilatorSubgroup (N c : ℕ) : AddSubgroup (ZMod N) :=
  (nsmulAddMonoidHom c).ker

private theorem nonunit_mem_H33 (z : ZMod 33) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 33 11 ∨ z ∈ annihilatorSubgroup 33 3 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 33. -/
theorem shc_hasGeneratorCoordinate_zmod_thirty_three
    (h : Fin 5 → ZMod 33) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 33 11
  let J := annihilatorSubgroup 33 3
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 11 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  have hA : A.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) H
      cyclicSHCOddLowerBound_three
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 3) (b := 3)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H33 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

private theorem nonunit_mem_H35 (z : ZMod 35) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 35 7 ∨ z ∈ annihilatorSubgroup 35 5 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 35. -/
theorem shc_hasGeneratorCoordinate_zmod_thirty_five
    (h : Fin 5 → ZMod 35) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 35 7
  let J := annihilatorSubgroup 35 5
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 7 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  have hA : A.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) H
      cyclicSHCOddLowerBound_three
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 3) (b := 3)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H35 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

private theorem nonunit_mem_H39 (z : ZMod 39) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 39 13 ∨ z ∈ annihilatorSubgroup 39 3 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 39. -/
theorem shc_hasGeneratorCoordinate_zmod_thirty_nine
    (h : Fin 5 → ZMod 39) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 39 13
  let J := annihilatorSubgroup 39 3
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 13 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  have hA : A.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) H
      cyclicSHCOddLowerBound_three
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 3) (b := 3)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H39 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

set_option maxRecDepth 100000 in
private theorem nonunit_mem_H49 (z : ZMod 49) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 49 7 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 49. -/
theorem shc_hasGeneratorCoordinate_zmod_forty_nine
    (h : Fin 5 → ZMod 49) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 49 7
  let A := Finset.univ.filter fun i => h i ∈ H
  have hHcard : Fintype.card H = 7 := by decide
  have hA : A.card < 3 := by
    apply shc_index_card_lt_of_dissociation (k := 3) H
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 3) (b := 1)
    h A ∅ (hab := by norm_num) (hA := hA) (hB := by simp)
  intro i hi
  exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, nonunit_mem_H49 (h i) hi⟩)

set_option maxRecDepth 100000 in
private theorem nonunit_mem_H51 (z : ZMod 51) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 51 17 ∨ z ∈ annihilatorSubgroup 51 3 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 51. -/
theorem shc_hasGeneratorCoordinate_zmod_fifty_one
    (h : Fin 5 → ZMod 51) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 51 17
  let J := annihilatorSubgroup 51 3
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 17 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  have hA : A.card < 4 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) H
      cyclicSHCOddLowerBound_four
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 2 := by
    apply shc_index_card_lt_of_dissociation (k := 2) J
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 4) (b := 2)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H51 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

set_option maxRecDepth 100000 in
private theorem nonunit_mem_H55 (z : ZMod 55) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 55 11 ∨ z ∈ annihilatorSubgroup 55 5 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 55. -/
theorem shc_hasGeneratorCoordinate_zmod_fifty_five
    (h : Fin 5 → ZMod 55) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 55 11
  let J := annihilatorSubgroup 55 5
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 11 := by decide
  have hJcard : Fintype.card J = 5 := by decide
  have hA : A.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) H
      cyclicSHCOddLowerBound_three
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 3) (b := 3)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H55 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

set_option maxRecDepth 100000 in
private theorem nonunit_mem_H57 (z : ZMod 57) (hz : ¬ IsUnit z) :
    z ∈ annihilatorSubgroup 57 19 ∨ z ∈ annihilatorSubgroup 57 3 := by
  revert z
  decide

/-- Generator-coordinate existence for five-coordinate SHC at order 57. -/
theorem shc_hasGeneratorCoordinate_zmod_fifty_seven
    (h : Fin 5 → ZMod 57) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  let H := annihilatorSubgroup 57 19
  let J := annihilatorSubgroup 57 3
  let A := Finset.univ.filter fun i => h i ∈ H
  let B := Finset.univ.filter fun i => h i ∈ J
  have hHcard : Fintype.card H = 19 := by decide
  have hJcard : Fintype.card J = 3 := by decide
  have hA : A.card < 4 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) H
      cyclicSHCOddLowerBound_four
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 2 := by
    apply shc_index_card_lt_of_dissociation (k := 2) J
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  apply hasGeneratorCoordinate_of_index_cover (m := 5) (a := 4) (b := 2)
    h A B (hab := by norm_num) (hA := hA) (hB := hB)
  intro i hi
  rcases nonunit_mem_H57 (h i) hi with hiH | hiJ
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)

/-- At a prime modulus, any five-coordinate SHC family has a generator
coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_prime_five {p : ℕ} (hp : p.Prime)
    (h : Fin 5 → ZMod p) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨0, zmod_generator_of_isUnit (h 0) ?_⟩
  exact isUnit_iff_ne_zero.mpr (hs.ne_zero h 0)

/-- Every five-coordinate SHC family in the next odd strict window, except
for the unique tight subgroup-cover modulus 45, has a generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_five_of_odd_window_ne_forty_five
    {N : ℕ} (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 61) (hne : N ≠ 45)
    (h : Fin 5 → ZMod N) (hs : SHC h) : HasGeneratorCoordinate h := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have hcases :
      N = 33 ∨ N = 35 ∨ N = 37 ∨ N = 39 ∨ N = 41 ∨ N = 43 ∨ N = 45 ∨
      N = 47 ∨ N = 49 ∨ N = 51 ∨ N = 53 ∨ N = 55 ∨ N = 57 ∨ N = 59 ∨
      N = 61 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact shc_hasGeneratorCoordinate_zmod_thirty_three h hs
  · exact shc_hasGeneratorCoordinate_zmod_thirty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_thirty_nine h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact (hne rfl).elim
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_forty_nine h hs
  · exact shc_hasGeneratorCoordinate_zmod_fifty_one h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_fifty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_fifty_seven h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs
  · exact shc_hasGeneratorCoordinate_zmod_prime_five (by norm_num) h hs

end MinModulus
