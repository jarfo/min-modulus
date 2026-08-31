/-
# Complete six-coordinate generator theorem

This file closes the final generator exception at order 105.  If every
coordinate is a nonunit, the lower-dimensional subgroup bounds first force a
coordinate divisible by 3 but by neither 5 nor 7.  Unit scaling sends that
coordinate to 3, and sorting places it first.  The generated order-105
certificate then supplies either a subset-sum collision or a forbidden
head-2 relation.

Combining this case with the structural results in `SHCSixGenerator.lean`
proves generator-coordinate existence throughout the odd strict window
65 through 125.
-/
import MinModulus.SHCSixGenerator
import MinModulus.Generated.SHCSixN105

namespace MinModulus

open Finset

set_option maxRecDepth 100000

private abbrev P3 : AddSubgroup (ZMod 105) := (nsmulAddMonoidHom 35).ker
private abbrev P5 : AddSubgroup (ZMod 105) := (nsmulAddMonoidHom 21).ker
private abbrev P7 : AddSubgroup (ZMod 105) := (nsmulAddMonoidHom 15).ker

private theorem cast_thirty_five_eq_of_P5_of_cast_seven_eq (x y : ZMod 105)
    (hx : x ∈ P5) (hy : y ∈ P5)
    (hxy : ZMod.castHom (show 7 ∣ 105 by norm_num) (ZMod 7) x =
      ZMod.castHom (show 7 ∣ 105 by norm_num) (ZMod 7) y) :
    ZMod.castHom (show 35 ∣ 105 by norm_num) (ZMod 35) x =
      ZMod.castHom (show 35 ∣ 105 by norm_num) (ZMod 35) y := by
  revert x y
  decide

private theorem cast_thirty_five_eq_of_P7_of_cast_five_eq (x y : ZMod 105)
    (hx : x ∈ P7) (hy : y ∈ P7)
    (hxy : ZMod.castHom (show 5 ∣ 105 by norm_num) (ZMod 5) x =
      ZMod.castHom (show 5 ∣ 105 by norm_num) (ZMod 5) y) :
    ZMod.castHom (show 35 ∣ 105 by norm_num) (ZMod 35) x =
      ZMod.castHom (show 35 ∣ 105 by norm_num) (ZMod 35) y := by
  revert x y
  decide

private theorem no_shc_three_P5_three_P7
    (a : Fin 3 → P5) (b : Fin 3 → P7) :
    ¬ SHC (Fin.append (fun i ↦ (a i : ZMod 105)) (fun i ↦ (b i : ZMod 105))) := by
  let qa : Finset (Fin 3) → ZMod 7 := fun S ↦
    ZMod.castHom (show 7 ∣ 105 by norm_num) (ZMod 7) (∑ i ∈ S, (a i : ZMod 105))
  obtain ⟨pickA, hpickA⟩ :=
    exists_collision_choices (α := 3) (β := 7) (k := 1) qa (by norm_num)
  let qb : Finset (Fin 3) → ZMod 5 := fun S ↦
    ZMod.castHom (show 5 ∣ 105 by norm_num) (ZMod 5) (∑ i ∈ S, (b i : ZMod 105))
  obtain ⟨pickB, hpickB⟩ :=
    exists_collision_choices (α := 3) (β := 5) (k := 1) qb (by norm_num)
  apply no_shc_of_block_collision (N := 105) (D := 35) (by norm_num)
      (fun i ↦ (a i : ZMod 105)) (fun i ↦ (b i : ZMod 105)) pickA pickB
  · intro i j
    apply cast_thirty_five_eq_of_P5_of_cast_seven_eq
    · exact P5.sum_mem fun x hx ↦ (a x).2
    · exact P5.sum_mem fun x hx ↦ (a x).2
    · exact hpickA i j
  · intro i j
    apply cast_thirty_five_eq_of_P7_of_cast_five_eq
    · exact P7.sum_mem fun x hx ↦ (b x).2
    · exact P7.sum_mem fun x hx ↦ (b x).2
    · exact hpickB i j
  · decide

private noncomputable def indexSet105 (h : Fin 6 → ZMod 105)
    (H : AddSubgroup (ZMod 105)) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter fun i ↦ h i ∈ H

private theorem mem_indexSet105_iff (h : Fin 6 → ZMod 105)
    (H : AddSubgroup (ZMod 105)) (i : Fin 6) :
    i ∈ indexSet105 h H ↔ h i ∈ H := by
  classical
  simp [indexSet105]

private theorem false_of_three_three_cover
    (h : Fin 6 → ZMod 105) (hs : SHC h)
    (hcover : ∀ i, i ∈ indexSet105 h P5 ∨ i ∈ indexSet105 h P7)
    (hA_lt : (indexSet105 h P5).card < 4)
    (hB_lt : (indexSet105 h P7).card < 4) : False := by
  classical
  let A := indexSet105 h P5
  let B := indexSet105 h P7
  have hcover' : (Finset.univ : Finset (Fin 6)) ⊆ A ∪ B := by
    intro i hi
    rcases hcover i with hiA | hiB
    · exact Finset.mem_union_left B hiA
    · exact Finset.mem_union_right A hiB
  have hcard : 6 ≤ A.card + B.card := by
    have hle := Finset.card_le_card hcover'
    have hu := Finset.card_union_le A B
    simpa using hle.trans hu
  have hA_bound : A.card ≤ 3 := by
    dsimp only [A]
    omega
  have hB_bound : B.card ≤ 3 := by
    dsimp only [B]
    omega
  have hAcard : A.card = 3 := by
    omega
  have hBcard : B.card = 3 := by omega
  have hUcard : (A ∪ B).card = 6 := by
    have hle := Finset.card_le_card hcover'
    have hle' : 6 ≤ (A ∪ B).card := by simpa using hle
    have hu : (A ∪ B).card ≤ 6 := by simpa using Finset.card_le_univ (A ∪ B)
    omega
  have hIcard : (A ∩ B).card = 0 := by
    have hsum := Finset.card_union_add_card_inter A B
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hIcard
  let eA : Fin 3 ↪ Fin 6 := (A.orderEmbOfFin hAcard).toEmbedding
  let eB : Fin 3 ↪ Fin 6 := (B.orderEmbOfFin hBcard).toEmbedding
  have hrange : Disjoint (Set.range eA) (Set.range eB) := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    obtain ⟨j, rfl⟩ := hiA
    obtain ⟨k, hik⟩ := hiB
    have hjeA : eA j ∈ A := A.orderEmbOfFin_mem hAcard j
    have hkeB : eB k ∈ B := B.orderEmbOfFin_mem hBcard k
    apply (Finset.disjoint_left.mp hdisj hjeA)
    simpa [hik] using hkeB
  let e : Fin 6 ↪ Fin 6 := Fin.Embedding.append hrange
  have hebij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, by simp⟩
  let p : Fin 6 ≃ Fin 6 := Equiv.ofBijective e hebij
  let a : Fin 3 → P5 := fun i ↦
    ⟨h (eA i), by
      have hi := A.orderEmbOfFin_mem hAcard i
      change eA i ∈ indexSet105 h P5 at hi
      exact (mem_indexSet105_iff h P5 (eA i)).mp hi⟩
  let b : Fin 3 → P7 := fun i ↦
    ⟨h (eB i), by
      have hi := B.orderEmbOfFin_mem hBcard i
      change eB i ∈ indexSet105 h P7 at hi
      exact (mem_indexSet105_iff h P7 (eB i)).mp hi⟩
  have happend :
      Fin.append (fun i ↦ (a i : ZMod 105)) (fun i ↦ (b i : ZMod 105)) = h ∘ p := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [a, eA, p, e, Fin.Embedding.append]
    · intro j
      change
        Fin.append (fun i ↦ (a i : ZMod 105)) (fun i ↦ (b i : ZMod 105))
            (Fin.natAdd 3 j) =
          h (Fin.append eA eB (Fin.natAdd 3 j))
      rw [Fin.append_right, Fin.append_right]
  apply no_shc_three_P5_three_P7 a b
  rw [happend]
  exact hs.reindex_equiv h p

private theorem nonunit_mem_P5_or_P7_of_not_exact_three (z : ZMod 105)
    (hnu : ¬ IsUnit z) (hnot : ¬ (z ∈ P3 ∧ z ∉ P5 ∧ z ∉ P7)) :
    z ∈ P5 ∨ z ∈ P7 := by
  revert z
  decide

private theorem exists_exact_three_coordinate (h : Fin 6 → ZMod 105) (hs : SHC h)
    (hnonunit : ∀ i, ¬ IsUnit (h i)) :
    ∃ i, h i ∈ P3 ∧ h i ∉ P5 ∧ h i ∉ P7 := by
  by_contra hnone
  have hcover : ∀ i, i ∈ indexSet105 h P5 ∨ i ∈ indexSet105 h P7 := by
    intro i
    have hnot : ¬ (h i ∈ P3 ∧ h i ∉ P5 ∧ h i ∉ P7) := by
      intro hi
      exact hnone ⟨i, hi⟩
    have hi := nonunit_mem_P5_or_P7_of_not_exact_three (h i) (hnonunit i) hnot
    simpa [indexSet105] using hi
  have hP5card : Fintype.card P5 = 21 := by decide
  have hP7card : Fintype.card P7 = 15 := by decide
  apply false_of_three_three_cover h hs hcover
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) P5
      cyclicSHCOddLowerBound_four
    · rw [hP5card]
      norm_num
    · rw [hP5card]
      norm_num
    · exact hs
    · intro i hi
      simpa [indexSet105] using hi
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) P7
      cyclicSHCOddLowerBound_four
    · rw [hP7card]
      norm_num
    · rw [hP7card]
      norm_num
    · exact hs
    · intro i hi
      simpa [indexSet105] using hi

private theorem exists_unit_mul_eq_three (z : ZMod 105)
    (h3 : z ∈ P3) (h5 : z ∉ P5) (h7 : z ∉ P7) :
    ∃ u : ZMod 105, IsUnit u ∧ u * z = 3 := by
  revert z
  decide

private def unitScale (v : (ZMod 105)ˣ) : ZMod 105 ≃+ ZMod 105 where
  toFun z := (v : ZMod 105) * z
  invFun z := ((v⁻¹ : (ZMod 105)ˣ) : ZMod 105) * z
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by simp [mul_add]

private theorem nonunit_val_ge_three (z : ZMod 105) (hz0 : z ≠ 0)
    (hnu : ¬ IsUnit z) : 3 ≤ z.val := by
  revert z
  decide

/-- Every six-coordinate SHC family at order 105 has a generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_five
    (h : Fin 6 → ZMod 105) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  by_contra hno
  have hnonunit : ∀ i, ¬ IsUnit (h i) := by
    intro i hi
    apply hno
    exact ⟨i, zmod_generator_of_isUnit _ hi⟩
  obtain ⟨x, hx3, hx5, hx7⟩ := exists_exact_three_coordinate h hs hnonunit
  obtain ⟨u, hu, hux⟩ := exists_unit_mul_eq_three (h x) hx3 hx5 hx7
  let v : (ZMod 105)ˣ := hu.unit
  let e : ZMod 105 ≃+ ZMod 105 := unitScale v
  let g : Fin 6 → ZMod 105 := e ∘ h
  have hgs : SHC g := hs.map_addEquiv h e
  have hgnu : ∀ i, ¬ IsUnit (g i) := by
    intro i
    simpa [g, e, unitScale, v, IsUnit.mul_iff, hu] using hnonunit i
  have hgx : g x = 3 := by simpa [g, e, unitScale, v] using hux
  let p : Fin 6 ≃ Fin 6 := Tuple.sort (fun i ↦ (g i).val)
  let g' : Fin 6 → ZMod 105 := g ∘ p
  have hg's : SHC g' := hgs.reindex_equiv g p
  have hg'mono : Monotone (fun i ↦ (g' i).val) :=
    Tuple.monotone_sort (fun i ↦ (g i).val)
  have hg'nu : ∀ i, ¬ IsUnit (g' i) := fun i ↦ hgnu (p i)
  have hg'0 : g' 0 = 3 := by
    let j : Fin 6 := p.symm x
    have hgj : g' j = 3 := by simp [g', j, p, hgx]
    have hle : (g' 0).val ≤ 3 := by
      calc
        (g' 0).val ≤ (g' j).val := hg'mono (Fin.zero_le j)
        _ = 3 := by
          rw [hgj]
          exact ZMod.val_ofNat_of_lt (by norm_num)
    have hge : 3 ≤ (g' 0).val :=
      nonunit_val_ge_three (g' 0) (hg's.ne_zero g' 0) (hg'nu 0)
    apply ZMod.val_injective
    rw [show (3 : ZMod 105).val = 3 by
      exact ZMod.val_ofNat_of_lt (by norm_num)]
    omega
  exact SHCSixExceptionalCertificate.sortedNormalizedNonunitExcluded_of_certificate
    SHCSixExceptionalCertificate.Generated.certificate105 g' hg'0 hg'mono hg'nu hg's

/-- Every six-coordinate SHC family in the full odd strict window has a
generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_six_of_odd_window
    {N : ℕ} (hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 125)
    (h : Fin 6 → ZMod N) (hs : SHC h) : HasGeneratorCoordinate h := by
  by_cases h105 : N = 105
  · subst N
    exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_one_hundred_five
      hodd hlower hupper h105 h hs

end MinModulus
