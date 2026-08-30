/-
# Five-coordinate generator theorem

This file closes the sole tight case left by the structural generator
reduction: order 45.  If all five coordinates are nonunits, the subgroup
cardinality bounds force exactly three coordinates into the order-15
annihilator subgroup and two into the order-9 subgroup.  Eight subset sums of
the first block collide modulo 5, and four subset sums of the second block
collide modulo 3.  Combining the two collisions would inject four elements
into a coset of the three-element kernel of `ZMod 45 → ZMod 15`, contradicting
dissociation.

Together with `SHCFiveGeneratorReduction.lean`, this proves generator-coordinate
existence at every odd modulus in the five-coordinate strict window 33–61.
-/
import MinModulus.SHCFiveGeneratorReduction

namespace MinModulus

open Finset

private abbrev H45 : AddSubgroup (ZMod 45) := (nsmulAddMonoidHom 15).ker
private abbrev J45 : AddSubgroup (ZMod 45) := (nsmulAddMonoidHom 9).ker
private abbrev K45 : AddSubgroup (ZMod 45) :=
  (ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15)).toAddMonoidHom.ker

private def blockSet (S : Finset (Fin 3)) (T : Finset (Fin 2)) : Finset (Fin 5) :=
  S.map (Fin.castAddEmb 2) ∪ T.map (Fin.natAddEmb 3)

private theorem blockSet_injective :
    Function.Injective (fun p : Finset (Fin 3) × Finset (Fin 2) ↦ blockSet p.1 p.2) := by
  decide

private theorem sum_blockSet (a : Fin 3 → ZMod 45) (b : Fin 2 → ZMod 45)
    (S : Finset (Fin 3)) (T : Finset (Fin 2)) :
    (∑ j ∈ blockSet S T, Fin.append a b j) = (∑ i ∈ S, a i) + ∑ i ∈ T, b i := by
  rw [blockSet, Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact Fin.append_left a b i
    · apply Finset.sum_congr rfl
      intro i hi
      exact Fin.append_right a b i
  · rw [Finset.disjoint_left]
    intro z hzS hzT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hzS
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hzT
    have hv := congrArg Fin.val heq
    simp only [Fin.natAddEmb, Fin.castAddEmb, Fin.castLEEmb, Function.Embedding.coeFn_mk,
      Fin.val_castLE, Fin.val_natAdd] at hv
    omega

private theorem cast_fifteen_eq_of_H45_of_cast_five_eq (x y : ZMod 45)
    (hx : x ∈ H45) (hy : y ∈ H45)
    (hxy : ZMod.castHom (show 5 ∣ 45 by norm_num) (ZMod 5) x =
      ZMod.castHom (show 5 ∣ 45 by norm_num) (ZMod 5) y) :
    ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) x =
      ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) y := by
  revert x y
  decide

private theorem cast_fifteen_eq_of_J45_of_cast_three_eq (x y : ZMod 45)
    (hx : x ∈ J45) (hy : y ∈ J45)
    (hxy : ZMod.castHom (show 3 ∣ 45 by norm_num) (ZMod 3) x =
      ZMod.castHom (show 3 ∣ 45 by norm_num) (ZMod 3) y) :
    ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) x =
      ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) y := by
  revert x y
  decide

/-- No SHC family can consist of three elements in the order-15 annihilator
subgroup followed by two in the order-9 annihilator subgroup of `ZMod 45`. -/
private theorem no_shc_three_H_two_J
    (a : Fin 3 → H45) (b : Fin 2 → J45) :
    ¬ SHC (Fin.append (fun i ↦ (a i : ZMod 45)) (fun i ↦ (b i : ZMod 45))) := by
  intro hs
  let qa : Finset (Fin 3) → ZMod 5 := fun S ↦
    ZMod.castHom (show 5 ∣ 45 by norm_num) (ZMod 5) (∑ i ∈ S, (a i : ZMod 45))
  have hqani : ¬ Function.Injective qa := by
    intro hi
    have hc := Fintype.card_le_of_injective qa hi
    simp only [Fintype.card_finset, Fintype.card_fin, ZMod.card] at hc
    norm_num at hc
  obtain ⟨SA, TA, hqa, hSAT⟩ := Function.not_injective_iff.mp hqani
  let qb : Finset (Fin 2) → ZMod 3 := fun S ↦
    ZMod.castHom (show 3 ∣ 45 by norm_num) (ZMod 3) (∑ i ∈ S, (b i : ZMod 45))
  have hqbni : ¬ Function.Injective qb := by
    intro hi
    have hc := Fintype.card_le_of_injective qb hi
    simp only [Fintype.card_finset, Fintype.card_fin, ZMod.card] at hc
    norm_num at hc
  obtain ⟨SB, TB, hqb, hSBT⟩ := Function.not_injective_iff.mp hqbni
  let sA : ZMod 45 := ∑ i ∈ SA, (a i : ZMod 45)
  let tA : ZMod 45 := ∑ i ∈ TA, (a i : ZMod 45)
  let sB : ZMod 45 := ∑ i ∈ SB, (b i : ZMod 45)
  let tB : ZMod 45 := ∑ i ∈ TB, (b i : ZMod 45)
  have hsA : sA ∈ H45 := by
    apply H45.sum_mem
    intro i hi
    exact (a i).2
  have htA : tA ∈ H45 := by
    apply H45.sum_mem
    intro i hi
    exact (a i).2
  have hsB : sB ∈ J45 := by
    apply J45.sum_mem
    intro i hi
    exact (b i).2
  have htB : tB ∈ J45 := by
    apply J45.sum_mem
    intro i hi
    exact (b i).2
  have hA15 : ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) sA =
      ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) tA := by
    apply cast_fifteen_eq_of_H45_of_cast_five_eq sA tA hsA htA
    exact hqa
  have hB15 : ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) sB =
      ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) tB := by
    apply cast_fifteen_eq_of_J45_of_cast_three_eq sB tB hsB htB
    exact hqb
  have hAker : ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) (tA - sA) = 0 := by
    rw [map_sub, hA15, sub_self]
  have hBker : ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) (tB - sB) = 0 := by
    rw [map_sub, hB15, sub_self]
  have hABker : ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15)
      ((tA + tB) - (sA + sB)) = 0 := by
    rw [map_sub, map_add, map_add, hA15, hB15, sub_self]
  let pickA : Fin 2 → Finset (Fin 3) := ![SA, TA]
  let pickB : Fin 2 → Finset (Fin 2) := ![SB, TB]
  let base : ZMod 45 := sA + sB
  let d : Fin 2 × Fin 2 → K45 := fun p ↦
    ⟨(∑ i ∈ pickA p.1, (a i : ZMod 45)) +
        (∑ i ∈ pickB p.2, (b i : ZMod 45)) - base, by
      change ZMod.castHom (show 15 ∣ 45 by norm_num) (ZMod 15) _ = 0
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j
      · simp [pickA, pickB, base, sA, sB]
      · simpa [pickA, pickB, base, sA, sB, tB] using hBker
      · simpa [pickA, pickB, base, sA, tA, sB] using hAker
      · simpa [pickA, pickB, base, sA, tA, sB, tB] using hABker⟩
  have hd_inj : Function.Injective d := by
    rintro ⟨pi, pj⟩ ⟨qi, qj⟩ hpq
    have hsum :
        (∑ i ∈ pickA pi, (a i : ZMod 45)) +
          (∑ i ∈ pickB pj, (b i : ZMod 45)) =
        (∑ i ∈ pickA qi, (a i : ZMod 45)) +
          (∑ i ∈ pickB qj, (b i : ZMod 45)) := by
      have hv := congrArg Subtype.val hpq
      simpa [d] using hv
    have hsets : blockSet (pickA pi) (pickB pj) =
        blockSet (pickA qi) (pickB qj) := by
      apply hs.dis
      calc
        (∑ j ∈ blockSet (pickA pi) (pickB pj),
            Fin.append (fun i ↦ (a i : ZMod 45)) (fun i ↦ (b i : ZMod 45)) j) =
            (∑ i ∈ pickA pi, (a i : ZMod 45)) +
              ∑ i ∈ pickB pj, (b i : ZMod 45) := sum_blockSet _ _ _ _
        _ = (∑ i ∈ pickA qi, (a i : ZMod 45)) +
              ∑ i ∈ pickB qj, (b i : ZMod 45) := hsum
        _ = (∑ j ∈ blockSet (pickA qi) (pickB qj),
            Fin.append (fun i ↦ (a i : ZMod 45)) (fun i ↦ (b i : ZMod 45)) j) :=
          (sum_blockSet _ _ _ _).symm
    have hpicks : (pickA pi, pickB pj) = (pickA qi, pickB qj) := by
      apply blockSet_injective
      exact hsets
    have hpA : pickA pi = pickA qi := congrArg Prod.fst hpicks
    have hpB : pickB pj = pickB qj := congrArg Prod.snd hpicks
    have hp1 : pi = qi := by
      fin_cases pi <;> fin_cases qi
      · rfl
      · exact (hSAT hpA).elim
      · exact (hSAT hpA.symm).elim
      · rfl
    have hp2 : pj = qj := by
      fin_cases pj <;> fin_cases qj
      · rfl
      · exact (hSBT hpB).elim
      · exact (hSBT hpB.symm).elim
      · rfl
    exact Prod.ext hp1 hp2
  have hc := Fintype.card_le_of_injective d hd_inj
  have hKcard : Fintype.card K45 = 3 := by decide
  rw [hKcard] at hc
  norm_num at hc

private theorem nonunit_mem_H45_or_J45 (z : ZMod 45) (hz : ¬ IsUnit z) :
    z ∈ H45 ∨ z ∈ J45 := by
  revert z
  decide

/-- Every five-coordinate SHC family in `ZMod 45` has a generator
coordinate.  The tight subgroup cover is ruled out by a quotient-pigeonhole
contradiction using dissociation alone. -/
theorem shc_hasGeneratorCoordinate_zmod_forty_five
    (h : Fin 5 → ZMod 45) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  by_contra hno
  have hnonunit : ∀ i, ¬ IsUnit (h i) := by
    intro i hi
    apply hno
    exact ⟨i, zmod_generator_of_isUnit _ hi⟩
  let A := Finset.univ.filter fun i ↦ h i ∈ H45
  let B := Finset.univ.filter fun i ↦ h i ∈ J45
  have hHcard : Fintype.card H45 = 15 := by decide
  have hJcard : Fintype.card J45 = 9 := by decide
  have hA : A.card < 4 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) H45
      cyclicSHCOddLowerBound_four
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hB : B.card < 3 := by
    apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J45
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hcover : (Finset.univ : Finset (Fin 5)) ⊆ A ∪ B := by
    intro i hi
    rcases nonunit_mem_H45_or_J45 (h i) (hnonunit i) with hiH | hiJ
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiH⟩)
    · exact Finset.mem_union_right A (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩)
  have hcard : 5 ≤ A.card + B.card := by
    have hle := Finset.card_le_card hcover
    have hu := Finset.card_union_le A B
    simpa using hle.trans hu
  have hAcard : A.card = 3 := by omega
  have hBcard : B.card = 2 := by omega
  have hUcard : (A ∪ B).card = 5 := by
    have hle := Finset.card_le_card hcover
    have hle' : 5 ≤ (A ∪ B).card := by simpa using hle
    have hu : (A ∪ B).card ≤ 5 := by simpa using Finset.card_le_univ (A ∪ B)
    omega
  have hIcard : (A ∩ B).card = 0 := by
    have hsum := Finset.card_union_add_card_inter A B
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hIcard
  let eA : Fin 3 ↪ Fin 5 := (A.orderEmbOfFin hAcard).toEmbedding
  let eB : Fin 2 ↪ Fin 5 := (B.orderEmbOfFin hBcard).toEmbedding
  have hrange : Disjoint (Set.range eA) (Set.range eB) := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    obtain ⟨j, rfl⟩ := hiA
    obtain ⟨k, hik⟩ := hiB
    have hjeA : eA j ∈ A := A.orderEmbOfFin_mem hAcard j
    have hkeB : eB k ∈ B := B.orderEmbOfFin_mem hBcard k
    apply (Finset.disjoint_left.mp hdisj hjeA)
    simpa [hik] using hkeB
  let e : Fin 5 ↪ Fin 5 := Fin.Embedding.append hrange
  have hebij : Function.Bijective e := by
    exact (Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, by simp⟩
  let p : Fin 5 ≃ Fin 5 := Equiv.ofBijective e hebij
  let a : Fin 3 → H45 := fun i ↦
    ⟨h (eA i), (Finset.mem_filter.mp (A.orderEmbOfFin_mem hAcard i)).2⟩
  let b : Fin 2 → J45 := fun i ↦
    ⟨h (eB i), (Finset.mem_filter.mp (B.orderEmbOfFin_mem hBcard i)).2⟩
  have happend :
      Fin.append (fun i ↦ (a i : ZMod 45)) (fun i ↦ (b i : ZMod 45)) = h ∘ p := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [a, eA, p, e, Fin.Embedding.append]
    | right i => simp [b, eB, p, e, Fin.Embedding.append]
  apply no_shc_three_H_two_J a b
  rw [happend]
  exact hs.reindex_equiv h p

/-- Every five-coordinate SHC family over an odd `ZMod` in the strict window
33 through 61 has a generator coordinate. -/
theorem shc_hasGeneratorCoordinate_zmod_five_of_odd_window
    {N : ℕ} (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 61)
    (h : Fin 5 → ZMod N) (hs : SHC h) : HasGeneratorCoordinate h := by
  by_cases hN : N = 45
  · subst N
    exact shc_hasGeneratorCoordinate_zmod_forty_five h hs
  · exact shc_hasGeneratorCoordinate_zmod_five_of_odd_window_ne_forty_five
      hodd hlower hupper hN h hs

end MinModulus
