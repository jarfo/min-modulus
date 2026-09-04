import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersennePointedNormalForm

namespace MinModulus

open Finset

variable {n : ℕ}

theorem sdiff_eq_union_of_inter_threePartition
    (B L S T F : Finset (Fin n))
    (hinter : B ∩ L = S)
    (hTsub : T ⊆ B \ L)
    (hpartition : B = (S ∪ T) ∪ F)
    (hFsub : F ⊆ B \ (S ∪ T)) :
    B \ L = T ∪ F ∧ Disjoint T F := by
  classical
  have hSsubL : S ⊆ L := by
    rw [← hinter]
    exact Finset.inter_subset_right
  have hFsubBL : F ⊆ B \ L := by
    intro b hbF
    have hbF' := Finset.mem_sdiff.mp (hFsub hbF)
    refine Finset.mem_sdiff.mpr ⟨hbF'.1, ?_⟩
    intro hbL
    have hbS : b ∈ S := by
      rw [← hinter]
      exact Finset.mem_inter.mpr ⟨hbF'.1, hbL⟩
    exact hbF'.2 (Finset.mem_union_left T hbS)
  have heq : B \ L = T ∪ F := by
    apply Finset.Subset.antisymm
    · intro b hbBL
      have hbB := (Finset.mem_sdiff.mp hbBL).1
      have hbNotL := (Finset.mem_sdiff.mp hbBL).2
      have hbPartition : b ∈ (S ∪ T) ∪ F := by
        rw [← hpartition]
        exact hbB
      rcases Finset.mem_union.mp hbPartition with hbST | hbF
      · rcases Finset.mem_union.mp hbST with hbS | hbT
        · exact (hbNotL (hSsubL hbS)).elim
        · exact Finset.mem_union_left F hbT
      · exact Finset.mem_union_right T hbF
    · exact Finset.union_subset hTsub hFsubBL
  have hdisjoint : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro b hbT hbF
    exact (Finset.mem_sdiff.mp (hFsub hbF)).2
      (Finset.mem_union_right S hbT)
  exact ⟨heq, hdisjoint⟩

def PrimitiveMiddleExactMersenneFiveExternalCapacityResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  PrimitiveMiddleExactMersennePointedResidual g y B leaf base ∧
    let L := (Finset.univ : Finset (Fin d)).image leaf
    ∃ T F : Finset (Fin n),
      3 ≤ T.card ∧ T.card ≤ 5 ∧ F.card ≤ 2 ∧
      B \ L = T ∪ F ∧ Disjoint T F ∧
      T.card + F.card = 5 ∧
      ((T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2)) ∧
      (∀ i j k : ℕ,
        L.card.choose i * T.card.choose j * F.card.choose k ≤ q) ∧
      48 * (L.card.choose (L.card / 2) *
        F.card.choose (F.card / 2)) < 2 ^ B.card

theorem PrimitiveMiddleExactMersennePointedResidual.toFiveExternalCapacityResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q))
    (hresidual :
      PrimitiveMiddleExactMersennePointedResidual g y B leaf base) :
    PrimitiveMiddleExactMersenneFiveExternalCapacityResidual
      g y B leaf base := by
  classical
  refine ⟨hresidual, ?_⟩
  rcases hresidual.1 with
    ⟨p, S, T₀, Sfull, k₀, w, hfixed, missing, hpunctured,
      hmissing, hCeq, hSeq, hcard, hw, hleafOrder, hLcap,
      hLcoset, hLgap, hfive, hseparated, hsecondary,
      hcriticalBound, hn, hBcard, hexternal, hdLower, hdUpper⟩
  rcases hfixed with
    ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
      hrows, hcomplete, hwindow⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hSrows : ∀ b : ↥B, (b : Fin n) ∈ Sfull →
      p.weight b = 2 * k₀ := by
    intro b hb
    exact (hrows b hb).1
  have hthree := hsecondary.toThreeResiduePartition
    g y B L Sfull p k₀ hprimitive hyq hfullOdd hmiddle hwindow
      hSsub hSrows (by simpa only [r, L] using hcomplete)
  have hrL : r ∈ L := by
    exact Finset.mem_image.mpr
      ⟨missing, Finset.mem_univ _, by simpa only [r] using hmissing⟩
  have hLnonempty : L.Nonempty := ⟨r, hrL⟩
  rcases hthree with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hUTcap, hfinal⟩
  rcases hfinal with ⟨F, hpartition, hFsub, hFcase⟩
  have hFsimple : F = ∅ ∨
      ∃ f : Fin n, f ∈ F ∧
        ∀ b : ↥B,
          ((b : Fin n) ∈ F ↔
            g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y) := by
    rcases hFcase with hFempty | hFfull
    · exact Or.inl hFempty
    · rcases hFfull with
        ⟨_k₂, f, hfF, _hk₂Mem, _hk₂Ne₀, _hk₂Ne₁,
          _hFrows, hFcomplete⟩
      exact Or.inr ⟨f, hfF, hFcomplete⟩
  have hcap := primaryUnion_threeResidue_fullLayerCapacity
    g hg y B L Sfull T F p k₀ hyq hfullOdd hLnonempty hLcoset hrL
      (by simpa only [r] using hcomplete) t htT hTsub hTcomplete
        hUTcap hFsub hFsimple
  have hcrit :=
    fortyEight_mul_primaryFinalCentralChoose_lt_two_pow_transversalCard
      B L T F hretained hcritical hTcard hcap
  have hrNotB : r ∉ B := by
    intro hrB
    have hmB : leaf missing ∈ B := by
      rw [hmissing]
      exact hrB
    have hbad : missing ≠ missing := (hpunctured missing).1 hmB
    exact hbad rfl
  have hSsubL : Sfull ⊆ L := by
    rw [hSeq]
    exact Finset.erase_subset _ _
  have hBinterL : B ∩ L = Sfull := by
    ext b
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hbB, hbL⟩
      rw [hSeq]
      exact Finset.mem_erase.mpr
        ⟨by
          intro hbr
          rw [hbr] at hbB
          exact hrNotB hbB,
         hbL⟩
    · intro hbS
      exact ⟨hSsub hbS, hSsubL hbS⟩
  obtain ⟨hexternalPartition, hTFdisjoint⟩ :=
    sdiff_eq_union_of_inter_threePartition
      B L Sfull T F hBinterL hTsub hpartition hFsub
  have hTFcard : T.card + F.card = 5 := by
    rw [hexternalPartition] at hexternal
    rw [Finset.card_union_of_disjoint hTFdisjoint] at hexternal
    exact hexternal
  have hTle : T.card ≤ 5 := by omega
  have hFle : F.card ≤ 2 := by omega
  have hprofiles :
      (T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2) := by
    omega
  change ∃ T F : Finset (Fin n),
      3 ≤ T.card ∧ T.card ≤ 5 ∧ F.card ≤ 2 ∧
      B \ L = T ∪ F ∧ Disjoint T F ∧
      T.card + F.card = 5 ∧
      ((T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2)) ∧
      (∀ i j k : ℕ,
        L.card.choose i * T.card.choose j * F.card.choose k ≤ q) ∧
      48 * (L.card.choose (L.card / 2) *
        F.card.choose (F.card / 2)) < 2 ^ B.card
  exact ⟨T, F, hTcard, hTle, hFle, hexternalPartition,
    hTFdisjoint, hTFcard, hprofiles, hcap, hcrit⟩

end MinModulus
