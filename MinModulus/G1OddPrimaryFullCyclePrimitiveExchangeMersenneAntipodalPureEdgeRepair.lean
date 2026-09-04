/-
# Specializing antipodal defect repair to the pure external edge

At the exact-Mersenne endpoint, the antipodal external row is a pure edge.
Its center and external owner lie off the pointed leaf, so it vanishes at
every non-root primary owner.  This discharges the only extra hypothesis of
the generic private-row repair theorem and produces the entire repaired
witness family directly from the antipodal geometry.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalDefectRepair

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A pure edge whose center and owner are off a pointed leaf vanishes at
every leaf coordinate other than its root endpoint. -/
theorem pureEdgeCoeffs_pointedLeaf_eq_zero
    {n d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (z : Fin d) (r center owner : Fin n) (hr : leaf z = r)
    (hcenterOff : center ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hownerOff : owner ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (i : Fin d) (hiz : i ≠ z) :
    pureEdgeCoeffs center owner r (leaf i) = 0 := by
  have hleafRoot : leaf i ≠ r := by
    rw [← hr]
    exact fun h ↦ hiz (hleaf h)
  have hleafCenter : leaf i ≠ center := by
    intro hi
    apply hcenterOff
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hleafOwner : leaf i ≠ owner := by
    intro hi
    apply hownerOff
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  simp [pureEdgeCoeffs, hleafCenter, hleafOwner, hleafRoot]

/-- In the pure-edge case, every member of the negative subset repairs the
localized root defect.  The vanishing premise required by the generic repair
theorem follows solely from the pointed-leaf geometry. -/
theorem pureEdge_normalizedPrivateRow_defectRepair
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (z : Fin d) (r : Fin n) (hr : leaf z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (leaf i) =
        signedPairCoeffs (leaf i) r)
    (center owner : Fin n)
    (hcenterOff : center ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hownerOff : owner ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (qrel : Fin n → ℤ)
    (hqrel : qrel = pureEdgeCoeffs center owner r -
      normalizedPrivateSubsetAggregate g y B p leaf z A M)
    (hrel : SingleFloorDefectZeroRelation g r qrel)
    (m : Fin d) (hmM : m ∈ M) :
    let row := normalizedCanonicalPrivateRow g y B p (leaf m)
    let repaired := qrel - row
    Witness g (g r - g (leaf m)) repaired ∧
      repaired r = -1 ∧ repaired (leaf m) = 0 := by
  classical
  have hexternal : ∀ i, i ∈ M →
      pureEdgeCoeffs center owner r (leaf i) = 0 := by
    intro i hiM
    have hiz : i ≠ z := by
      intro hiz
      subst i
      exact (Finset.disjoint_left.mp hdisjoint) hzA hiM
    exact pureEdgeCoeffs_pointedLeaf_eq_zero leaf hleaf z r center owner
      hr hcenterOff hownerOff i hiz
  exact normalizedPrivateRow_defectRepair
    g y B p leaf hleaf z r hr A M hdisjoint hcard hzA hrows
      (pureEdgeCoeffs center owner r) qrel hexternal hqrel hrel m hmM

/-- The pointed positive root forces the negative subset to be nonempty, so
the pure-edge defect always admits at least one repaired private-row witness. -/
theorem exists_pureEdge_normalizedPrivateRow_defectRepair
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (z : Fin d) (r : Fin n) (hr : leaf z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (leaf i) =
        signedPairCoeffs (leaf i) r)
    (center owner : Fin n)
    (hcenterOff : center ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hownerOff : owner ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (qrel : Fin n → ℤ)
    (hqrel : qrel = pureEdgeCoeffs center owner r -
      normalizedPrivateSubsetAggregate g y B p leaf z A M)
    (hrel : SingleFloorDefectZeroRelation g r qrel) :
    ∃ m : Fin d, ∃ _hmM : m ∈ M,
      let row := normalizedCanonicalPrivateRow g y B p (leaf m)
      let repaired := qrel - row
      Witness g (g r - g (leaf m)) repaired ∧
        repaired r = -1 ∧ repaired (leaf m) = 0 := by
  classical
  have hexternal : ∀ i, i ∈ M →
      pureEdgeCoeffs center owner r (leaf i) = 0 := by
    intro i hiM
    have hiz : i ≠ z := by
      intro hiz
      subst i
      exact (Finset.disjoint_left.mp hdisjoint) hzA hiM
    exact pureEdgeCoeffs_pointedLeaf_eq_zero leaf hleaf z r center owner
      hr hcenterOff hownerOff i hiz
  exact exists_normalizedPrivateRow_defectRepair
    g y B p leaf hleaf z r hr A M hdisjoint hcard hzA hrows
      (pureEdgeCoeffs center owner r) qrel hexternal hqrel hrel

/-- At an antipodal middle parameter, the pure-edge center lies off the
pointed leaf.  Otherwise the all-but-root deletion law would put that retained
coordinate in the deletion set. -/
theorem TwoRetainedCanonicalPrivatePresentation.antipodal_center_not_mem_leaf
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (r : Fin n)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (k₀ k : ℤ)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2)) :
    (if k₀ = -1 then p.z else p.x) ∉
      (Finset.univ : Finset (Fin d)).image leaf := by
  let center : Fin n := if k₀ = -1 then p.z else p.x
  have hcenterR : center ≠ r := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
      simpa only [hk₀, if_true, hrx] using p.x_ne_z.symm
    · have hk₀Ne : k₀ ≠ -1 := by omega
      have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
      simpa only [hk₀Ne, if_false, hrz] using p.x_ne_z
  have hcenterNotB : center ∉ B := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · simpa only [hk₀, if_true] using p.z_not_mem
    · have hk₀Ne : k₀ ≠ -1 := by omega
      simpa only [hk₀Ne, if_false] using p.x_not_mem
  intro hcenterLeaf
  exact hcenterNotB (hdeleted center hcenterLeaf hcenterR)

/-- Lossless antipodal endpoint with the repaired family installed.  The
common-omission branch is unchanged.  In the exact-negative branch, every
negative binary digit supplies a repaired witness on the same canonical
presentation, not merely an existential witness from detached subset data. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_pureEdgeRepair_dichotomy
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ k : ℤ)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
        p.scalar b • y = s • v ∧
        ∃ cPlus cMinus qrel : Fin n → ℤ, ∃ i : Fin n,
          Witness g (p.scalar b • y) cPlus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cPlus j = 0) ∧
          Witness g (-(p.scalar b • y)) cMinus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cMinus j = 0) ∧
          cMinus r = -1 ∧
          i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          (i = r ∨ 2 ≤ cPlus i) ∧
          p.coeff b i + 2 ≤ cPlus i ∧
          qrel = p.coeff b + cMinus ∧
          SingleFloorDefectZeroRelation g r qrel ∧
          qrel center = 2 ∧ qrel (b : Fin n) = -1 ∧
          ((∃ j : Fin n,
              j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
                cPlus j = -1 ∧ cMinus j = -1) ∨
            ∃ A M : Finset (Fin d),
              cMinus = -cPlus ∧ Disjoint A M ∧
              A.card = M.card ∧ ⟨0, by omega⟩ ∈ A ∧
              cPlus = normalizedPrivateSubsetAggregate
                g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
              qrel = p.coeff b - normalizedPrivateSubsetAggregate
                g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
              (binarySubsetValue A = binarySubsetValue M + s ∨
                binarySubsetValue A + (2 ^ d - 1) =
                  binarySubsetValue M + s) ∧
              ∀ m, m ∈ M →
                let row := normalizedCanonicalPrivateRow
                  g y B p (leaf (e m))
                let repaired := qrel - row
                Witness g (g r - g (leaf (e m))) repaired ∧
                  repaired r = -1 ∧ repaired (leaf (e m)) = 0) := by
  dsimp only
  let center : Fin n := if k₀ = -1 then p.z else p.x
  obtain ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
      cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus,
      hminusOff, hminusR, hiLeaf, hiLocalized, hiGap, hqrel,
      hdefect, hqcenter, hqb, houtcome⟩ :=
    p.exists_antipodal_mersenneLeaf_privateRowDefect_dichotomy
      g hg y root v B hyq hfullOdd hprimitive hd hv leaf hleaf e
        hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hprimaryWeight
          b hb hr hantipodal howner hweight
  have hmiddle : k₀ = -1 ∨ k₀ = 0 := by
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · exact Or.inl hk₀
    · exact Or.inr hk₀
  have hrPrimitive : r = primitiveMiddleInsertedCoordinate p k₀ := by
    simpa only [primitiveMiddleInsertedCoordinate] using hr
  have hf : Function.Injective (fun j ↦ leaf (e j)) :=
    hleaf.comp e.injective
  have hrows : ∀ j, j ≠ ⟨0, by omega⟩ →
      normalizedCanonicalPrivateRow g y B p (leaf (e j)) =
        signedPairCoeffs (leaf (e j)) r := by
    intro j hjzero
    have hjB : leaf (e j) ∈ B := (hleafMem j).2 hjzero
    rw [normalizedCanonicalPrivateRow_of_mem
      g y B p (leaf (e j)) hjB, hrPrimitive]
    exact p.primitive_primaryMiddle_owner_mul_coeff_eq_signedPair
      g y B hyq hfullOdd hprimitive ⟨leaf (e j), hjB⟩ k₀ hmiddle
        (hprimaryWeight j hjB)
  have hcenterOff := p.antipodal_center_not_mem_leaf
    g y B leaf r hdeleted k₀ k hr hantipodal
  have hcenterOffF : center ∉
      (Finset.univ : Finset (Fin d)).image (fun j ↦ leaf (e j)) := by
    intro hmem
    apply hcenterOff
    obtain ⟨j, _hj, hj⟩ := Finset.mem_image.mp hmem
    exact Finset.mem_image.mpr ⟨e j, Finset.mem_univ (e j), hj⟩
  have hbF : (b : Fin n) ∉
      (Finset.univ : Finset (Fin d)).image (fun j ↦ leaf (e j)) := by
    intro hmem
    apply hb
    obtain ⟨j, _hj, hj⟩ := Finset.mem_image.mp hmem
    exact Finset.mem_image.mpr ⟨e j, Finset.mem_univ (e j), hj⟩
  have hnewOutcome :
      (∃ j : Fin n,
          j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
            cPlus j = -1 ∧ cMinus j = -1) ∨
        ∃ A M : Finset (Fin d),
          cMinus = -cPlus ∧ Disjoint A M ∧
          A.card = M.card ∧ ⟨0, by omega⟩ ∈ A ∧
          cPlus = normalizedPrivateSubsetAggregate
            g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M ∧
          qrel = p.coeff b - normalizedPrivateSubsetAggregate
            g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M ∧
          (binarySubsetValue A = binarySubsetValue M + s ∨
            binarySubsetValue A + (2 ^ d - 1) =
              binarySubsetValue M + s) ∧
          ∀ m, m ∈ M →
            let row := normalizedCanonicalPrivateRow
              g y B p (leaf (e m))
            let repaired := qrel - row
            Witness g (g r - g (leaf (e m))) repaired ∧
              repaired r = -1 ∧ repaired (leaf (e m)) = 0 := by
    rcases houtcome with hcommon |
        ⟨A, M, hneg, hdisjoint, hcard, hzero, hcPrivate,
          hqPrivate, harithmetic⟩
    · exact Or.inl hcommon
    · right
      refine ⟨A, M, hneg, hdisjoint, hcard, hzero, hcPrivate,
        hqPrivate, harithmetic, ?_⟩
      intro m hmM
      have hqPure : qrel = pureEdgeCoeffs center (b : Fin n) r -
          normalizedPrivateSubsetAggregate
            g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M := by
        rw [← hshape]
        exact hqPrivate
      exact pureEdge_normalizedPrivateRow_defectRepair
        g y B p (fun j ↦ leaf (e j)) hf ⟨0, by omega⟩ r hrzero
          A M hdisjoint hcard hzero hrows center (b : Fin n)
            hcenterOffF hbF qrel hqPure hdefect m hmM
  exact ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
    cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus, hminusOff,
    hminusR, hiLeaf, hiLocalized, hiGap, hqrel, hdefect,
    hqcenter, hqb, hnewOutcome⟩

end MinModulus
