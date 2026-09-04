/-
# Selected incidence charge for the complete Mersenne external fiber

The adjacent-heavy and primary-omission arms of the external-fiber split
contain actual leaf coordinates, but their quantitative theorem previously
remembered only owner counts.  This module chooses those coordinates and
partitions each owner family into exact coordinate fibers.

After doubling the owner-count inequality, root omissions contribute their
two displayed opposite-target omissions, primary omissions contribute two
incidences at their selected non-root primary leaf, and residual owners are
absorbed by their exact matrix mass.  The adjacent arm similarly becomes two
selected units at a genuine heavy leaf coordinate.  This yields one weighted
incidence alternative on the original complete secondary fiber.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneExternalTargetCapacity

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A specified leaf coordinate carrying the heavy incidence supplied by an
adjacent external row. -/
def MersenneLeafAdjacentHeavyIncidenceAt
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (b : ↥B) (i : Fin n) : Prop :=
  i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧ p.scalar b • y = s • v ∧
      ∃ c : Fin n → ℤ, Witness g (p.scalar b • y) c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        2 ≤ c i

/-- An adjacent-heavy row is exactly a row with a heavy incidence at some
specified leaf coordinate. -/
theorem mersenneLeafAdjacentHeavyRow_iff_exists_incidenceAt
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (b : ↥B) :
    MersenneLeafAdjacentHeavyRow g y v B p leaf b ↔
      ∃ i : Fin n,
        MersenneLeafAdjacentHeavyIncidenceAt g y v B p leaf b i := by
  constructor
  · rintro ⟨s, hs0, hsq, htarget, c, hc, hoff, i, hiLeaf, hiHeavy⟩
    exact ⟨i, hiLeaf, s, hs0, hsq, htarget, c, hc, hoff, hiHeavy⟩
  · rintro ⟨i, hiLeaf, s, hs0, hsq, htarget, c, hc, hoff, hiHeavy⟩
    exact ⟨s, hs0, hsq, htarget, c, hc, hoff, i, hiLeaf, hiHeavy⟩

/-- Canonically selected heavy leaf coordinate, with the owner coordinate as
an irrelevant fallback outside the adjacent-heavy predicate. -/
noncomputable def mersenneLeafAdjacentHeavyCoordinate
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (b : ↥B) : Fin n := by
  classical
  by_cases hrow : MersenneLeafAdjacentHeavyRow g y v B p leaf b
  · exact Classical.choose
      ((mersenneLeafAdjacentHeavyRow_iff_exists_incidenceAt
        g y v B p leaf b).mp hrow)
  · exact (b : Fin n)

/-- The selected coordinate retains its concrete same-target witness and
coefficient at least two. -/
theorem mersenneLeafAdjacentHeavyCoordinate_spec
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (b : ↥B)
    (hrow : MersenneLeafAdjacentHeavyRow g y v B p leaf b) :
    MersenneLeafAdjacentHeavyIncidenceAt g y v B p leaf b
      (mersenneLeafAdjacentHeavyCoordinate g y v B p leaf b) := by
  classical
  rw [mersenneLeafAdjacentHeavyCoordinate, dif_pos hrow]
  exact Classical.choose_spec
    ((mersenneLeafAdjacentHeavyRow_iff_exists_incidenceAt
      g y v B p leaf b).mp hrow)

/-- Adjacent-heavy owners whose selected heavy incidence is at `i`. -/
noncomputable def adjacentHeavyOwnersAt
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (E : Finset ↥B) (i : Fin n) : Finset ↥B :=
  ownersSatisfying E (fun b ↦
    MersenneLeafAdjacentHeavyRow g y v B p leaf b ∧
      mersenneLeafAdjacentHeavyCoordinate g y v B p leaf b = i)

/-- The selected heavy-coordinate fibers partition all adjacent-heavy owners
exactly over the pointed leaf image. -/
theorem card_adjacentHeavyOwners_eq_sum_selectedCoordinateFibers
    {n d : ℕ} (g : Fin n → G) (y v : G)
    (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (E : Finset ↥B) :
    (ownersSatisfying E (fun b ↦
      MersenneLeafAdjacentHeavyRow g y v B p leaf b)).card =
      ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
        (adjacentHeavyOwnersAt g y v B p leaf E i).card := by
  classical
  let S := ownersSatisfying E (fun b ↦
    MersenneLeafAdjacentHeavyRow g y v B p leaf b)
  let L := (Finset.univ : Finset (Fin d)).image leaf
  let coord : ↥B → Fin n := fun b ↦
    mersenneLeafAdjacentHeavyCoordinate g y v B p leaf b
  have hmaps : ∀ b ∈ S, coord b ∈ L := by
    intro b hbS
    have hb := (mem_ownersSatisfying_iff E
      (fun u ↦ MersenneLeafAdjacentHeavyRow g y v B p leaf u) b).mp
        (by simpa only [S] using hbS)
    exact (mersenneLeafAdjacentHeavyCoordinate_spec
      g y v B p leaf b hb.2).1
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (ownersSatisfying E (fun b ↦
        MersenneLeafAdjacentHeavyRow g y v B p leaf b)).card = S.card := rfl
    _ = ∑ i ∈ L, (S.filter fun b ↦ coord b = i).card := hcard
    _ = ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
        (adjacentHeavyOwnersAt g y v B p leaf E i).card := by
      apply Finset.sum_congr rfl
      intro i _hiL
      congr 1
      ext b
      simp only [S, coord, adjacentHeavyOwnersAt,
        mem_ownersSatisfying_iff, Finset.mem_filter]
      aesop

/-- A specified non-root primary index carrying a common omission and its
actual normalized primary signed-pair row. -/
def AntipodalRepairPrimaryOmissionIncidenceAt
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (target : G)
    (i : Fin d) : Prop :=
  ∃ _hiB : f i ∈ B,
    i ≠ z ∧
      ∃ cPlus cMinus : Fin n → ℤ,
        Witness g target cPlus ∧ Witness g (-target) cMinus ∧
          cPlus (f i) = -1 ∧ cMinus (f i) = -1 ∧
          normalizedCanonicalPrivateRow g y B p (f i) =
            signedPairCoeffs (f i) r

/-- A primary omission charge is exactly an incidence at one specified
non-root primary index. -/
theorem antipodalRepairPrimaryOmissionCharge_iff_exists_incidenceAt
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (target : G) :
    AntipodalRepairPrimaryOmissionCharge g y B p f z r target ↔
      ∃ i : Fin d,
        AntipodalRepairPrimaryOmissionIncidenceAt
          g y B p f z r target i := by
  rfl

/-- Canonically selected non-root primary omission index. -/
noncomputable def antipodalRepairPrimaryOmissionIndex
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (target : G) : Fin d := by
  classical
  by_cases hcharge : AntipodalRepairPrimaryOmissionCharge
      g y B p f z r target
  · exact Classical.choose
      ((antipodalRepairPrimaryOmissionCharge_iff_exists_incidenceAt
        g y B p f z r target).mp hcharge)
  · exact z

/-- The selected primary index retains the two opposite-target omissions and
the actual normalized owner-to-root row. -/
theorem antipodalRepairPrimaryOmissionIndex_spec
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (target : G)
    (hcharge : AntipodalRepairPrimaryOmissionCharge
      g y B p f z r target) :
    AntipodalRepairPrimaryOmissionIncidenceAt g y B p f z r target
      (antipodalRepairPrimaryOmissionIndex g y B p f z r target) := by
  classical
  rw [antipodalRepairPrimaryOmissionIndex, dif_pos hcharge]
  exact Classical.choose_spec
    ((antipodalRepairPrimaryOmissionCharge_iff_exists_incidenceAt
      g y B p f z r target).mp hcharge)

/-- Primary-omission owners whose selected common omission has index `i`. -/
noncomputable def primaryOmissionOwnersAt
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n)
    (E : Finset ↥B) (i : Fin d) : Finset ↥B :=
  ownersSatisfying E (fun b ↦
    AntipodalRepairPrimaryOmissionCharge
      g y B p f z r (p.scalar b • y) ∧
    antipodalRepairPrimaryOmissionIndex
      g y B p f z r (p.scalar b • y) = i)

/-- The selected omission-index fibers partition all primary-omission owners
exactly over the non-root pointed indices. -/
theorem card_primaryOmissionOwners_eq_sum_selectedIndexFibers
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n)
    (E : Finset ↥B) :
    (ownersSatisfying E (fun b ↦
      AntipodalRepairPrimaryOmissionCharge
        g y B p f z r (p.scalar b • y))).card =
      ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
        (primaryOmissionOwnersAt g y B p f z r E i).card := by
  classical
  let P : ↥B → Prop := fun b ↦
    AntipodalRepairPrimaryOmissionCharge
      g y B p f z r (p.scalar b • y)
  let S := ownersSatisfying E P
  let I := (Finset.univ : Finset (Fin d)).erase z
  let index : ↥B → Fin d := fun b ↦
    antipodalRepairPrimaryOmissionIndex
      g y B p f z r (p.scalar b • y)
  have hmaps : ∀ b ∈ S, index b ∈ I := by
    intro b hbS
    have hb := (mem_ownersSatisfying_iff E P b).mp
      (by simpa only [S] using hbS)
    have hspec := antipodalRepairPrimaryOmissionIndex_spec
      g y B p f z r (p.scalar b • y) hb.2
    rcases hspec with ⟨_hiB, hiNe, _hdata⟩
    exact Finset.mem_erase.mpr ⟨hiNe, Finset.mem_univ _⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (ownersSatisfying E (fun b ↦
        AntipodalRepairPrimaryOmissionCharge
          g y B p f z r (p.scalar b • y))).card = S.card := rfl
    _ = ∑ i ∈ I, (S.filter fun b ↦ index b = i).card := hcard
    _ = ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
        (primaryOmissionOwnersAt g y B p f z r E i).card := by
      apply Finset.sum_congr rfl
      intro i _hiI
      congr 1
      ext b
      simp only [P, S, index, primaryOmissionOwnersAt,
        mem_ownersSatisfying_iff, Finset.mem_filter]
      aesop

/-- Weighted complete-fiber alternative.  The adjacent branch is partitioned
into selected heavy-coordinate incidences.  In the antipodal branch, two
units per owner are charged to the fixed root or a selected non-root primary
index, the unique cancellation costs two units, and residual owners are paid
by their exact matrix incidence mass. -/
theorem completeExternalFiber_selectedIncidenceCharge
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
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ k : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (T : Finset (Fin n))
    (hTsub : T ⊆ B \ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hparameter : (k = k₀ + 1 ∨ k₀ = k + 1) ∨
      (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (hrows : ∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧ p.weight b = 2 * k) :
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    let z : Fin d := ⟨0, by omega⟩
    let E := deletedOwnerSubfiber B T
    2 * E.card =
        2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
          (adjacentHeavyOwnersAt g y v B p leaf E i).card ∨
      2 * E.card ≤
        2 * (ownersSatisfying E (fun b ↦
          AntipodalRepairRootCommonOmission g (p.scalar b • y) r)).card +
        2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
          (primaryOmissionOwnersAt g y B p f z r E i).card + 2 +
        ∑ b ∈ ownersSatisfying E (fun b ↦
          AntipodalRepairResidualMatrix g y B p f z r v b),
            antipodalRepairResidualIncidenceMass g y B p f z r v b := by
  dsimp only
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  let z : Fin d := ⟨0, by omega⟩
  let E := deletedOwnerSubfiber B T
  let Adj : ↥B → Prop := fun b ↦
    MersenneLeafAdjacentHeavyRow g y v B p leaf b
  let Root : ↥B → Prop := fun b ↦
    AntipodalRepairRootCommonOmission g (p.scalar b • y) r
  let Primary : ↥B → Prop := fun b ↦
    AntipodalRepairPrimaryOmissionCharge
      g y B p f z r (p.scalar b • y)
  let Residual : ↥B → Prop := fun b ↦
    AntipodalRepairResidualMatrix g y B p f z r v b
  have hbase :=
    completeExternalFiber_allAdjacentHeavy_or_card_le_omissionCharges_add_one_add_residualMatrices
      g hg y root v B p hyq hfullOdd hprimitive hd hv leaf hleaf e
        hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hmiddle
          hprimaryWeight T hTsub hr hparameter hrows
  rcases hbase with hAdj | hAntipodal
  · left
    have hAdjOwners : ownersSatisfying E Adj = E := by
      ext b
      simp only [mem_ownersSatisfying_iff]
      constructor
      · exact fun h ↦ h.1
      · intro hbE
        exact ⟨hbE, hAdj b hbE⟩
    have hpartition := card_adjacentHeavyOwners_eq_sum_selectedCoordinateFibers
      g y v B p leaf E
    have hAdjOwners' : ownersSatisfying E (fun b ↦
        MersenneLeafAdjacentHeavyRow g y v B p leaf b) = E := by
      simpa only [Adj] using hAdjOwners
    have hcard : E.card =
        ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
          (adjacentHeavyOwnersAt g y v B p leaf E i).card := by
      rw [hAdjOwners'] at hpartition
      exact hpartition
    have hweighted := congrArg (fun u : ℕ ↦ 2 * u) hcard
    simpa only [E] using hweighted
  · right
    have hprimaryPartition :=
      card_primaryOmissionOwners_eq_sum_selectedIndexFibers
        g y B p f z r E
    have hresidualFour := four_mul_card_residualOwners_le_sum_incidenceMass
      g y B p f z r v E
    have hresidualTwo :
        2 * (ownersSatisfying E Residual).card ≤
          ∑ b ∈ ownersSatisfying E Residual,
            antipodalRepairResidualIncidenceMass g y B p f z r v b := by
      have hresidualFour' :
          4 * (ownersSatisfying E Residual).card ≤
            ∑ b ∈ ownersSatisfying E Residual,
              antipodalRepairResidualIncidenceMass
                g y B p f z r v b := by
        simpa only [Residual] using hresidualFour
      omega
    have hAntipodal' : E.card ≤
        (ownersSatisfying E Root).card +
          (ownersSatisfying E Primary).card + 1 +
          (ownersSatisfying E Residual).card := by
      simpa only [E, Root, Primary, Residual, f, z] using hAntipodal
    have hprimaryPartition' :
        (ownersSatisfying E Primary).card =
          ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
            (primaryOmissionOwnersAt g y B p f z r E i).card := by
      simpa only [Primary] using hprimaryPartition
    have hweighted : 2 * E.card ≤
        2 * (ownersSatisfying E Root).card +
          2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
            (primaryOmissionOwnersAt g y B p f z r E i).card + 2 +
          ∑ b ∈ ownersSatisfying E Residual,
            antipodalRepairResidualIncidenceMass g y B p f z r v b := by
      omega
    simpa only [E, Root, Residual, f, z] using hweighted

/-- The secondary fiber stored by the exact five-external-row endpoint has,
simultaneously, at least three owners, injective nonzero-target capacity, and
the complete selected-incidence charge above. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.secondaryFiber_selectedIncidenceCharge
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
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (L : Finset (Fin n))
    (hL : L = (Finset.univ : Finset (Fin d)).image leaf)
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows g y B L p k₀) :
    ∃ T : Finset (Fin n),
      3 ≤ T.card ∧ T ⊆ B \ L ∧ T.card ≤ addOrderOf y - 1 ∧
      (let f : Fin d → Fin n := fun i ↦ leaf (e i)
       let z : Fin d := ⟨0, by omega⟩
       let E := deletedOwnerSubfiber B T
       2 * E.card =
           2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
             (adjacentHeavyOwnersAt g y v B p leaf E i).card ∨
         2 * E.card ≤
           2 * (ownersSatisfying E (fun b ↦
             AntipodalRepairRootCommonOmission
               g (p.scalar b • y) r)).card +
           2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
             (primaryOmissionOwnersAt g y B p f z r E i).card + 2 +
           ∑ b ∈ ownersSatisfying E (fun b ↦
             AntipodalRepairResidualMatrix g y B p f z r v b),
               antipodalRepairResidualIncidenceMass
                 g y B p f z r v b) := by
  rcases hfive with
    ⟨T, k, _t, _F, hTcard, _hTle, _hFle, hTsub, _htT,
      _hkMem, _hkNe, hparameter, hrows, _hTexact, _hTadjacent,
      _hTcomplete, _hTseparated, _hpartition, _hdisjoint,
      _hcard, _hprofiles, _hFcase, _hcap, _hcritical⟩
  let E := deletedOwnerSubfiber B T
  have hTsubB : T ⊆ B := fun i hi ↦ (Finset.mem_sdiff.mp (hTsub hi)).1
  have hEcard : E.card = T.card := by
    simpa only [E] using card_deletedOwnerSubfiber B T hTsubB
  have howner : ∀ b, b ∈ E → p.coeff b (b : Fin n) = -1 := by
    intro b hbE
    have hbT := (mem_deletedOwnerSubfiber_iff B T b).mp
      (by simpa only [E] using hbE)
    have hbOutside : (b : Fin n) ∉
        (Finset.univ : Finset (Fin d)).image leaf := by
      simpa only [← hL] using (Finset.mem_sdiff.mp (hTsub hbT)).2
    exact p.external_owner_eq_neg_one_of_mersenneLeaf
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hbOutside k
        (hrows b hbT).1 (hrows b hbT).2.1
  have hweight : ∀ b, b ∈ E → p.weight b = 2 * k := by
    intro b hbE
    exact (hrows b ((mem_deletedOwnerSubfiber_iff B T b).mp
      (by simpa only [E] using hbE))).2.1
  have hEcapacity : E.card ≤ addOrderOf y - 1 :=
    p.card_fixedWeight_negOne_le_order_sub_one
      g hg y B E k howner hweight
  have hweighted := completeExternalFiber_selectedIncidenceCharge
    g hg y root v B p hyq hfullOdd hprimitive hd hv leaf hleaf e
      hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hmiddle
        hprimaryWeight T (by simpa only [← hL] using hTsub) hr
          hparameter (fun b hbT ↦ ⟨(hrows b hbT).1, (hrows b hbT).2.1⟩)
  refine ⟨T, hTcard, hTsub, ?_, ?_⟩
  · omega
  · exact hweighted

end MinModulus
