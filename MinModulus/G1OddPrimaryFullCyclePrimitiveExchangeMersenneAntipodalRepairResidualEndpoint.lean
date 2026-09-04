/-
# Installing the antipodal repair residual in the Mersenne endpoint

The abstract repair residual has an especially rigid target in the pointed
Mersenne normal form.  The repaired target is the negative `m`-th SI digit,
so cancelling an external row of positive scalar `s` leaves exactly
`-(a m + s) * v`.  Original validity makes every nonzero residual target
genuinely nonzero.  This module packages that scalar identity together with
the exact cancellation/leaf-residual split for use in the full lossless
antipodal endpoint.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairResidual

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A witness for a valid tuple cannot have target zero. -/
theorem witness_target_ne_zero_of_validTuple
    {n : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    {target : G} {c : Fin n → ℤ} (hc : Witness g target c) :
    target ≠ 0 := by
  intro htarget
  apply (validTuple_iff_no_zero_witness g).mp hg c
  simpa only [htarget] using hc

/-- In a pointed Mersenne leaf, cancelling an external target `s • v` from
the repair at `m` leaves the negative scalar `a(m)+s`. -/
theorem mersenneLeaf_repair_sub_external_target
    {n d : ℕ} (g : Fin n → G) (root v : G)
    (hd : 0 < d)
    (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (r : Fin n)
    (hrzero : leaf (e ⟨0, hd⟩) = r)
    (s : ℕ) (m : Fin d) :
    (g r - g (leaf (e m))) - s • v = -((a m.val + s) • v) := by
  have hroot : g r = root := by
    rw [← hrzero, hnormal]
    simp [a]
  rw [hroot, hnormal]
  simp only [add_nsmul]
  abel

/-- At the pointed Mersenne endpoint, each repaired row either cancels the
external row exactly (forcing both binary subsets to be singletons) or leaves
a nonzero leaf-supported witness at the explicit scalar `-(a(m)+s) • v`.
-/
theorem normalizedPrivateRow_exactCancellation_or_mersenneResidualWitness
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 0 < d)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (r : Fin n) (hrzero : leaf (e ⟨0, hd⟩) = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : ⟨0, hd⟩ ∈ A)
    (hrows : ∀ i, i ≠ ⟨0, hd⟩ →
      normalizedCanonicalPrivateRow g y B p (leaf (e i)) =
        signedPairCoeffs (leaf (e i)) r)
    (s : ℕ) (b : ↥B)
    (htarget : p.scalar b • y = s • v)
    (qrel : Fin n → ℤ)
    (hqrel : qrel = p.coeff b -
      normalizedPrivateSubsetAggregate
        g y B p (fun i ↦ leaf (e i)) ⟨0, hd⟩ A M)
    (m : Fin d) (hmM : m ∈ M)
    (hrepair : Witness g (g r - g (leaf (e m)))
      (qrel - normalizedCanonicalPrivateRow g y B p (leaf (e m)))) :
    let residual := normalizedPrivateRepairResidual
      g y B p (fun i ↦ leaf (e i)) ⟨0, hd⟩ A M m
    ((qrel - normalizedCanonicalPrivateRow g y B p (leaf (e m)) =
          p.coeff b ∧
        A = {⟨0, hd⟩} ∧ M = {m}) ∨
      (Witness g (-((a m.val + s) • v)) residual ∧
        (g r - g (leaf (e m))) - p.scalar b • y =
          -((a m.val + s) • v) ∧
        -((a m.val + s) • v) ≠ 0 ∧
        residual r = 0 ∧ residual (leaf (e m)) = 0 ∧
        ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image
            (fun i ↦ leaf (e i)) → residual j = 0)) := by
  classical
  dsimp only
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  have hf : Function.Injective f := hleaf.comp e.injective
  have hscalar :
      (g r - g (leaf (e m))) - p.scalar b • y =
        -((a m.val + s) • v) := by
    rw [htarget]
    exact mersenneLeaf_repair_sub_external_target
      g root v hd leaf e hnormal r hrzero s m
  have houtcome := normalizedPrivateRow_exactCancellation_or_residualWitness
    g y B p f hf ⟨0, hd⟩ r hrzero A M hdisjoint hcard hzA hrows
      m hmM (p.coeff b) qrel (p.scalar b • y)
        (g r - g (leaf (e m))) (p.isWitness b) hqrel hrepair
  rcases houtcome with hcancel | hresidual
  · exact Or.inl hcancel
  · right
    have hresidual' : Witness g (-((a m.val + s) • v))
        (normalizedPrivateRepairResidual g y B p f
          ⟨0, hd⟩ A M m) := by
      rw [← hscalar]
      exact hresidual
    exact ⟨hresidual', hscalar,
      witness_target_ne_zero_of_validTuple g hg hresidual',
      normalizedPrivateRepairResidual_apply_root
        g y B p f hf ⟨0, hd⟩ r hrzero A M hdisjoint hcard hzA
          hrows m hmM,
      normalizedPrivateRepairResidual_apply_selectedOwner
        g y B p f hf ⟨0, hd⟩ r hrzero A M hdisjoint hcard hzA
          hrows m hmM,
      normalizedPrivateRepairResidual_zero_off
        g y B p f hf ⟨0, hd⟩ r hrzero A M hdisjoint hcard hzA
          hrows m hmM⟩

/-- Lossless antipodal endpoint with the post-repair Mersenne residual
installed.  The common-omission branch is unchanged.  In the exact-negative
branch, every `m ∈ M` retains its repair and is classified further as literal
singleton cancellation or as a nonzero leaf-supported witness at the explicit
target `-(a(m)+s) • v`. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_repairResidual_dichotomy
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
                let residual := normalizedPrivateRepairResidual
                  g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M m
                Witness g (g r - g (leaf (e m))) repaired ∧
                  repaired r = -1 ∧ repaired (leaf (e m)) = 0 ∧
                  ((repaired = p.coeff b ∧
                      A = {⟨0, by omega⟩} ∧ M = {m}) ∨
                    (Witness g (-((a m.val + s) • v)) residual ∧
                      (g r - g (leaf (e m))) - p.scalar b • y =
                        -((a m.val + s) • v) ∧
                      -((a m.val + s) • v) ≠ 0 ∧
                      residual r = 0 ∧
                      residual (leaf (e m)) = 0 ∧
                      ∀ j,
                        j ∉ (Finset.univ : Finset (Fin d)).image
                            (fun i ↦ leaf (e i)) →
                          residual j = 0))) := by
  dsimp only
  obtain ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
      cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus,
      hminusOff, hminusR, hiLeaf, hiLocalized, hiGap, hqrel,
      hdefect, hqcenter, hqb, houtcome⟩ :=
    p.exists_antipodal_mersenneLeaf_pureEdgeRepair_dichotomy
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
            let residual := normalizedPrivateRepairResidual
              g y B p (fun j ↦ leaf (e j)) ⟨0, by omega⟩ A M m
            Witness g (g r - g (leaf (e m))) repaired ∧
              repaired r = -1 ∧ repaired (leaf (e m)) = 0 ∧
              ((repaired = p.coeff b ∧
                  A = {⟨0, by omega⟩} ∧ M = {m}) ∨
                (Witness g (-((a m.val + s) • v)) residual ∧
                  (g r - g (leaf (e m))) - p.scalar b • y =
                    -((a m.val + s) • v) ∧
                  -((a m.val + s) • v) ≠ 0 ∧
                  residual r = 0 ∧
                  residual (leaf (e m)) = 0 ∧
                  ∀ j,
                    j ∉ (Finset.univ : Finset (Fin d)).image
                        (fun i ↦ leaf (e i)) →
                      residual j = 0)) := by
    rcases houtcome with hcommon |
        ⟨A, M, hneg, hdisjoint, hcard, hzero, hcPrivate,
          hqPrivate, harithmetic, hrepairs⟩
    · exact Or.inl hcommon
    · right
      refine ⟨A, M, hneg, hdisjoint, hcard, hzero, hcPrivate,
        hqPrivate, harithmetic, ?_⟩
      intro m hmM
      dsimp only
      obtain ⟨hrepair, hrepairRoot, hrepairOwner⟩ := hrepairs m hmM
      refine ⟨hrepair, hrepairRoot, hrepairOwner, ?_⟩
      exact normalizedPrivateRow_exactCancellation_or_mersenneResidualWitness
        g hg y root v B p (by omega) leaf hleaf e hnormal r hrzero
          A M hdisjoint hcard hzero hrows s b htarget qrel hqPrivate
            m hmM hrepair
  exact ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
    cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus, hminusOff,
    hminusR, hiLeaf, hiLocalized, hiGap, hqrel, hdefect,
    hqcenter, hqb, hnewOutcome⟩

end MinModulus
