/-
# Repairing the antipodal single-floor defect

Subtracting an owner-to-root signed pair from a zero relation with coefficient
`-2` at the root repairs the floor exactly when the selected owner has
coefficient `1`.  The result is a legal witness at the negative pair target,
with an omission at the root and coefficient zero at the selected owner.

For the explicit antipodal private-row dependence, every index in the
negative subset has precisely that owner coefficient.  Equal cardinality and
the pointed positive root guarantee that the negative subset is nonempty, so
at least one repaired witness always exists.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalPrivateDependence

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A pointed positive subset with an equal-cardinality partner forces the
partner to be nonempty. -/
theorem negative_subset_nonempty_of_pointed_equalCard
    {d : ℕ} {A M : Finset (Fin d)} {z : Fin d}
    (hcard : A.card = M.card) (hzA : z ∈ A) :
    M.Nonempty := by
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨z, hzA⟩
  apply Finset.card_pos.mp
  omega

/-- Subtracting the owner-to-root pair repairs a single root-floor defect.
The repaired relation is a witness at the negative pair target. -/
theorem SingleFloorDefectZeroRelation.sub_signedPair_isWitness
    {n : ℕ} (g : Fin n → G) (r : Fin n) (qrel : Fin n → ℤ)
    (hrel : SingleFloorDefectZeroRelation g r qrel)
    (owner : Fin n) (hownerRoot : owner ≠ r)
    (hqOwner : qrel owner = 1) :
    let repaired := qrel - signedPairCoeffs owner r
    Witness g (g r - g owner) repaired ∧
      repaired r = -1 ∧ repaired owner = 0 := by
  dsimp only
  let repaired : Fin n → ℤ := qrel - signedPairCoeffs owner r
  have hrowRoot : signedPairCoeffs owner r r = -1 := by
    simp [signedPairCoeffs, Ne.symm hownerRoot]
  have hrowOwner : signedPairCoeffs owner r owner = 1 := by
    simp [signedPairCoeffs, hownerRoot]
  have hrepairedRoot : repaired r = -1 := by
    simp only [repaired, Pi.sub_apply, hrel.defect, hrowRoot]
    omega
  have hrepairedOwner : repaired owner = 0 := by
    simp only [repaired, Pi.sub_apply, hqOwner, hrowOwner]
    omega
  refine ⟨?_, hrepairedRoot, hrepairedOwner⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hrzero : repaired r = 0 := congrFun hzero r
    rw [hrepairedRoot] at hrzero
    omega
  · intro i
    change -1 ≤ repaired i
    by_cases hir : i = r
    · subst i
      rw [hrepairedRoot]
    by_cases hio : i = owner
    · subst i
      rw [hrepairedOwner]
      omega
    have hrowZero : signedPairCoeffs owner r i = 0 := by
      simp [signedPairCoeffs, hio, hir]
    have hfloor := hrel.floor_away i hir
    simpa only [repaired, Pi.sub_apply, hrowZero, sub_zero] using hfloor
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib,
      hrel.coeff_sum, signedPairCoeffs]
    simp
  · calc
      (∑ i, repaired i • g i) =
          (∑ i, qrel i • g i) -
            ∑ i, signedPairCoeffs owner r i • g i := by
              simp only [repaired, Pi.sub_apply, sub_smul,
                Finset.sum_sub_distrib]
      _ = 0 - (g owner - g r) := by
        rw [hrel.weighted_sum,
          signedPairCoeffs_weighted_sum]
      _ = g r - g owner := by abel

/-- A member of the negative subset has coefficient `-1` in the normalized
private-row aggregate. -/
theorem normalizedPrivateSubsetAggregate_apply_mem_negative
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) :
    normalizedPrivateSubsetAggregate g y B p f z A M (f m) = -1 := by
  classical
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have hmA : m ∉ A := by
    intro hmA
    exact (Finset.disjoint_left.mp hdisjoint) hmA hmM
  have hfmA : f m ∉ A.image f := by
    intro hfmA
    obtain ⟨i, hiA, hifm⟩ := Finset.mem_image.mp hfmA
    have him : i = m := hf hifm
    exact hmA (him ▸ hiA)
  have hfmM : f m ∈ M.image f :=
    Finset.mem_image.mpr ⟨m, hmM, rfl⟩
  have hvalue := congrFun (hprivate.trans hindicators) (f m)
  simpa only [hfmA, hfmM, ↓reduceIte, zero_sub] using hvalue

/-- Every row in the negative subset repairs the explicit private-row defect
when subtracted from it. -/
theorem normalizedPrivateRow_defectRepair
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (external qrel : Fin n → ℤ)
    (hexternal : ∀ m, m ∈ M → external (f m) = 0)
    (hqrel : qrel = external -
      normalizedPrivateSubsetAggregate g y B p f z A M)
    (hrel : SingleFloorDefectZeroRelation g r qrel)
    (m : Fin d) (hmM : m ∈ M) :
    let row := normalizedCanonicalPrivateRow g y B p (f m)
    let repaired := qrel - row
    Witness g (g r - g (f m)) repaired ∧
      repaired r = -1 ∧ repaired (f m) = 0 := by
  classical
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hfmRoot : f m ≠ r := by
    rw [← hr]
    exact fun h ↦ hmz (hf h)
  have haggregateOwner :=
    normalizedPrivateSubsetAggregate_apply_mem_negative
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  have hqOwner : qrel (f m) = 1 := by
    rw [hqrel]
    simp only [Pi.sub_apply, hexternal m hmM, haggregateOwner]
    norm_num
  have hrepair :=
    hrel.sub_signedPair_isWitness g r qrel (f m) hfmRoot hqOwner
  have hrow := hrows m hmz
  simpa only [hrow] using hrepair

/-- The explicit private-row dependence always yields a repaired witness:
the negative subset is nonempty, and any one of its rows can be selected. -/
theorem exists_normalizedPrivateRow_defectRepair
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (external qrel : Fin n → ℤ)
    (hexternal : ∀ m, m ∈ M → external (f m) = 0)
    (hqrel : qrel = external -
      normalizedPrivateSubsetAggregate g y B p f z A M)
    (hrel : SingleFloorDefectZeroRelation g r qrel) :
    ∃ m : Fin d, ∃ _hmM : m ∈ M,
      let row := normalizedCanonicalPrivateRow g y B p (f m)
      let repaired := qrel - row
      Witness g (g r - g (f m)) repaired ∧
        repaired r = -1 ∧ repaired (f m) = 0 := by
  classical
  obtain ⟨m, hmM⟩ :=
    negative_subset_nonempty_of_pointed_equalCard hcard hzA
  refine ⟨m, hmM, ?_⟩
  exact normalizedPrivateRow_defectRepair
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows
      external qrel hexternal hqrel hrel m hmM

end MinModulus
