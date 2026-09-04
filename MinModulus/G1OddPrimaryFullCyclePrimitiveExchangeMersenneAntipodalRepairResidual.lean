/-
# The leaf-only residual of an antipodal defect repair

Subtract the external pure row from one of the repaired witnesses.  The
off-leaf part cancels, as do the pointed root and the selected negative owner.
What remains is the signed indicator of `M.erase m` minus that of
`A.erase z`.  It is therefore either zero, in the exact singleton case, or a
new legal leaf-supported witness.  This is the first lossless post-repair
alternative needed by the privacy/minimality step.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalPureEdgeRepair

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A positive subset member has coefficient `1` in the normalized
private-row aggregate. -/
theorem normalizedPrivateSubsetAggregate_apply_mem_positive
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (i : Fin d) (hiA : i ∈ A) :
    normalizedPrivateSubsetAggregate g y B p f z A M (f i) = 1 := by
  classical
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have hfiA : f i ∈ A.image f :=
    Finset.mem_image.mpr ⟨i, hiA, rfl⟩
  have hfiM : f i ∉ M.image f := by
    intro hfiM
    obtain ⟨j, hjM, hjfi⟩ := Finset.mem_image.mp hfiM
    have hji : j = i := hf hjfi
    exact (Finset.disjoint_left.mp hdisjoint) hiA (hji ▸ hjM)
  have hvalue := congrFun (hprivate.trans hindicators) (f i)
  simpa only [hfiA, hfiM, ↓reduceIte, sub_zero] using hvalue

/-- The pointed root has coefficient `1` in the normalized private-row
aggregate. -/
theorem normalizedPrivateSubsetAggregate_apply_root
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r) :
    normalizedPrivateSubsetAggregate g y B p f z A M r = 1 := by
  classical
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have hrA : r ∈ A.image f :=
    Finset.mem_image.mpr ⟨z, hzA, hr⟩
  have hrM : r ∉ M.image f := by
    intro hrM
    obtain ⟨i, hiM, hif⟩ := Finset.mem_image.mp hrM
    have hiz : i = z := hf (hif.trans hr.symm)
    exact (Finset.disjoint_left.mp hdisjoint) hzA (hiz ▸ hiM)
  have hvalue := congrFun (hprivate.trans hindicators) r
  simpa only [hrA, hrM, ↓reduceIte, sub_zero] using hvalue

/-- The leaf-only coefficient vector left after cancelling the external row
from the repair at `m`. -/
noncomputable def normalizedPrivateRepairResidual
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d)
    (A M : Finset (Fin d)) (m : Fin d) : Fin n → ℤ :=
  -normalizedPrivateSubsetAggregate g y B p f z A M -
    normalizedCanonicalPrivateRow g y B p (f m)

/-- Cancelling the external row from a repaired defect relation gives exactly
the normalized private repair residual. -/
theorem repaired_sub_external_eq_normalizedPrivateRepairResidual
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d)
    (A M : Finset (Fin d)) (m : Fin d)
    (external qrel : Fin n → ℤ)
    (hqrel : qrel = external -
      normalizedPrivateSubsetAggregate g y B p f z A M) :
    (qrel - normalizedCanonicalPrivateRow g y B p (f m)) - external =
      normalizedPrivateRepairResidual g y B p f z A M m := by
  rw [hqrel]
  funext i
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply]
  ring

/-- The repair residual vanishes at its pointed root. -/
theorem normalizedPrivateRepairResidual_apply_root
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
    normalizedPrivateRepairResidual g y B p f z A M m r = 0 := by
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hfmRoot : f m ≠ r := by
    rw [← hr]
    exact fun h ↦ hmz (hf h)
  have haggregate := normalizedPrivateSubsetAggregate_apply_root
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows
  have hrow : normalizedCanonicalPrivateRow g y B p (f m) r = -1 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, Ne.symm hfmRoot]
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    haggregate, hrow]
  norm_num

/-- The repair residual also vanishes at the selected negative owner. -/
theorem normalizedPrivateRepairResidual_apply_selectedOwner
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
    normalizedPrivateRepairResidual g y B p f z A M m (f m) = 0 := by
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hfmRoot : f m ≠ r := by
    rw [← hr]
    exact fun h ↦ hmz (hf h)
  have haggregate := normalizedPrivateSubsetAggregate_apply_mem_negative
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  have hrow : normalizedCanonicalPrivateRow g y B p (f m) (f m) = 1 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hfmRoot]
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    haggregate, hrow]
  norm_num

/-- Every coefficient of the leaf-only repair residual respects the witness
floor. -/
theorem normalizedPrivateRepairResidual_floor
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (j : Fin n) :
    -1 ≤ normalizedPrivateRepairResidual g y B p f z A M m j := by
  classical
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  by_cases hjr : j = r
  · subst j
    rw [normalizedPrivateRepairResidual_apply_root
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM]
    omega
  by_cases hjm : j = f m
  · subst j
    rw [normalizedPrivateRepairResidual_apply_selectedOwner
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM]
    omega
  have hrowZero : normalizedCanonicalPrivateRow g y B p (f m) j = 0 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hjm, hjr]
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have haggregate := congrFun (hprivate.trans hindicators) j
  by_cases hjA : j ∈ A.image f <;>
    by_cases hjM : j ∈ M.image f <;>
      simp only [hjA, hjM, ↓reduceIte] at haggregate <;>
      simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
        hrowZero, haggregate] <;> omega

/-- The repair residual is supported entirely on the pointed leaf. -/
theorem normalizedPrivateRepairResidual_zero_off
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (j : Fin n)
    (hj : j ∉ (Finset.univ : Finset (Fin d)).image f) :
    normalizedPrivateRepairResidual g y B p f z A M m j = 0 := by
  classical
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hjOwner : j ≠ f m := by
    intro hjOwner
    apply hj
    exact Finset.mem_image.mpr
      ⟨m, Finset.mem_univ m, hjOwner.symm⟩
  have hjRoot : j ≠ r := by
    intro hjRoot
    apply hj
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_univ z, hr.trans hjRoot.symm⟩
  have hrowZero : normalizedCanonicalPrivateRow g y B p (f m) j = 0 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hjOwner, hjRoot]
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have hjA : j ∉ A.image f := by
    intro hjA
    obtain ⟨i, _hiA, hif⟩ := Finset.mem_image.mp hjA
    exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hif⟩)
  have hjM : j ∉ M.image f := by
    intro hjM
    obtain ⟨i, _hiM, hif⟩ := Finset.mem_image.mp hjM
    exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hif⟩)
  have haggregate := congrFun (hprivate.trans hindicators) j
  simp only [hjA, hjM, ↓reduceIte, sub_zero] at haggregate
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    hrowZero, haggregate]
  norm_num

/-- The residual is zero exactly when the original positive and negative sets
are the pointed and selected singletons. -/
theorem normalizedPrivateRepairResidual_eq_zero_iff
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
    normalizedPrivateRepairResidual g y B p f z A M m = 0 ↔
      A = {z} ∧ M = {m} := by
  classical
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  constructor
  · intro hzero
    have hAsub : A ⊆ {z} := by
      intro i hiA
      have hiz : i = z := by
        by_contra hiz
        have him : i ≠ m := by
          intro him
          subst i
          exact (Finset.disjoint_left.mp hdisjoint) hiA hmM
        have haggregate := normalizedPrivateSubsetAggregate_apply_mem_positive
          g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiA
        have hfiRoot : f i ≠ r := by
          rw [← hr]
          exact fun h ↦ hiz (hf h)
        have hfiOwner : f i ≠ f m := fun h ↦ him (hf h)
        have hrowZero :
            normalizedCanonicalPrivateRow g y B p (f m) (f i) = 0 := by
          rw [hrows m hmz]
          simp [signedPairCoeffs, hfiOwner, hfiRoot]
        have hvalue := congrFun hzero (f i)
        simp only [normalizedPrivateRepairResidual, Pi.sub_apply,
          Pi.neg_apply, Pi.zero_apply, haggregate, hrowZero] at hvalue
        omega
      simp [hiz]
    have hMsub : M ⊆ {m} := by
      intro i hiM
      have him : i = m := by
        by_contra him
        have hiz : i ≠ z := by
          intro hiz
          subst i
          exact (Finset.disjoint_left.mp hdisjoint) hzA hiM
        have haggregate := normalizedPrivateSubsetAggregate_apply_mem_negative
          g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiM
        have hfiRoot : f i ≠ r := by
          rw [← hr]
          exact fun h ↦ hiz (hf h)
        have hfiOwner : f i ≠ f m := fun h ↦ him (hf h)
        have hrowZero :
            normalizedCanonicalPrivateRow g y B p (f m) (f i) = 0 := by
          rw [hrows m hmz]
          simp [signedPairCoeffs, hfiOwner, hfiRoot]
        have hvalue := congrFun hzero (f i)
        simp only [normalizedPrivateRepairResidual, Pi.sub_apply,
          Pi.neg_apply, Pi.zero_apply, haggregate, hrowZero] at hvalue
        omega
      simp [him]
    exact ⟨Finset.Subset.antisymm hAsub
        (Finset.singleton_subset_iff.mpr hzA),
      Finset.Subset.antisymm hMsub
        (Finset.singleton_subset_iff.mpr hmM)⟩
  · rintro ⟨rfl, rfl⟩
    funext j
    simp [normalizedPrivateRepairResidual, normalizedPrivateSubsetAggregate]

/-- If it is nonzero, the repair residual is a legal witness at the
difference between the repaired and external targets. -/
theorem normalizedPrivateRepairResidual_isWitness
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M)
    (external qrel : Fin n → ℤ) (externalTarget repairedTarget : G)
    (hexternal : Witness g externalTarget external)
    (hqrel : qrel = external -
      normalizedPrivateSubsetAggregate g y B p f z A M)
    (hrepair : Witness g repairedTarget
      (qrel - normalizedCanonicalPrivateRow g y B p (f m)))
    (hresidual : normalizedPrivateRepairResidual
      g y B p f z A M m ≠ 0) :
    Witness g (repairedTarget - externalTarget)
      (normalizedPrivateRepairResidual g y B p f z A M m) := by
  let repaired := qrel - normalizedCanonicalPrivateRow g y B p (f m)
  have hidentity : repaired - external =
      normalizedPrivateRepairResidual g y B p f z A M m :=
    repaired_sub_external_eq_normalizedPrivateRepairResidual
      g y B p f z A M m external qrel hqrel
  have hrepair' : Witness g repairedTarget repaired := by
    simpa only [repaired] using hrepair
  refine ⟨hresidual, ?_, ?_, ?_⟩
  · exact normalizedPrivateRepairResidual_floor
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  · rw [← hidentity]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hrepair'.2.2.1, hexternal.2.2.1, sub_zero]
  · calc
      (∑ i, normalizedPrivateRepairResidual g y B p f z A M m i • g i) =
          ∑ i, (repaired i • g i - external i • g i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← hidentity]
            simp only [Pi.sub_apply, sub_smul]
      _ = (∑ i, repaired i • g i) -
          ∑ i, external i • g i := by
            rw [Finset.sum_sub_distrib]
      _ = repairedTarget - externalTarget := by
        rw [hrepair'.2.2.2, hexternal.2.2.2]

/-- Exact post-repair dichotomy: either the repaired witness is literally the
external row and both subset sides are singletons, or their leaf-only
difference is another legal witness. -/
theorem normalizedPrivateRow_exactCancellation_or_residualWitness
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M)
    (external qrel : Fin n → ℤ) (externalTarget repairedTarget : G)
    (hexternal : Witness g externalTarget external)
    (hqrel : qrel = external -
      normalizedPrivateSubsetAggregate g y B p f z A M)
    (hrepair : Witness g repairedTarget
      (qrel - normalizedCanonicalPrivateRow g y B p (f m))) :
    ((qrel - normalizedCanonicalPrivateRow g y B p (f m)) = external ∧
        A = {z} ∧ M = {m}) ∨
      Witness g (repairedTarget - externalTarget)
        (normalizedPrivateRepairResidual g y B p f z A M m) := by
  by_cases hzero : normalizedPrivateRepairResidual
      g y B p f z A M m = 0
  · left
    have hsets := (normalizedPrivateRepairResidual_eq_zero_iff
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM).1 hzero
    have hidentity := repaired_sub_external_eq_normalizedPrivateRepairResidual
      g y B p f z A M m external qrel hqrel
    refine ⟨?_, hsets⟩
    apply sub_eq_zero.mp
    exact hidentity.trans hzero
  · right
    exact normalizedPrivateRepairResidual_isWitness
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
        external qrel externalTarget repairedTarget hexternal hqrel hrepair hzero

end MinModulus
