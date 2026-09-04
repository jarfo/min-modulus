/-
# Signed leaf incidence of antipodal repair residuals

Away from the pointed root and selected owner, the repair residual is exactly
the negative indicator of `A` plus the positive indicator of `M`.  Thus the
extra leaf hit forced by cyclic-kernel routing has a canonical sign and subset
side: it is either an `A`-hit of coefficient `-1` or an `M`-hit of coefficient
`1`.  This turns the residual family into directed finite-set incidence data
ready for counting over the external fiber.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairKernelRouting

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A positive-subset leaf has residual coefficient `-1`. -/
theorem normalizedPrivateRepairResidual_apply_positiveLeaf
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (i : Fin d) (hiA : i ∈ A)
    (hiz : i ≠ z) :
    normalizedPrivateRepairResidual g y B p f z A M m (f i) = -1 := by
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have him : i ≠ m := by
    intro him
    subst i
    exact (Finset.disjoint_left.mp hdisjoint) hiA hmM
  have hfiRoot : f i ≠ r := by
    rw [← hr]
    exact fun h ↦ hiz (hf h)
  have hfiOwner : f i ≠ f m := fun h ↦ him (hf h)
  have haggregate := normalizedPrivateSubsetAggregate_apply_mem_positive
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiA
  have hrowZero :
      normalizedCanonicalPrivateRow g y B p (f m) (f i) = 0 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hfiOwner, hfiRoot]
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    haggregate, hrowZero]
  norm_num

/-- A non-selected negative-subset leaf has residual coefficient `1`. -/
theorem normalizedPrivateRepairResidual_apply_otherNegativeLeaf
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (i : Fin d)
    (hiM : i ∈ M) (him : i ≠ m) :
    normalizedPrivateRepairResidual g y B p f z A M m (f i) = 1 := by
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hiz : i ≠ z := by
    intro hiz
    subst i
    exact (Finset.disjoint_left.mp hdisjoint) hzA hiM
  have hfiRoot : f i ≠ r := by
    rw [← hr]
    exact fun h ↦ hiz (hf h)
  have hfiOwner : f i ≠ f m := fun h ↦ him (hf h)
  have haggregate := normalizedPrivateSubsetAggregate_apply_mem_negative
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiM
  have hrowZero :
      normalizedCanonicalPrivateRow g y B p (f m) (f i) = 0 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hfiOwner, hfiRoot]
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    haggregate, hrowZero]
  norm_num

/-- A leaf outside both binary subsets has residual coefficient zero. -/
theorem normalizedPrivateRepairResidual_apply_leafOutsideSubsets
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (i : Fin d)
    (hiA : i ∉ A) (hiM : i ∉ M) :
    normalizedPrivateRepairResidual g y B p f z A M m (f i) = 0 := by
  classical
  have hmz : m ≠ z := by
    intro hmz
    subst m
    exact (Finset.disjoint_left.mp hdisjoint) hzA hmM
  have hiz : i ≠ z := fun hiz ↦ hiA (hiz ▸ hzA)
  have him : i ≠ m := fun him ↦ hiM (him ▸ hmM)
  have hfiRoot : f i ≠ r := by
    rw [← hr]
    exact fun h ↦ hiz (hf h)
  have hfiOwner : f i ≠ f m := fun h ↦ him (hf h)
  have hrowZero :
      normalizedCanonicalPrivateRow g y B p (f m) (f i) = 0 := by
    rw [hrows m hmz]
    simp [signedPairCoeffs, hfiOwner, hfiRoot]
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z hr A M hdisjoint hcard hzA
  have hfiA : f i ∉ A.image f := by
    intro hfiA
    obtain ⟨j, hjA, hjfi⟩ := Finset.mem_image.mp hfiA
    have hji : j = i := hf hjfi
    exact hiA (hji ▸ hjA)
  have hfiM : f i ∉ M.image f := by
    intro hfiM
    obtain ⟨j, hjM, hjfi⟩ := Finset.mem_image.mp hfiM
    have hji : j = i := hf hjfi
    exact hiM (hji ▸ hjM)
  have haggregate := congrFun (hprivate.trans hindicators) (f i)
  simp only [hfiA, hfiM, ↓reduceIte, sub_zero] at haggregate
  simp only [normalizedPrivateRepairResidual, Pi.sub_apply, Pi.neg_apply,
    haggregate, hrowZero]
  norm_num

/-- Away from the repaired root and owner, residual support is exactly
membership in `A ∪ M`. -/
theorem normalizedPrivateRepairResidual_apply_leaf_ne_zero_iff
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (i : Fin d)
    (hiz : i ≠ z) (him : i ≠ m) :
    normalizedPrivateRepairResidual g y B p f z A M m (f i) ≠ 0 ↔
      i ∈ A ∨ i ∈ M := by
  constructor
  · intro hne
    by_cases hiA : i ∈ A
    · exact Or.inl hiA
    · by_cases hiM : i ∈ M
      · exact Or.inr hiM
      · exact False.elim (hne
          (normalizedPrivateRepairResidual_apply_leafOutsideSubsets
            g y B p f hf z r hr A M hdisjoint hcard hzA hrows
              m hmM i hiA hiM))
  · rintro (hiA | hiM)
    · rw [normalizedPrivateRepairResidual_apply_positiveLeaf
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiA hiz]
      norm_num
    · rw [normalizedPrivateRepairResidual_apply_otherNegativeLeaf
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiM him]
      norm_num

/-- The transversal hit of a normalized repair residual is a signed directed
incidence: negative on `A` or positive on `M`, away from root and owner. -/
theorem CyclicKernelSupportTransversal.exists_signed_other_pointedLeaf_of_normalizedPrivateRepairResidual
    {n d : ℕ} (g : Fin n → G) (y v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (htrans : CyclicKernelSupportTransversal g y B)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (m : Fin d) (hmM : m ∈ M) (k : ℕ)
    (hc : Witness g (-(k • v))
      (normalizedPrivateRepairResidual g y B p f z A M m))
    (hne : -(k • v) ≠ 0) :
    ∃ i : Fin d, i ≠ z ∧ i ≠ m ∧ f i ∈ B ∧
      ((i ∈ A ∧
          normalizedPrivateRepairResidual g y B p f z A M m (f i) = -1) ∨
        (i ∈ M ∧
          normalizedPrivateRepairResidual g y B p f z A M m (f i) = 1)) := by
  let c := normalizedPrivateRepairResidual g y B p f z A M m
  have hroot := normalizedPrivateRepairResidual_apply_root
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  have howner := normalizedPrivateRepairResidual_apply_selectedOwner
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  have hoff := normalizedPrivateRepairResidual_zero_off
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
  obtain ⟨i, hiz, him, hiB, hine⟩ :=
    htrans.exists_other_pointedLeaf_of_mersenneResidualWitness
      g y v B hcyclic f z r hr m k c hc hne hroot howner hoff
  refine ⟨i, hiz, him, hiB, ?_⟩
  rcases (normalizedPrivateRepairResidual_apply_leaf_ne_zero_iff
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows
      m hmM i hiz him).mp hine with hiA | hiM
  · exact Or.inl ⟨hiA,
      normalizedPrivateRepairResidual_apply_positiveLeaf
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiA hiz⟩
  · exact Or.inr ⟨hiM,
      normalizedPrivateRepairResidual_apply_otherNegativeLeaf
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiM him⟩

end MinModulus
