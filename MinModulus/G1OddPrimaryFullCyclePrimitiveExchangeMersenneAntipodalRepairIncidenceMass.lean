/-
# Exact incidence mass of the antipodal repair family

The signed pointwise laws assemble into a complete finite incidence matrix.
For the repair selected at `m`, leaf support is exactly

  (A.erase z) ∪ (M.erase m).

Thus every non-root `A` column has negative incidence from all `|M|` rows,
and every `M` column has positive incidence from all rows except its diagonal.
The family contains exactly `2 |M| (|M|-1)` nonzero leaf incidences.  This is
the quantitative input for charging the antipodal external fiber.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairIncidence

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Pointed leaf indices on which a normalized repair residual is nonzero. -/
noncomputable def normalizedPrivateRepairResidualLeafSupport
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d)
    (A M : Finset (Fin d)) (m : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (fun i ↦
    normalizedPrivateRepairResidual g y B p f z A M m (f i) ≠ 0)

/-- The residual support is exactly the off-root positive subset together
with the off-diagonal negative subset. -/
theorem normalizedPrivateRepairResidualLeafSupport_eq
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
    normalizedPrivateRepairResidualLeafSupport g y B p f z A M m =
      (A.erase z) ∪ (M.erase m) := by
  classical
  ext i
  simp only [normalizedPrivateRepairResidualLeafSupport, mem_filter,
    mem_univ, true_and, mem_union, mem_erase]
  constructor
  · intro hne
    have hiz : i ≠ z := by
      intro hiz
      subst i
      apply hne
      rw [hr]
      exact normalizedPrivateRepairResidual_apply_root
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
    have him : i ≠ m := by
      intro him
      subst i
      exact hne (normalizedPrivateRepairResidual_apply_selectedOwner
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM)
    rcases (normalizedPrivateRepairResidual_apply_leaf_ne_zero_iff
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows
        m hmM i hiz him).mp hne with hiA | hiM
    · exact Or.inl ⟨hiz, hiA⟩
    · exact Or.inr ⟨him, hiM⟩
  · rintro (⟨hiz, hiA⟩ | ⟨him, hiM⟩)
    · exact (normalizedPrivateRepairResidual_apply_leaf_ne_zero_iff
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiz (fun him ↦
            (Finset.disjoint_left.mp hdisjoint) hiA (him ▸ hmM))).2
        (Or.inl hiA)
    · have hiz : i ≠ z := by
        intro hiz
        subst i
        exact (Finset.disjoint_left.mp hdisjoint) hzA hiM
      exact (normalizedPrivateRepairResidual_apply_leaf_ne_zero_iff
        g y B p f hf z r hr A M hdisjoint hcard hzA hrows
          m hmM i hiz him).2 (Or.inr hiM)

/-- Every repair residual has `2(|M|-1)` nonzero pointed-leaf entries. -/
theorem card_normalizedPrivateRepairResidualLeafSupport
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
    (normalizedPrivateRepairResidualLeafSupport
      g y B p f z A M m).card = 2 * (M.card - 1) := by
  rw [normalizedPrivateRepairResidualLeafSupport_eq
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM]
  have hdisjointErase : Disjoint (A.erase z) (M.erase m) :=
    hdisjoint.mono (Finset.erase_subset z A) (Finset.erase_subset m M)
  rw [Finset.card_union_of_disjoint hdisjointErase,
    Finset.card_erase_of_mem hzA, Finset.card_erase_of_mem hmM, hcard]
  omega

/-- A non-root `A` column receives coefficient `-1` from every repair row. -/
theorem normalizedPrivateRepairResidual_negativeIncidence_complete
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (i : Fin d) (hiA : i ∈ A) (hiz : i ≠ z) :
    (M.filter (fun m ↦
      normalizedPrivateRepairResidual g y B p f z A M m (f i) = -1)).card =
        M.card := by
  classical
  apply congrArg Finset.card
  ext m
  simp only [mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hmM
    exact ⟨hmM, normalizedPrivateRepairResidual_apply_positiveLeaf
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows
        m hmM i hiA hiz⟩

/-- An `M` column receives coefficient `1` from precisely the off-diagonal
repair rows. -/
theorem normalizedPrivateRepairResidual_positiveIncidence_eq_erase
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (i : Fin d) (hiM : i ∈ M) :
    M.filter (fun m ↦
      normalizedPrivateRepairResidual g y B p f z A M m (f i) = 1) =
        M.erase i := by
  classical
  ext m
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hmM, hcoeff⟩
    refine ⟨?_, hmM⟩
    intro hmi
    subst m
    have hzero := normalizedPrivateRepairResidual_apply_selectedOwner
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiM
    omega
  · rintro ⟨hmi, hmM⟩
    refine ⟨hmM, ?_⟩
    exact normalizedPrivateRepairResidual_apply_otherNegativeLeaf
      g y B p f hf z r hr A M hdisjoint hcard hzA hrows
        m hmM i hiM (Ne.symm hmi)

/-- Each `M` column has exactly `|M|-1` positive repair incidences. -/
theorem card_normalizedPrivateRepairResidual_positiveIncidence
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (i : Fin d) (hiM : i ∈ M) :
    (M.filter (fun m ↦
      normalizedPrivateRepairResidual g y B p f z A M m (f i) = 1)).card =
        M.card - 1 := by
  rw [normalizedPrivateRepairResidual_positiveIncidence_eq_erase
    g y B p f hf z r hr A M hdisjoint hcard hzA hrows i hiM,
    Finset.card_erase_of_mem hiM]

/-- Exact total number of nonzero pointed-leaf incidences in the repair
family. -/
theorem sum_card_normalizedPrivateRepairResidualLeafSupport
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (hf : Function.Injective f)
    (z : Fin d) (r : Fin n) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r) :
    (∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
      g y B p f z A M m).card) = M.card * (2 * (M.card - 1)) := by
  calc
    (∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m).card) =
        ∑ _m ∈ M, 2 * (M.card - 1) := by
          apply Finset.sum_congr rfl
          intro m hmM
          exact card_normalizedPrivateRepairResidualLeafSupport
            g y B p f hf z r hr A M hdisjoint hcard hzA hrows m hmM
    _ = M.card * (2 * (M.card - 1)) := by simp

end MinModulus
