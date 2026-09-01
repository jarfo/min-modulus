/-
# Positive upper faces absorb the paired restoration complement

The exact complement of the singleton-positive paired restoration packing is
the union of two excluded target faces.  Each excluded face forces the whole
restoration support, while the singleton-positive root geometry puts the
target positive tail inside that support.  Hence the excluded face lies in
the target's positive upper face.

Consequently, for every collision family containing the two selected targets,
the part of its positive-upper union outside the paired packing is exactly the
whole complement of that packing.  This converts the external-contamination
problem into the precise internal question of controlling the intersection
with the paired packing.
-/
import MinModulus.G1PositiveUpperParityIncidence
import MinModulus.G1PairedRestorationTransport

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- In the live singleton-positive target profile, the excluded restoration
face is contained in the target's positive upper face. -/
theorem restorationFanForcedExcludedValueSlice_subset_positiveUpperValueLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    restorationFanForcedExcludedValueSlice r q j ⊆
      reducedCollisionPositiveUpperValueLayer q := by
  classical
  have hAin :=
    targetPositive_subset_restorationFanSupport_of_singletonPositive
      r q hcard hdrop j k hAcard hB hjq hkq hAq
  intro x hx
  rw [restorationFanForcedExcludedValueSlice] at hx
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  rw [reducedCollisionPositiveUpperValueLayer,
    blockedSignatureUpperValueLayer]
  apply Finset.mem_image.mpr
  refine ⟨S, ?_, rfl⟩
  have hupper := (Finset.mem_inter.mp hS).2
  exact mem_blockedSignatureUpperSubsetLayer_iff.mpr fun a ha ↦
    (mem_blockedSignatureUpperSubsetLayer_iff.mp hupper) (hAin ha)

/-- If a family contains both selected targets, its positive-upper union
contains the entire complement of the paired restoration packing. -/
theorem pairedRestoration_complement_subset_positiveUpperValueUnionAll
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty)
    (hvF : v ∈ F) (huF : u ∈ F) :
    subsetSumRange g \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k ⊆
      reducedCollisionPositiveUpperValueUnionAll F := by
  classical
  rw [subsetSumRange_sdiff_pairedRestorationFanValueUnionWithTailUpperFaces
    hg r v u hcardv hcardu hdropv hdropu j k hjk hAcard hB
      hjv hku hkv hju hAv hAu]
  intro x hx
  rcases Finset.mem_union.mp hx with hxv | hxu
  · exact Finset.mem_biUnion.mpr ⟨v, hvF,
      restorationFanForcedExcludedValueSlice_subset_positiveUpperValueLayer
        r v hcardv hdropv j k hAcard hB hjv hkv hAv hxv⟩
  · have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
    exact Finset.mem_biUnion.mpr ⟨u, huF,
      restorationFanForcedExcludedValueSlice_subset_positiveUpperValueLayer
        r u hcardu hdropu k j hAcard hBswap hku hju hAu hxu⟩

/-- The positive-upper union's part outside the paired packing is not merely
bounded by the packing complement: it is exactly that complement. -/
theorem positiveUpperValueUnionAll_sdiff_pairedRestoration_eq_complement
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty)
    (hvF : v ∈ F) (huF : u ∈ F) :
    reducedCollisionPositiveUpperValueUnionAll F \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k =
      subsetSumRange g \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr
      ⟨reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F hx'.1,
        hx'.2⟩
  · intro x hx
    have hcomp := pairedRestoration_complement_subset_positiveUpperValueUnionAll
      hg r v u F hcardv hcardu hdropv hdropu j k hjk hAcard hB
        hjv hku hkv hju hAv hAu hvF huF hx
    exact Finset.mem_sdiff.mpr ⟨hcomp, (Finset.mem_sdiff.mp hx).2⟩

/-- Cardinal form of the exact external-contamination reduction. -/
theorem card_positiveUpperValueUnionAll_sdiff_pairedRestoration
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty)
    (hvF : v ∈ F) (huF : u ∈ F) :
    (reducedCollisionPositiveUpperValueUnionAll F \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card =
      (subsetSumRange g \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card := by
  rw [positiveUpperValueUnionAll_sdiff_pairedRestoration_eq_complement
    hg r v u F hcardv hcardu hdropv hdropu j k hjk hAcard hB
      hjv hku hkv hju hAv hAu hvF huF]

section CriticalPairedComplement

/-- Milestone 2dg: in the live singleton-positive/two-negative critical
profile, the two canonical selected targets belong to the complete non-root
family and make its positive-upper union cover the exact paired complement.
Thus its external part has doubled cardinality precisely `w_v+w_u`. -/
theorem genuineDominant_two_tail_exists_positiveUpper_pairedComplement
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    ∃ j k : Fin n,
    ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ F ∧ u ∈ F ∧ j ≠ k ∧
      reducedCollisionPositiveUpperValueUnionAll F \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k =
        subsetSumRange g \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k ∧
      2 * (reducedCollisionPositiveUpperValueUnionAll F \
          pairedRestorationFanValueUnionWithTailUpperFaces r v u j k).card =
        reducedCollisionWeight (m := n) v +
          reducedCollisionWeight (m := n) u := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let F := criticalCanonicalNonrootCollisions g r
  obtain ⟨j, k, v, u, hjk, hB, hvcritical, hucritical, _hvu,
      hjv, hku, hkv, hju, hAv, hAu, _h8v, _h8u, _hpackCard,
      _hpackSub, _hambient, hsingleton⟩ :=
    genuineDominant_two_tail_exists_pairedRestorationFan_twoFace_packing
      hqodd g hg r hr hres hBcard
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hkB : k ∈ r.val.2 := by rw [hB]; simp
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hkR : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hkB
  have hvr : v ≠ r := by
    intro hvr
    subst v
    exact hjv hjR
  have hur : u ≠ r := by
    intro hur
    subst u
    exact hku hkR
  have hvall := genuineDominant_two_tail_all_other_eighthWeight_growth
    hqodd g hg r hr hres hBcard v hvcritical hvr
  have huall := genuineDominant_two_tail_all_other_eighthWeight_growth
    hqodd g hg r hr hres hBcard u hucritical hur
  have hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by omega
  have hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card := by omega
  have hdropv : (reducedCollisionDroppedSupport r v).Nonempty :=
    ⟨j, Finset.mem_sdiff.mpr ⟨hjR, hjv⟩⟩
  have hdropu : (reducedCollisionDroppedSupport r u).Nonempty :=
    ⟨k, Finset.mem_sdiff.mpr ⟨hkR, hku⟩⟩
  have hvF : v ∈ F := by
    exact Finset.mem_erase.mpr ⟨hvr, hvcritical⟩
  have huF : u ∈ F := by
    exact Finset.mem_erase.mpr ⟨hur, hucritical⟩
  have hEq :=
    positiveUpperValueUnionAll_sdiff_pairedRestoration_eq_complement
      hg r v u F hcardv hcardu hdropv hdropu j k hjk hAcard hB
        hjv hku hkv hju hAv hAu hvF huF
  have hcomplementCard := (hsingleton hAcard).2
  refine ⟨j, k, v, u, hvF, huF, hjk, hEq, ?_⟩
  rw [hEq]
  exact hcomplementCard

end CriticalPairedComplement

end MinModulus
