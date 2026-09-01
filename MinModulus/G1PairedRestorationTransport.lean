/-
# Transporting the two excluded restoration-fan faces

The exact paired complement consists of one excluded face for each selected
target.  On such a face the subset meets the target support in exactly the
restoration support `H`.  In the singleton-positive root profile, the target
positive tail lies in `H`; writing `E = B_q ∩ H`, the target collision sends

  `H ∪ P` to `B_q ∪ P`

and changes the subset sum by the fixed translate `h + ssum(E)`.

The transported face contains the complete root support.  For the two
distinct canonical targets, pairwise crossing makes the transported faces
disjoint inside that full-root upper face.  Thus the exact deficit is not
free new mass: collision transport folds it back into two disjoint regions
of the already-counted full-root face, with two explicit affine shifts.
-/
import MinModulus.G1PairedRestorationComplement

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Replace the target-positive part of an excluded fan subset by the
target-negative part, retaining all padding outside the target support. -/
def restorationFanExcludedTransport
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (S : Finset (Fin m)) :
    Finset (Fin m) :=
  q.val.2 ∪ (S \ reducedCollisionSupport q)

/-- The intrinsic target face reached by excluded-face collision transport. -/
noncomputable def restorationFanExcludedTransportSubsetSlice
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m) :
    Finset (Finset (Fin m)) :=
  blockedSignatureUpperSubsetLayer (q.val.2 ∪ {j}) ∩
    blockedSignatureSubsetLayer q.val.1

/-- Subset-sum values of the transported target face. -/
noncomputable def restorationFanExcludedTransportValueSlice
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m) : Finset G :=
  (restorationFanExcludedTransportSubsetSlice q j).image (ssum g)

omit [DecidableEq G] in
/-- An excluded fan subset meets the target support in exactly the selected
restoration support. -/
theorem restorationFanForcedExcludedSubsetSlice_inter_targetSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) {S : Finset (Fin m)}
    (hS : S ∈ restorationFanForcedExcludedSubsetSlice r q j) :
    S ∩ reducedCollisionSupport q =
      reducedCollisionRestorationFanSupport r q := by
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  have hparts := Finset.mem_inter.mp hS
  have hblocked := (Finset.mem_inter.mp hparts.1).2
  have hupper := hparts.2
  apply Finset.Subset.antisymm
  · intro x hx
    have hxS := (Finset.mem_inter.mp hx).1
    have hxq := (Finset.mem_inter.mp hx).2
    by_contra hxH
    have hxCommon : x ∈ reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q :=
      Finset.mem_sdiff.mpr ⟨hxq, hxH⟩
    have hxAllowed := Finset.mem_powerset.mp hblocked hxS
    exact (Finset.mem_sdiff.mp hxAllowed).2 hxCommon
  · intro x hxH
    exact Finset.mem_inter.mpr
      ⟨(mem_blockedSignatureUpperSubsetLayer_iff.mp hupper) hxH,
        hHq hxH⟩

omit [DecidableEq G] in
/-- Split an excluded subset into the fixed restoration support and padding
outside the target support. -/
theorem restorationFanForcedExcludedSubsetSlice_eq_support_union_padding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) {S : Finset (Fin m)}
    (hS : S ∈ restorationFanForcedExcludedSubsetSlice r q j) :
    S = reducedCollisionRestorationFanSupport r q ∪
      (S \ reducedCollisionSupport q) := by
  have hinter :=
    restorationFanForcedExcludedSubsetSlice_inter_targetSupport
      r q hcard hdrop j hS
  ext x
  constructor
  · intro hxS
    by_cases hxq : x ∈ reducedCollisionSupport q
    · exact Finset.mem_union_left _
        (hinter ▸ Finset.mem_inter.mpr ⟨hxS, hxq⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxS, hxq⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hxH | hxP
    · have hxInter : x ∈ S ∩ reducedCollisionSupport q :=
        hinter.symm ▸ hxH
      exact (Finset.mem_inter.mp hxInter).1
    · exact (Finset.mem_sdiff.mp hxP).1

omit [DecidableEq G] in
/-- If the target trace outside `H` is negative, then every positive target
coordinate belongs to `H`. -/
theorem targetPositive_subset_restorationFanSupport_of_commonBlock_negative
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (htrace : reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q ⊆ q.val.2) :
    q.val.1 ⊆ reducedCollisionRestorationFanSupport r q := by
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  intro x hxA
  by_contra hxH
  have hxq : x ∈ reducedCollisionSupport q :=
    Finset.mem_union_left _ hxA
  have hxB := htrace (Finset.mem_sdiff.mpr ⟨hxq, hxH⟩)
  exact Finset.disjoint_left.mp q.property.1 hxA hxB

omit [DecidableEq G] in
/-- Once the target positive tail lies in `H`, the whole restoration support
is its disjoint union with the external negative part. -/
theorem restorationFanSupport_eq_targetPositive_union_negativeInter
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (hAin : q.val.1 ⊆ reducedCollisionRestorationFanSupport r q) :
    reducedCollisionRestorationFanSupport r q =
      q.val.1 ∪
        (q.val.2 ∩ reducedCollisionRestorationFanSupport r q) := by
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  ext x
  constructor
  · intro hxH
    rcases Finset.mem_union.mp (hHq hxH) with hxA | hxB
    · exact Finset.mem_union_left _ hxA
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxB, hxH⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hxA | hxE
    · exact hAin hxA
    · exact (Finset.mem_inter.mp hxE).2

omit [DecidableEq G] in
/-- Collision transport changes every excluded-face subset sum by one fixed
translate, namely the half target plus the sum of the target-negative part
inside the restoration support. -/
theorem ssum_restorationFanExcludedTransport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (hAin : q.val.1 ⊆ reducedCollisionRestorationFanSupport r q)
    (j : Fin m) {S : Finset (Fin m)}
    (hS : S ∈ restorationFanForcedExcludedSubsetSlice r q j) :
    ssum g S = ssum g (restorationFanExcludedTransport q S) + h +
      ssum g (q.val.2 ∩
        reducedCollisionRestorationFanSupport r q) := by
  let H := reducedCollisionRestorationFanSupport r q
  let P := S \ reducedCollisionSupport q
  let E := q.val.2 ∩ H
  have hSdecomp : S = H ∪ P := by
    simpa only [H, P] using
      restorationFanForcedExcludedSubsetSlice_eq_support_union_padding
        r q hcard hdrop j hS
  have hHdecomp : H = q.val.1 ∪ E := by
    simpa only [H, E] using
      restorationFanSupport_eq_targetPositive_union_negativeInter
        r q hcard hdrop hAin
  have hHP : Disjoint H P := by
    rw [Finset.disjoint_left]
    intro x hxH hxP
    have hxq := (restorationFanSupport_subset_external r q hcard hdrop hxH)
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.sdiff_subset hxq)
  have hAE : Disjoint q.val.1 E := by
    exact q.property.1.mono_right Finset.inter_subset_left
  have hBP : Disjoint q.val.2 P := by
    rw [Finset.disjoint_left]
    intro x hxB hxP
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_union_right _ hxB)
  calc
    ssum g S = ssum g (H ∪ P) := by rw [hSdecomp]
    _ = ssum g H + ssum g P := ssum_union_of_disjoint g hHP
    _ = ssum g (q.val.1 ∪ E) + ssum g P := by rw [hHdecomp]
    _ = (ssum g q.val.1 + ssum g E) + ssum g P := by
      rw [ssum_union_of_disjoint g hAE]
    _ = (ssum g q.val.2 + h + ssum g E) + ssum g P := by
      rw [q.property.2]
    _ = ssum g (q.val.2 ∪ P) + h + ssum g E := by
      rw [ssum_union_of_disjoint g hBP]
      abel
    _ = ssum g (restorationFanExcludedTransport q S) + h +
        ssum g (q.val.2 ∩
          reducedCollisionRestorationFanSupport r q) := by
      rfl

omit [DecidableEq G] in
/-- In the singleton-positive/two-negative root profile, every retained root
coordinate lies in the selected target's negative tail. -/
theorem rootSupport_erase_subset_targetNegative_of_singletonPositive
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    (reducedCollisionSupport r).erase j ⊆ q.val.2 := by
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAcard
  have haq : a ∈ q.val.2 := by
    rcases hAq with ⟨x, hx⟩
    have hxa : x = a := by simpa [hA] using (Finset.mem_inter.mp hx).1
    exact hxa ▸ (Finset.mem_inter.mp hx).2
  intro x hx
  have hx' := Finset.mem_erase.mp hx
  rcases Finset.mem_union.mp hx'.2 with hxA | hxB
  · have hxa : x = a := by simpa [hA] using hxA
    exact hxa ▸ haq
  · rw [hB] at hxB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
    rcases hxB with rfl | rfl
    · exact False.elim (hx'.1 rfl)
    · exact hkq

omit [DecidableEq G] in
/-- The singleton-positive hypotheses put the whole target positive tail in
the restoration support. -/
theorem targetPositive_subset_restorationFanSupport_of_singletonPositive
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
    q.val.1 ⊆ reducedCollisionRestorationFanSupport r q := by
  apply targetPositive_subset_restorationFanSupport_of_commonBlock_negative
    r q hcard hdrop
  rw [restorationFanCommonBlockedSupport_eq_rootSupport_erase
    r q hcard hdrop j k hAcard hB hjq hkq hAq]
  exact rootSupport_erase_subset_targetNegative_of_singletonPositive
    r q j k hAcard hB hkq hAq

omit [DecidableEq G] in
/-- The target negative tail, together with its dropped root coordinate,
contains the complete root support. -/
theorem rootSupport_subset_targetNegative_union_singleton
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    reducedCollisionSupport r ⊆ q.val.2 ∪ {j} := by
  have htrace :=
    rootSupport_erase_subset_targetNegative_of_singletonPositive
      r q j k hAcard hB hkq hAq
  intro x hxR
  by_cases hxj : x = j
  · exact Finset.mem_union_right _ (by simp [hxj])
  · exact Finset.mem_union_left _
      (htrace (Finset.mem_erase.mpr ⟨hxj, hxR⟩))

omit [DecidableEq G] in
/-- The pointwise affine transport formula specialized to the live
singleton-positive target profile. -/
theorem ssum_restorationFanExcludedTransport_of_singletonPositive
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty)
    {S : Finset (Fin m)}
    (hS : S ∈ restorationFanForcedExcludedSubsetSlice r q j) :
    ssum g S = ssum g (restorationFanExcludedTransport q S) + h +
      ssum g (q.val.2 ∩
        reducedCollisionRestorationFanSupport r q) := by
  exact ssum_restorationFanExcludedTransport r q hcard hdrop
    (targetPositive_subset_restorationFanSupport_of_singletonPositive
      r q hcard hdrop j k hAcard hB hjq hkq hAq) j hS

omit [DecidableEq G] in
/-- Excluded-face transport is onto the intrinsic target upper/lower face. -/
theorem image_restorationFanForcedExcludedSubsetSlice_transport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) (hjq : j ∉ reducedCollisionSupport q) :
    (restorationFanForcedExcludedSubsetSlice r q j).image
        (restorationFanExcludedTransport q) =
      restorationFanExcludedTransportSubsetSlice q j := by
  classical
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  apply Finset.Subset.antisymm
  · intro T hT
    rcases Finset.mem_image.mp hT with ⟨S, hS, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · rw [mem_blockedSignatureUpperSubsetLayer_iff]
      intro x hx
      rcases Finset.mem_union.mp hx with hxB | hxj
      · exact Finset.mem_union_left _ hxB
      · have hxj' : x = j := by simpa using hxj
        subst x
        have hjS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
          (Finset.mem_inter.mp (Finset.mem_inter.mp hS).1).1)
            (Finset.mem_singleton_self j)
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjS, hjq⟩)
    · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
      intro x hx
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hxA
      rcases Finset.mem_union.mp hx with hxB | hxP
      · exact Finset.disjoint_left.mp q.property.1 hxA hxB
      · exact (Finset.mem_sdiff.mp hxP).2
          (Finset.mem_union_left _ hxA)
  · intro T hT
    have hUpper := (Finset.mem_inter.mp hT).1
    have hLower := (Finset.mem_inter.mp hT).2
    let S := reducedCollisionRestorationFanSupport r q ∪
      (T \ reducedCollisionSupport q)
    have hS : S ∈ restorationFanForcedExcludedSubsetSlice r q j := by
      apply Finset.mem_inter.mpr
      constructor
      · apply Finset.mem_inter.mpr
        constructor
        · rw [mem_blockedSignatureUpperSubsetLayer_iff]
          intro x hx
          have hxj : x = j := by simpa using hx
          subst x
          apply Finset.mem_union_right
          apply Finset.mem_sdiff.mpr
          refine ⟨(mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper) ?_, hjq⟩
          exact Finset.mem_union_right _ (Finset.mem_singleton_self j)
        · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
          intro x hxS
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hxCommon
          rcases Finset.mem_union.mp hxS with hxH | hxP
          · exact (Finset.mem_sdiff.mp hxCommon).2 hxH
          · exact (Finset.mem_sdiff.mp hxP).2
              (Finset.mem_sdiff.mp hxCommon).1
      · rw [mem_blockedSignatureUpperSubsetLayer_iff]
        exact Finset.subset_union_left
    apply Finset.mem_image.mpr
    refine ⟨S, hS, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxB | hxP
      · exact (mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper)
          (Finset.mem_union_left _ hxB)
      · have hxS := (Finset.mem_sdiff.mp hxP).1
        have hxS' : x ∈ reducedCollisionRestorationFanSupport r q ∪
            (T \ reducedCollisionSupport q) := by
          simpa only [S] using hxS
        rcases Finset.mem_union.mp hxS' with hxH | hxTP
        · exact False.elim ((Finset.mem_sdiff.mp hxP).2 (hHq hxH))
        · exact (Finset.mem_sdiff.mp hxTP).1
    · intro hxT
      by_cases hxq : x ∈ reducedCollisionSupport q
      · rcases Finset.mem_union.mp hxq with hxA | hxB
        · have hxAllowed := Finset.mem_powerset.mp hLower hxT
          exact False.elim ((Finset.mem_sdiff.mp hxAllowed).2 hxA)
        · exact Finset.mem_union_left _ hxB
      · apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxT, hxq⟩), hxq⟩

omit [DecidableEq G] in
/-- Every transported target face lies in the complete root upper face. -/
theorem restorationFanExcludedTransportSubsetSlice_subset_rootUpper
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    restorationFanExcludedTransportSubsetSlice q j ⊆
      blockedSignatureUpperSubsetLayer (reducedCollisionSupport r) := by
  have hroot := rootSupport_subset_targetNegative_union_singleton
    r q j k hAcard hB hkq hAq
  intro S hS
  rw [mem_blockedSignatureUpperSubsetLayer_iff]
  exact hroot.trans
    (mem_blockedSignatureUpperSubsetLayer_iff.mp
      (Finset.mem_inter.mp hS).1)

omit [DecidableEq G] in
/-- A positive/negative crossing in either orientation separates the two
transported target faces. -/
theorem restorationFanExcludedTransportSubsetSlices_disjoint_of_cross
    {g : Fin (m + 1) → G} {h : G}
    (v u : ReducedSubsetSumCollision g h) (j k : Fin m)
    (hcross : (v.val.1 ∩ u.val.2).Nonempty ∨
      (u.val.1 ∩ v.val.2).Nonempty) :
    Disjoint (restorationFanExcludedTransportSubsetSlice v j)
      (restorationFanExcludedTransportSubsetSlice u k) := by
  classical
  rw [Finset.disjoint_left]
  intro S hSv hSu
  rcases hcross with hvu | huv
  · obtain ⟨x, hx⟩ := hvu
    have hxS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
      (Finset.mem_inter.mp hSu).1)
        (Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
    have hxAllowed := Finset.mem_powerset.mp
      (Finset.mem_inter.mp hSv).2 hxS
    exact (Finset.mem_sdiff.mp hxAllowed).2 (Finset.mem_inter.mp hx).1
  · obtain ⟨x, hx⟩ := huv
    have hxS := (mem_blockedSignatureUpperSubsetLayer_iff.mp
      (Finset.mem_inter.mp hSv).1)
        (Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
    have hxAllowed := Finset.mem_powerset.mp
      (Finset.mem_inter.mp hSu).2 hxS
    exact (Finset.mem_sdiff.mp hxAllowed).2 (Finset.mem_inter.mp hx).1

/-- Distinct canonical selected targets have disjoint transported faces. -/
theorem canonical_restorationFanExcludedTransportSubsetSlices_disjoint
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvu : v ≠ u) (j k : Fin m) :
    Disjoint (restorationFanExcludedTransportSubsetSlice v j)
      (restorationFanExcludedTransportSubsetSlice u k) := by
  exact restorationFanExcludedTransportSubsetSlices_disjoint_of_cross
    v u j k
      (distinct_canonicalReducedCollisions_positive_negative_cross
        g hg hh hh0 v u hv hu (Ne.symm hvu))

omit [DecidableEq G] in
/-- The transported face has the same exact half-target weight as the
excluded face from which it came. -/
theorem two_mul_card_restorationFanExcludedTransportSubsetSlice
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjq : j ∉ reducedCollisionSupport q) :
    2 * (restorationFanExcludedTransportSubsetSlice q j).card =
      reducedCollisionWeight (m := m) q := by
  classical
  have hdisj : Disjoint (q.val.2 ∪ {j}) q.val.1 := by
    rw [Finset.disjoint_union_left]
    constructor
    · exact q.property.1.symm
    · rw [Finset.disjoint_left]
      intro x hxj hxA
      have hx : x = j := by simpa using hxj
      subst x
      exact hjq (Finset.mem_union_left _ hxA)
  have hunion : (q.val.2 ∪ {j}) ∪ q.val.1 =
      reducedCollisionSupport q ∪ {j} := by
    ext x
    simp only [reducedCollisionSupport, Finset.mem_union,
      Finset.mem_singleton]
    tauto
  have hcardInsert : (reducedCollisionSupport q ∪ {j}).card =
      (reducedCollisionSupport q).card + 1 := by
    simpa [Finset.union_comm] using
      (Finset.card_insert_of_notMem hjq)
  have hle : (reducedCollisionSupport q).card + 1 ≤ m := by
    rw [← hcardInsert]
    simpa using Finset.card_le_univ (reducedCollisionSupport q ∪ {j})
  rw [restorationFanExcludedTransportSubsetSlice,
    card_upperSubsetLayer_inter_blockedSubsetLayer _ _ hdisj,
    hunion, hcardInsert]
  change 2 * 2 ^ (m - ((reducedCollisionSupport q).card + 1)) =
    2 ^ (m - (reducedCollisionSupport q).card)
  have hexp : m - (reducedCollisionSupport q).card =
      (m - ((reducedCollisionSupport q).card + 1)) + 1 := by omega
  rw [hexp, pow_succ]
  omega

/-- The paired transported faces. -/
noncomputable def pairedRestorationFanExcludedTransportSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    Finset (Finset (Fin m)) :=
  restorationFanExcludedTransportSubsetSlice v j ∪
    restorationFanExcludedTransportSubsetSlice u k

omit [DecidableEq G] in
/-- The two canonical transports pack disjointly into the complete root
upper face. -/
theorem pairedRestorationFanExcludedTransportSubsetUnion_subset_rootUpper
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    pairedRestorationFanExcludedTransportSubsetUnion v u j k ⊆
      blockedSignatureUpperSubsetLayer (reducedCollisionSupport r) := by
  classical
  intro S hS
  rcases Finset.mem_union.mp hS with hSv | hSu
  · exact restorationFanExcludedTransportSubsetSlice_subset_rootUpper
      r v j k hAcard hB hkv hAv hSv
  · have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
    exact restorationFanExcludedTransportSubsetSlice_subset_rootUpper
      r u k j hAcard hBswap hju hAu hSu

/-- Exact total size of the disjoint paired transport. -/
theorem two_mul_card_pairedRestorationFanExcludedTransportSubsetUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvu : v ≠ u) (j k : Fin m)
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u) :
    2 * (pairedRestorationFanExcludedTransportSubsetUnion v u j k).card =
      reducedCollisionWeight (m := m) v +
        reducedCollisionWeight (m := m) u := by
  have hdisj :=
    canonical_restorationFanExcludedTransportSubsetSlices_disjoint
      hg hh hh0 v u hv hu hvu j k
  rw [pairedRestorationFanExcludedTransportSubsetUnion,
    Finset.card_union_of_disjoint hdisj,
    Nat.mul_add,
    two_mul_card_restorationFanExcludedTransportSubsetSlice v j hjv,
    two_mul_card_restorationFanExcludedTransportSubsetSlice u k hku]

/-- Translate an excluded value face back through its target collision. -/
noncomputable def restorationFanForcedExcludedTranslatedValueSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) : Finset G :=
  (restorationFanForcedExcludedValueSlice r q j).image
    (fun x ↦ x - h - ssum g
      (q.val.2 ∩ reducedCollisionRestorationFanSupport r q))

/-- The excluded value face, shifted by its explicit collision vector, is
exactly the intrinsic transported target face. -/
theorem restorationFanForcedExcludedTranslatedValueSlice_eq_transport
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
    restorationFanForcedExcludedTranslatedValueSlice r q j =
      restorationFanExcludedTransportValueSlice q j := by
  classical
  apply Finset.Subset.antisymm
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
    have hsum :=
      ssum_restorationFanExcludedTransport_of_singletonPositive
        r q hcard hdrop j k hAcard hB hjq hkq hAq hS
    have hT : restorationFanExcludedTransport q S ∈
        restorationFanExcludedTransportSubsetSlice q j := by
      have himage : restorationFanExcludedTransport q S ∈
          (restorationFanForcedExcludedSubsetSlice r q j).image
            (restorationFanExcludedTransport q) :=
        Finset.mem_image.mpr ⟨S, hS, rfl⟩
      rw [image_restorationFanForcedExcludedSubsetSlice_transport
        r q hcard hdrop j hjq] at himage
      exact himage
    rw [restorationFanExcludedTransportValueSlice]
    apply Finset.mem_image.mpr
    refine ⟨restorationFanExcludedTransport q S, hT, ?_⟩
    rw [hsum]
    abel
  · intro y hy
    rw [restorationFanExcludedTransportValueSlice] at hy
    rcases Finset.mem_image.mp hy with ⟨T, hT, rfl⟩
    have hpre : T ∈
        (restorationFanForcedExcludedSubsetSlice r q j).image
          (restorationFanExcludedTransport q) := by
      rw [image_restorationFanForcedExcludedSubsetSlice_transport
        r q hcard hdrop j hjq]
      exact hT
    rcases Finset.mem_image.mp hpre with ⟨S, hS, hST⟩
    rw [restorationFanForcedExcludedTranslatedValueSlice]
    apply Finset.mem_image.mpr
    refine ⟨ssum g S, ?_, ?_⟩
    · rw [restorationFanForcedExcludedValueSlice]
      exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
    · have hsum :=
        ssum_restorationFanExcludedTransport_of_singletonPositive
          r q hcard hdrop j k hAcard hB hjq hkq hAq hS
      rw [← hST]
      rw [hsum]
      abel

/-- Values of the two transported target faces. -/
noncomputable def pairedRestorationFanExcludedTransportValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  restorationFanExcludedTransportValueSlice v j ∪
    restorationFanExcludedTransportValueSlice u k

/-- Validity preserves the crossing-forced disjointness of the two
transported faces at value level. -/
theorem canonical_restorationFanExcludedTransportValueSlices_disjoint
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvu : v ≠ u) (j k : Fin m) :
    Disjoint (restorationFanExcludedTransportValueSlice v j)
      (restorationFanExcludedTransportValueSlice u k) := by
  classical
  have hsubset :=
    canonical_restorationFanExcludedTransportSubsetSlices_disjoint
      hg hh hh0 v u hv hu hvu j k
  rw [Finset.disjoint_left]
  intro x hxv hxu
  rcases Finset.mem_image.mp hxv with ⟨S, hSv, hSx⟩
  rcases Finset.mem_image.mp hxu with ⟨T, hTu, hTx⟩
  have hST : S = T := ssum_injective g hg (hSx.trans hTx.symm)
  subst T
  exact Finset.disjoint_left.mp hsubset hSv hTu

/-- The paired transported value union has exactly the combined half-target
weight. -/
theorem two_mul_card_pairedRestorationFanExcludedTransportValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvu : v ≠ u) (j k : Fin m)
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u) :
    2 * (pairedRestorationFanExcludedTransportValueUnion v u j k).card =
      reducedCollisionWeight (m := m) v +
        reducedCollisionWeight (m := m) u := by
  have hdisj :=
    canonical_restorationFanExcludedTransportValueSlices_disjoint
      hg hh hh0 v u hv hu hvu j k
  rw [pairedRestorationFanExcludedTransportValueUnion,
    Finset.card_union_of_disjoint hdisj,
    restorationFanExcludedTransportValueSlice,
    restorationFanExcludedTransportValueSlice,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  have hvcard :=
    two_mul_card_restorationFanExcludedTransportSubsetSlice v j hjv
  have hucard :=
    two_mul_card_restorationFanExcludedTransportSubsetSlice u k hku
  omega

/-- The paired transported values remain inside the already-counted complete
root upper value face. -/
theorem pairedRestorationFanExcludedTransportValueUnion_subset_rootUpper
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    pairedRestorationFanExcludedTransportValueUnion v u j k ⊆
      blockedSignatureUpperValueLayer g (reducedCollisionSupport r) := by
  classical
  have hsub :=
    pairedRestorationFanExcludedTransportSubsetUnion_subset_rootUpper
      r v u j k hAcard hB hkv hju hAv hAu
  intro x hx
  rw [pairedRestorationFanExcludedTransportValueUnion] at hx
  rw [blockedSignatureUpperValueLayer]
  rcases Finset.mem_union.mp hx with hxv | hxu
  · rcases Finset.mem_image.mp hxv with ⟨S, hS, hSx⟩
    exact Finset.mem_image.mpr
      ⟨S, hsub (Finset.mem_union_left _ hS), hSx⟩
  · rcases Finset.mem_image.mp hxu with ⟨S, hS, hSx⟩
    exact Finset.mem_image.mpr
      ⟨S, hsub (Finset.mem_union_right _ hS), hSx⟩

/-- The affine folding into the full-root face gives a global weight
constraint on the two selected targets. -/
theorem selectedTargetWeights_le_two_rootWeight_of_pairedTransport
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r v u : ReducedSubsetSumCollision g h)
    (hv : IsCanonicalReducedCollision hh v)
    (hu : IsCanonicalReducedCollision hh u)
    (hvu : v ≠ u) (j k : Fin m)
    (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    reducedCollisionWeight (m := m) v +
        reducedCollisionWeight (m := m) u ≤
      2 * reducedCollisionWeight (m := m) r := by
  have hsubset :=
    pairedRestorationFanExcludedTransportValueUnion_subset_rootUpper
      r v u j k hAcard hB hkv hju hAv hAu
  have hcardle := Finset.card_le_card hsubset
  have hpair :=
    two_mul_card_pairedRestorationFanExcludedTransportValueUnion
      hg hh hh0 v u hv hu hvu j k hjv hku
  have hroot :
      (blockedSignatureUpperValueLayer g
        (reducedCollisionSupport r)).card =
          reducedCollisionWeight (m := m) r := by
    rw [card_blockedSignatureUpperValueLayer hg]
    rfl
  rw [hroot] at hcardle
  omega

/-- Apply the two target-specific affine shifts to the exact paired
complement. -/
noncomputable def pairedRestorationFanForcedExcludedTranslatedValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  restorationFanForcedExcludedTranslatedValueSlice r v j ∪
    restorationFanForcedExcludedTranslatedValueSlice r u k

/-- Componentwise collision transport folds the two translated complement
faces exactly onto the paired transported value union. -/
theorem pairedRestorationFanForcedExcludedTranslatedValueUnion_eq_transport
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hkv : k ∈ v.val.2) (hju : j ∈ u.val.2)
    (hAv : (r.val.1 ∩ v.val.2).Nonempty)
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    pairedRestorationFanForcedExcludedTranslatedValueUnion r v u j k =
      pairedRestorationFanExcludedTransportValueUnion v u j k := by
  have hv :=
    restorationFanForcedExcludedTranslatedValueSlice_eq_transport
      r v hcardv hdropv j k hAcard hB hjv hkv hAv
  have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
  have hu :=
    restorationFanForcedExcludedTranslatedValueSlice_eq_transport
      r u hcardu hdropu k j hAcard hBswap hku hju hAu
  rw [pairedRestorationFanForcedExcludedTranslatedValueUnion,
    pairedRestorationFanExcludedTransportValueUnion, hv, hu]

end MinModulus
