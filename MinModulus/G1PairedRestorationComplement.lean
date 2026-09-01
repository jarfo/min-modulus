/-
# Exact complement of the singleton-positive paired fan packing

In the singleton-positive/two-negative root profile, a selected target that
drops `j` and contains the other negative root coordinate `k` also contains
the unique positive root coordinate in its negative tail.  Its root trace is
therefore exactly `supp(r) \ {j}`.  Since the restoration fan removes all
external excess coordinates but one at a time, its common blocked set is
exactly that same erased root support.

The directional root cell forcing `j` and avoiding every other root
coordinate splits into the exact fan slice and one excluded face.  The latter
has doubled cardinality equal to the target's native padding weight.  For the
two coupled targets, these are precisely the two pieces missing from the
paired two-face near-tiling.
-/
import MinModulus.G1PairedRestorationPositiveFace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

section OneTargetComplement

omit [DecidableEq G] in
/-- In the singleton-positive/two-negative profile, the target contains every
root coordinate except the selected coordinate it drops. -/
theorem rootSupport_erase_subset_targetSupport_of_singletonPositive
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    (reducedCollisionSupport r).erase j ⊆
      reducedCollisionSupport q := by
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAcard
  have haq : a ∈ q.val.2 := by
    rcases hAq with ⟨x, hx⟩
    have hxA := (Finset.mem_inter.mp hx).1
    have hxq := (Finset.mem_inter.mp hx).2
    have hxa : x = a := by simpa [hA] using hxA
    subst x
    exact hxq
  intro x hx
  have hx' := Finset.mem_erase.mp hx
  rcases Finset.mem_union.mp hx'.2 with hxA | hxB
  · have hxa : x = a := by simpa [hA] using hxA
    subst x
    exact Finset.mem_union_right _ haq
  · rw [hB] at hxB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
    rcases hxB with rfl | rfl
    · exact False.elim (hx'.1 rfl)
    · exact Finset.mem_union_right _ hkq

omit [DecidableEq G] in
/-- The exact fan common block is the root support with the dropped coordinate
erased. -/
theorem restorationFanCommonBlockedSupport_eq_rootSupport_erase
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
    reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q =
      (reducedCollisionSupport r).erase j := by
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hsubRoot :=
    rootSupport_erase_subset_targetSupport_of_singletonPositive
      r q j k hAcard hB hjq hkq hAq
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have hsub : (reducedCollisionSupport r).erase j ⊆
      reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨hsubRoot hx, ?_⟩
    intro hxH
    have hxExt := hHext hxH
    exact (Finset.mem_sdiff.mp hxExt).2 (Finset.mem_of_mem_erase hx)
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [card_restorationFanCommonBlockedSupport r q hcard hdrop,
    Finset.card_erase_of_mem hjR]

/-- The one root-coordinate cell forcing `j` and avoiding every other root
coordinate. -/
noncomputable def directionalRootPatternSubsetCell
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) (j : Fin m) :
    Finset (Finset (Fin m)) :=
  blockedSignatureUpperSubsetLayer {j} ∩
    blockedSignatureSubsetLayer ((reducedCollisionSupport r).erase j)

/-- The face excluded from the forced half of an exact restoration fan. -/
noncomputable def restorationFanForcedExcludedSubsetSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) :
    Finset (Finset (Fin m)) :=
  (blockedSignatureUpperSubsetLayer {j} ∩
      blockedSignatureSubsetLayer
        (reducedCollisionSupport q \
          reducedCollisionRestorationFanSupport r q)) ∩
    blockedSignatureUpperSubsetLayer
      (reducedCollisionRestorationFanSupport r q)

/-- Values carried by the excluded forced face. -/
noncomputable def restorationFanForcedExcludedValueSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) : Finset G :=
  (restorationFanForcedExcludedSubsetSlice r q j).image (ssum g)

omit [DecidableEq G] in
/-- The directional root cell has exactly the root padding cardinality. -/
theorem card_directionalRootPatternSubsetCell
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjR : j ∈ reducedCollisionSupport r) :
    (directionalRootPatternSubsetCell r j).card =
      reducedCollisionWeight (m := m) r := by
  have hdisj : Disjoint ({j} : Finset (Fin m))
      ((reducedCollisionSupport r).erase j) := by simp
  have hunion : ({j} : Finset (Fin m)) ∪
      (reducedCollisionSupport r).erase j =
        reducedCollisionSupport r := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, hx⟩)
      · exact hjR
      · exact hx
    · intro hx
      by_cases hxj : x = j
      · exact Or.inl hxj
      · exact Or.inr ⟨hxj, hx⟩
  rw [directionalRootPatternSubsetCell,
    card_upperSubsetLayer_inter_blockedSubsetLayer _ _ hdisj,
    hunion]
  rfl

omit [DecidableEq G] in
/-- The directional root cell is the disjoint union of the forced fan slice
and its excluded upper face. -/
theorem directionalRootPatternSubsetCell_eq_forced_union_excluded
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
    directionalRootPatternSubsetCell r j =
      restorationFanForcedSubsetSlice r q j ∪
        restorationFanForcedExcludedSubsetSlice r q j := by
  classical
  have hcommon := restorationFanCommonBlockedSupport_eq_rootSupport_erase
    r q hcard hdrop j k hAcard hB hjq hkq hAq
  rw [directionalRootPatternSubsetCell,
    restorationFanForcedSubsetSlice,
    restorationFanForcedExcludedSubsetSlice,
    restorationFanSubsetUnion_eq_lower_sdiff_upper r q hcard hdrop,
    hcommon]
  ext S
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  tauto

omit [DecidableEq G] in
/-- The forced fan slice and its excluded face are disjoint. -/
theorem restorationFanForcedSubsetSlice_disjoint_excluded
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) :
    Disjoint (restorationFanForcedSubsetSlice r q j)
      (restorationFanForcedExcludedSubsetSlice r q j) := by
  classical
  rw [Finset.disjoint_left]
  intro S hS hE
  have hFan := (Finset.mem_inter.mp hS).2
  have hUpper := (Finset.mem_inter.mp hE).2
  rw [restorationFanSubsetUnion] at hFan
  rcases Finset.mem_biUnion.mp hFan with ⟨e, he, hLayer⟩
  have heH : e ∈ reducedCollisionRestorationFanSupport r q := he
  have heUpper :=
    (mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper) heH
  have heBlocked : e ∈ restorationFanBlockedSupport r q e := by
    rw [restorationFanBlockedSupport_eq_sdiff_union_singleton
      r q hcard hdrop heH]
    simp
  have hAllowed := Finset.mem_powerset.mp hLayer heUpper
  exact (Finset.mem_sdiff.mp hAllowed).2 heBlocked

omit [DecidableEq G] in
/-- The excluded directional face has exactly half the target's native
padding weight. -/
theorem two_mul_card_restorationFanForcedExcludedSubsetSlice
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
    2 * (restorationFanForcedExcludedSubsetSlice r q j).card =
      reducedCollisionWeight (m := m) q := by
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hcell := directionalRootPatternSubsetCell_eq_forced_union_excluded
    r q hcard hdrop j k hAcard hB hjq hkq hAq
  have hdisj := restorationFanForcedSubsetSlice_disjoint_excluded
    r q hcard hdrop j
  have hcardUnion :
      (directionalRootPatternSubsetCell r j).card =
        (restorationFanForcedSubsetSlice r q j).card +
          (restorationFanForcedExcludedSubsetSlice r q j).card := by
    rw [hcell, Finset.card_union_of_disjoint hdisj]
  have hcellCard := card_directionalRootPatternSubsetCell r j hjR
  have hforced := two_mul_card_restorationFanForcedSubsetSlice
    r q hcard hdrop j hjq
  have hqle : reducedCollisionWeight (m := m) q ≤
      reducedCollisionWeight (m := m) r :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hcard m)
  omega

/-- Validity transports the exact excluded-face count to subset-sum values. -/
theorem two_mul_card_restorationFanForcedExcludedValueSlice
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j k : Fin m) (hAcard : r.val.1.card = 1)
    (hB : r.val.2 = {j, k})
    (hjq : j ∉ reducedCollisionSupport q)
    (hkq : k ∈ q.val.2)
    (hAq : (r.val.1 ∩ q.val.2).Nonempty) :
    2 * (restorationFanForcedExcludedValueSlice r q j).card =
      reducedCollisionWeight (m := m) q := by
  rw [restorationFanForcedExcludedValueSlice,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    two_mul_card_restorationFanForcedExcludedSubsetSlice
      r q hcard hdrop j k hAcard hB hjq hkq hAq]

end OneTargetComplement

section PairedComplement

/-- Ordinary-subset version of the paired lower packing. -/
noncomputable def pairedRestorationFanSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    Finset (Finset (Fin m)) :=
  blockedSignatureSubsetLayer (reducedCollisionSupport r) ∪
    (restorationFanForcedSubsetSlice r v j ∪
      restorationFanForcedSubsetSlice r u k)

/-- Ordinary-subset version of the paired packing with both root upper
faces. -/
noncomputable def pairedRestorationFanSubsetUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    Finset (Finset (Fin m)) :=
  (pairedRestorationFanSubsetUnion r v u j k ∪
      blockedSignatureUpperSubsetLayer r.val.2) ∪
    blockedSignatureUpperSubsetLayer r.val.1

/-- The ordinary paired union maps exactly to the previously defined value
union. -/
theorem image_pairedRestorationFanSubsetUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    (pairedRestorationFanSubsetUnionWithTailUpperFaces
        r v u j k).image (ssum g) =
      pairedRestorationFanValueUnionWithTailUpperFaces r v u j k := by
  classical
  have hroot :
      (blockedSignatureSubsetLayer
          (reducedCollisionSupport r)).image (ssum g) =
        collisionPaddingValueLayer r := by
    change blockedSignatureValueLayer g (reducedCollisionSupport r) =
      collisionPaddingValueLayer r
    exact (collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support r).symm
  rw [pairedRestorationFanSubsetUnionWithTailUpperFaces,
    pairedRestorationFanSubsetUnion,
    pairedRestorationFanValueUnionWithTailUpperFaces,
    pairedRestorationFanValueUnion,
    Finset.image_union, Finset.image_union, Finset.image_union,
    Finset.image_union,
    restorationFanForcedValueSlice,
    restorationFanForcedValueSlice,
    blockedSignatureUpperValueLayer,
    blockedSignatureUpperValueLayer,
    hroot]

omit [DecidableEq G] in
/-- In the singleton-positive profile, the only ordinary subsets missing
from the paired two-face packing are the two forced excluded fan faces. -/
theorem univ_sdiff_pairedRestorationFanSubsetUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h)
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
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    (Finset.univ : Finset (Finset (Fin m))) \
        pairedRestorationFanSubsetUnionWithTailUpperFaces r v u j k =
      restorationFanForcedExcludedSubsetSlice r v j ∪
        restorationFanForcedExcludedSubsetSlice r u k := by
  classical
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAcard
  have hcellV :=
    directionalRootPatternSubsetCell_eq_forced_union_excluded
      r v hcardv hdropv j k hAcard hB hjv hkv hAv
  have hBswap : r.val.2 = {k, j} := by simpa [pair_comm] using hB
  have hcellU :=
    directionalRootPatternSubsetCell_eq_forced_union_excluded
      r u hcardu hdropu k j hAcard hBswap hku hju hAu
  have hdisjV := restorationFanForcedSubsetSlice_disjoint_excluded
    r v hcardv hdropv j
  have hdisjU := restorationFanForcedSubsetSlice_disjoint_excluded
    r u hcardu hdropu k
  ext S
  constructor
  · intro hS
    have hnotTotal := (Finset.mem_sdiff.mp hS).2
    have hnotLower :
        S ∉ pairedRestorationFanSubsetUnion r v u j k := by
      intro hLower
      exact hnotTotal (Finset.mem_union_left _ (Finset.mem_union_left _ hLower))
    have hnotB : S ∉ blockedSignatureUpperSubsetLayer r.val.2 := by
      intro hUpper
      exact hnotTotal (Finset.mem_union_left _ (Finset.mem_union_right _ hUpper))
    have hnotA : S ∉ blockedSignatureUpperSubsetLayer r.val.1 := by
      intro hUpper
      exact hnotTotal (Finset.mem_union_right _ hUpper)
    have haS : a ∉ S := by
      intro ha
      apply hnotA
      rw [mem_blockedSignatureUpperSubsetLayer_iff, hA]
      simpa using ha
    by_cases hjS : j ∈ S
    · by_cases hkS : k ∈ S
      · exact False.elim (hnotB <| by
          rw [mem_blockedSignatureUpperSubsetLayer_iff, hB]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hjS
          · exact hkS)
      · have hCell : S ∈ directionalRootPatternSubsetCell r j := by
          apply Finset.mem_inter.mpr
          constructor
          · rw [mem_blockedSignatureUpperSubsetLayer_iff]
            simpa using hjS
          · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
            intro x hxS
            apply Finset.mem_sdiff.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            intro hxErase
            have hxR := Finset.mem_of_mem_erase hxErase
            rcases Finset.mem_union.mp hxR with hxRA | hxRB
            · have hxa : x = a := by simpa [hA] using hxRA
              exact haS (hxa ▸ hxS)
            · rw [hB] at hxRB
              simp only [Finset.mem_insert, Finset.mem_singleton] at hxRB
              rcases hxRB with rfl | rfl
              · exact (Finset.mem_erase.mp hxErase).1 rfl
              · exact hkS hxS
        rw [hcellV] at hCell
        rcases Finset.mem_union.mp hCell with hFan | hExcluded
        · exact False.elim (hnotLower <| Finset.mem_union_right _
            (Finset.mem_union_left _ hFan))
        · exact Finset.mem_union_left _ hExcluded
    · by_cases hkS : k ∈ S
      · have hCell : S ∈ directionalRootPatternSubsetCell r k := by
          apply Finset.mem_inter.mpr
          constructor
          · rw [mem_blockedSignatureUpperSubsetLayer_iff]
            simpa using hkS
          · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
            intro x hxS
            apply Finset.mem_sdiff.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            intro hxErase
            have hxR := Finset.mem_of_mem_erase hxErase
            rcases Finset.mem_union.mp hxR with hxRA | hxRB
            · have hxa : x = a := by simpa [hA] using hxRA
              exact haS (hxa ▸ hxS)
            · rw [hB] at hxRB
              simp only [Finset.mem_insert, Finset.mem_singleton] at hxRB
              rcases hxRB with rfl | rfl
              · exact hjS hxS
              · exact (Finset.mem_erase.mp hxErase).1 rfl
        rw [hcellU] at hCell
        rcases Finset.mem_union.mp hCell with hFan | hExcluded
        · exact False.elim (hnotLower <| Finset.mem_union_right _
            (Finset.mem_union_right _ hFan))
        · exact Finset.mem_union_right _ hExcluded
      · exfalso
        apply hnotLower
        apply Finset.mem_union_left
        rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
        intro x hxS
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hxR
        rcases Finset.mem_union.mp hxR with hxRA | hxRB
        · have hxa : x = a := by simpa [hA] using hxRA
          exact haS (hxa ▸ hxS)
        · rw [hB] at hxRB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxRB
          rcases hxRB with rfl | rfl
          · exact hjS hxS
          · exact hkS hxS
  · intro hS
    have hSuniv : S ∈ (Finset.univ : Finset (Finset (Fin m))) :=
      Finset.mem_univ _
    apply Finset.mem_sdiff.mpr
    refine ⟨hSuniv, ?_⟩
    intro hTotal
    rcases Finset.mem_union.mp hS with hEv | hEu
    · have hCell : S ∈ directionalRootPatternSubsetCell r j := by
        rw [hcellV]
        exact Finset.mem_union_right _ hEv
      have hjMem := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hCell).1) (Finset.mem_singleton_self j)
      have hLower := (Finset.mem_inter.mp hCell).2
      have hkNot : k ∉ S := by
        intro hkMem
        have hkErase : k ∈ (reducedCollisionSupport r).erase j := by
          apply Finset.mem_erase.mpr
          exact ⟨Ne.symm hjk, Finset.mem_union_right _ (by rw [hB]; simp)⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hkMem)).2 hkErase
      have haNot : a ∉ S := by
        intro haMem
        have haRoot : a ∈ reducedCollisionSupport r := by
          exact Finset.mem_union_left _ (by rw [hA]; simp)
        have haErase : a ∈ (reducedCollisionSupport r).erase j := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, haRoot⟩
          intro haj
          have haA : a ∈ r.val.1 := by rw [hA]; simp
          have haB : a ∈ r.val.2 := by rw [hB]; simp [haj]
          exact Finset.disjoint_left.mp r.property.1
            haA haB
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower haMem)).2 haErase
      rcases Finset.mem_union.mp hTotal with hTail | hUpperA
      · rcases Finset.mem_union.mp hTail with hLowerAll | hUpperB
        · rcases Finset.mem_union.mp hLowerAll with hRoot | hSlices
          · have hAllowed := Finset.mem_powerset.mp hRoot hjMem
            exact (Finset.mem_sdiff.mp hAllowed).2
              (Finset.mem_union_right _ (by rw [hB]; simp))
          · rcases Finset.mem_union.mp hSlices with hFv | hFu
            · exact Finset.disjoint_left.mp hdisjV hFv hEv
            · have hkForced :=
                (mem_blockedSignatureUpperSubsetLayer_iff.mp
                  (Finset.mem_inter.mp hFu).1) (Finset.mem_singleton_self k)
              exact hkNot hkForced
        · exact hkNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hUpperB)
            (by rw [hB]; simp))
      · exact haNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hUpperA)
          (by rw [hA]; simp))
    · have hCell : S ∈ directionalRootPatternSubsetCell r k := by
        rw [hcellU]
        exact Finset.mem_union_right _ hEu
      have hkMem := (mem_blockedSignatureUpperSubsetLayer_iff.mp
        (Finset.mem_inter.mp hCell).1) (Finset.mem_singleton_self k)
      have hLower := (Finset.mem_inter.mp hCell).2
      have hjNot : j ∉ S := by
        intro hjMem
        have hjErase : j ∈ (reducedCollisionSupport r).erase k := by
          apply Finset.mem_erase.mpr
          exact ⟨hjk, Finset.mem_union_right _ (by rw [hB]; simp)⟩
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower hjMem)).2 hjErase
      have haNot : a ∉ S := by
        intro haMem
        have haRoot : a ∈ reducedCollisionSupport r :=
          Finset.mem_union_left _ (by rw [hA]; simp)
        have haErase : a ∈ (reducedCollisionSupport r).erase k := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, haRoot⟩
          intro hak
          have haA : a ∈ r.val.1 := by rw [hA]; simp
          have haB : a ∈ r.val.2 := by rw [hB]; simp [hak]
          exact Finset.disjoint_left.mp r.property.1
            haA haB
        exact (Finset.mem_sdiff.mp
          (Finset.mem_powerset.mp hLower haMem)).2 haErase
      rcases Finset.mem_union.mp hTotal with hTail | hUpperA
      · rcases Finset.mem_union.mp hTail with hLowerAll | hUpperB
        · rcases Finset.mem_union.mp hLowerAll with hRoot | hSlices
          · have hAllowed := Finset.mem_powerset.mp hRoot hkMem
            exact (Finset.mem_sdiff.mp hAllowed).2
              (Finset.mem_union_right _ (by rw [hB]; simp))
          · rcases Finset.mem_union.mp hSlices with hFv | hFu
            · have hjForced :=
                (mem_blockedSignatureUpperSubsetLayer_iff.mp
                  (Finset.mem_inter.mp hFv).1) (Finset.mem_singleton_self j)
              exact hjNot hjForced
            · exact Finset.disjoint_left.mp hdisjU hFu hEu
        · exact hjNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hUpperB)
            (by rw [hB]; simp))
      · exact haNot ((mem_blockedSignatureUpperSubsetLayer_iff.mp hUpperA)
          (by rw [hA]; simp))

/-- An injective map preserves finite set difference exactly. -/
theorem image_sdiff_of_injective
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (A B : Finset X) :
    A.image f \ B.image f = (A \ B).image f := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyA, hyB⟩
    rcases Finset.mem_image.mp hyA with ⟨x, hxA, hxy⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hxA, ?_⟩, hxy⟩
    intro hxB
    exact hyB (Finset.mem_image.mpr ⟨x, hxB, hxy⟩)
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxB⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxA, hxy⟩, ?_⟩
    intro hyB
    rcases Finset.mem_image.mp hyB with ⟨z, hzB, hzy⟩
    have hzx : z = x := hf (hzy.trans hxy.symm)
    exact hxB (hzx ▸ hzB)

/-- Validity lifts the exact ordinary complement identity to subset-sum
values: no value is missing except one of the two excluded target faces. -/
theorem subsetSumRange_sdiff_pairedRestorationFanValueUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
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
    (hAu : (r.val.1 ∩ u.val.2).Nonempty) :
    subsetSumRange g \
        pairedRestorationFanValueUnionWithTailUpperFaces r v u j k =
      restorationFanForcedExcludedValueSlice r v j ∪
        restorationFanForcedExcludedValueSlice r u k := by
  rw [subsetSumRange,
    ← image_pairedRestorationFanSubsetUnionWithTailUpperFaces,
    image_sdiff_of_injective (ssum g) (ssum_injective g hg),
    univ_sdiff_pairedRestorationFanSubsetUnionWithTailUpperFaces
      r v u hcardv hcardu hdropv hdropu j k hjk hAcard hB
        hjv hku hkv hju hAv hAu,
    Finset.image_union,
    restorationFanForcedExcludedValueSlice,
    restorationFanForcedExcludedValueSlice]

end PairedComplement

end MinModulus
