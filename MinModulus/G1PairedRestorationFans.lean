/-
# Paired directional restoration fans

When the dominant root has negative tail `{j,k}`, its two selected escape
targets have opposite root traces: one drops `j` and contains `k`, while the
other drops `k` and contains `j`.  Restrict each target's exact restoration
fan to subsets containing its dropped coordinate.  Each restriction has
twice-cardinality `2w_r-w_target`.  The two directional slices are disjoint
from one another and from the root layer, because their `(j,k)` patterns are
respectively `(1,0)`, `(0,1)`, and `(0,0)`.  The full `{j,k}` upper face has
pattern `(1,1)` and is disjoint as well.

Thus the four pieces realize a structural Boolean packing, not a collection
of unrelated finite cases.  Factor-eight target decay gives a uniform lower
bound of `23w_r/8` before adjoining the upper face.
-/
import MinModulus.G1RestorationFanExactUnion

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

section ExactForcedSlice

/-- Scaling out a disjoint forced set `T` from an upper/lower intersection
commutes with an additional forced set `H`. -/
theorem pow_card_mul_card_upper_union_inter_blocked_eq
    (T H C : Finset (Fin m))
    (hT : Disjoint T (H ∪ C)) (hHC : Disjoint H C) :
    2 ^ T.card *
        (blockedSignatureUpperSubsetLayer (T ∪ H) ∩
          blockedSignatureSubsetLayer C).card =
      (blockedSignatureUpperSubsetLayer H ∩
        blockedSignatureSubsetLayer C).card := by
  have hTH : Disjoint T H := hT.mono_right Finset.subset_union_left
  have hTC : Disjoint T C := hT.mono_right Finset.subset_union_right
  have hTHC : Disjoint (T ∪ H) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨hTC, hHC⟩
  have hcardTH : (T ∪ H).card = T.card + H.card :=
    Finset.card_union_of_disjoint hTH
  have hcardHC : (H ∪ C).card = H.card + C.card :=
    Finset.card_union_of_disjoint hHC
  have hcardTHC : ((T ∪ H) ∪ C).card = T.card + H.card + C.card := by
    rw [Finset.card_union_of_disjoint hTHC, hcardTH]
  have hsumle : T.card + H.card + C.card ≤ m := by
    rw [← hcardTHC]
    simpa using Finset.card_le_univ ((T ∪ H) ∪ C)
  rw [card_upperSubsetLayer_inter_blockedSubsetLayer (T ∪ H) C hTHC,
    card_upperSubsetLayer_inter_blockedSubsetLayer H C hHC,
    hcardTHC, hcardHC, ← pow_add]
  congr 1
  omega

omit [DecidableEq G] in
/-- Forcing coordinates disjoint from the target support removes exactly a
factor `2^|T|` from the whole exact fan, including its excluded face. -/
theorem pow_card_mul_card_upper_inter_restorationFanSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (T : Finset (Fin m))
    (hTq : Disjoint T (reducedCollisionSupport q)) :
    2 ^ T.card *
        (blockedSignatureUpperSubsetLayer T ∩
          restorationFanSubsetUnion r q).card =
      (restorationFanSubsetUnion r q).card := by
  classical
  let H := reducedCollisionRestorationFanSupport r q
  let C := reducedCollisionSupport q \ H
  let UT := blockedSignatureUpperSubsetLayer T
  let UH := blockedSignatureUpperSubsetLayer H
  let LC := blockedSignatureSubsetLayer C
  have hHq : H ⊆ reducedCollisionSupport q :=
    (restorationFanSupport_subset_external r q hcard hdrop).trans
      Finset.sdiff_subset
  have hCq : C ⊆ reducedCollisionSupport q := Finset.sdiff_subset
  have hTH : Disjoint T H := hTq.mono_right hHq
  have hTC : Disjoint T C := hTq.mono_right hCq
  have hTHC : Disjoint T (H ∪ C) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hTH, hTC⟩
  have hHC : Disjoint H C := by
    rw [Finset.disjoint_left]
    intro j hjH hjC
    exact (Finset.mem_sdiff.mp hjC).2 hjH
  have hfan : restorationFanSubsetUnion r q = LC \ UH := by
    simpa [H, C, LC, UH] using
      restorationFanSubsetUnion_eq_lower_sdiff_upper
        r q hcard hdrop
  have hinter : UT ∩ restorationFanSubsetUnion r q =
      (UT ∩ LC) \ UH := by
    rw [hfan]
    ext S
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hremoved : (UT ∩ LC) ∩ UH =
      blockedSignatureUpperSubsetLayer (T ∪ H) ∩ LC := by
    ext S
    dsimp only [UT, UH]
    simp only [Finset.mem_inter,
      mem_blockedSignatureUpperSubsetLayer_iff]
    constructor
    · rintro ⟨⟨hTS, hSLC⟩, hHS⟩
      exact ⟨Finset.union_subset_iff.mpr ⟨hTS, hHS⟩, hSLC⟩
    · rintro ⟨hTHS, hSLC⟩
      have hparts := Finset.union_subset_iff.mp hTHS
      exact ⟨⟨hparts.1, hSLC⟩, hparts.2⟩
  have hscaleMain : 2 ^ T.card * (UT ∩ LC).card = LC.card := by
    simpa [UT, LC] using
      pow_card_mul_card_upper_inter_blocked_eq_blocked T C hTC
  have hscaleRemoved : 2 ^ T.card * ((UT ∩ LC) ∩ UH).card =
      (UH ∩ LC).card := by
    rw [hremoved]
    simpa [UH, LC] using
      pow_card_mul_card_upper_union_inter_blocked_eq T H C hTHC hHC
  calc
    2 ^ T.card *
        (blockedSignatureUpperSubsetLayer T ∩
          restorationFanSubsetUnion r q).card =
        2 ^ T.card * ((UT ∩ LC).card - ((UT ∩ LC) ∩ UH).card) := by
      rw [hinter, Finset.card_sdiff,
        Finset.inter_comm UH (UT ∩ LC)]
    _ = 2 ^ T.card * (UT ∩ LC).card -
        2 ^ T.card * ((UT ∩ LC) ∩ UH).card :=
      Nat.mul_sub_left_distrib _ _ _
    _ = LC.card - (UH ∩ LC).card := by
      rw [hscaleMain, hscaleRemoved]
    _ = (LC \ UH).card := by
      rw [Finset.card_sdiff, Finset.inter_comm]
    _ = (restorationFanSubsetUnion r q).card := by rw [hfan]

/-- The part of a restoration fan whose ordinary subsets contain `j`. -/
noncomputable def restorationFanForcedSubsetSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) :
    Finset (Finset (Fin m)) :=
  blockedSignatureUpperSubsetLayer {j} ∩ restorationFanSubsetUnion r q

/-- The corresponding subset-sum values. -/
noncomputable def restorationFanForcedValueSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) : Finset G :=
  (restorationFanForcedSubsetSlice r q j).image (ssum g)

omit [DecidableEq G] in
/-- A dropped coordinate splits the exact fan into two equal directional
halves.  The subtraction form is retained because it composes directly with
the exact fan count. -/
theorem two_mul_card_restorationFanForcedSubsetSlice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) (hjq : j ∉ reducedCollisionSupport q) :
    2 * (restorationFanForcedSubsetSlice r q j).card =
      2 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) q := by
  have hdisj : Disjoint ({j} : Finset (Fin m))
      (reducedCollisionSupport q) := by
    simpa [Finset.disjoint_left] using hjq
  have hscale :=
    pow_card_mul_card_upper_inter_restorationFanSubsetUnion
      r q hcard hdrop {j} hdisj
  rw [Finset.card_singleton, pow_one,
    card_restorationFanSubsetUnion r q hcard hdrop] at hscale
  exact hscale

/-- Validity transports the exact directional-half count to values. -/
theorem two_mul_card_restorationFanForcedValueSlice
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (j : Fin m) (hjq : j ∉ reducedCollisionSupport q) :
    2 * (restorationFanForcedValueSlice r q j).card =
      2 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) q := by
  rw [restorationFanForcedValueSlice,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    two_mul_card_restorationFanForcedSubsetSlice
      r q hcard hdrop j hjq]

/-- A forced fan slice lies in its singleton upper face. -/
theorem restorationFanForcedValueSlice_subset_upper
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) :
    restorationFanForcedValueSlice r q j ⊆
      blockedSignatureUpperValueLayer g {j} := by
  classical
  intro x hx
  rw [restorationFanForcedValueSlice] at hx
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  rw [blockedSignatureUpperValueLayer]
  exact Finset.mem_image.mpr
    ⟨S, (Finset.mem_inter.mp hS).1, rfl⟩

/-- A forced fan slice remains inside the whole fan. -/
theorem restorationFanForcedValueSlice_subset_fan
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m) :
    restorationFanForcedValueSlice r q j ⊆
      restorationFanValueUnion r q := by
  classical
  intro x hx
  rw [restorationFanForcedValueSlice] at hx
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  rw [restorationFanValueUnion]
  exact Finset.mem_image.mpr
    ⟨S, (Finset.mem_inter.mp hS).2, rfl⟩

end ExactForcedSlice

section PairedPacking

/-- Root layer plus the two opposite directional fan slices. -/
noncomputable def pairedRestorationFanValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  collisionPaddingValueLayer r ∪
    (restorationFanForcedValueSlice r v j ∪
      restorationFanForcedValueSlice r u k)

/-- Add the complete upper face forcing the two root-tail coordinates. -/
noncomputable def pairedRestorationFanValueUnionWithTailUpper
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) : Finset G :=
  pairedRestorationFanValueUnion r v u j k ∪
    blockedSignatureUpperValueLayer g {j, k}

/-- The root layer is disjoint from a slice forcing one of its blocked
coordinates. -/
theorem collisionPaddingValueLayer_disjoint_restorationFanForcedValueSlice
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h) (j : Fin m)
    (hjR : j ∈ reducedCollisionSupport r) :
    Disjoint (collisionPaddingValueLayer r)
      (restorationFanForcedValueSlice r q j) := by
  have hhit : (({j} : Finset (Fin m)) ∩
      reducedCollisionSupport r).Nonempty :=
    ⟨j, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, hjR⟩⟩
  have hdisj :=
    blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
      hg {j} (reducedCollisionSupport r) hhit
  rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]
  exact hdisj.symm.mono Finset.Subset.rfl
    (restorationFanForcedValueSlice_subset_upper r q j)

/-- Opposite directional slices are disjoint when the coordinate forced by
the first belongs to the second target's root trace. -/
theorem restorationFanForcedValueSlices_disjoint
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjR : j ∈ reducedCollisionSupport r)
    (hju : j ∈ reducedCollisionSupport u) :
    Disjoint (restorationFanForcedValueSlice r v j)
      (restorationFanForcedValueSlice r u k) := by
  have hTsub : ({j} : Finset (Fin m)) ⊆ reducedCollisionSupport r := by
    simpa using hjR
  have hTtarget : (({j} : Finset (Fin m)) ∩
      reducedCollisionSupport u).Nonempty :=
    ⟨j, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, hju⟩⟩
  have hdisj :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r u hcardu hdropu {j} hTsub hTtarget
  exact hdisj.mono
    (restorationFanForcedValueSlice_subset_upper r v j)
    (restorationFanForcedValueSlice_subset_fan r u k)

/-- Exact doubled cardinality of the root and the two opposite directional
slices. -/
theorem two_mul_card_pairedRestorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hjR : j ∈ reducedCollisionSupport r)
    (hkR : k ∈ reducedCollisionSupport r)
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hju : j ∈ reducedCollisionSupport u) :
    2 * (pairedRestorationFanValueUnion r v u j k).card =
      6 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) v -
        reducedCollisionWeight (m := m) u := by
  let R := collisionPaddingValueLayer r
  let V := restorationFanForcedValueSlice r v j
  let U := restorationFanForcedValueSlice r u k
  have hRV : Disjoint R V := by
    simpa [R, V] using
      collisionPaddingValueLayer_disjoint_restorationFanForcedValueSlice
        hg r v j hjR
  have hRU : Disjoint R U := by
    simpa [R, U] using
      collisionPaddingValueLayer_disjoint_restorationFanForcedValueSlice
        hg r u k hkR
  have hVU : Disjoint V U := by
    simpa [V, U] using restorationFanForcedValueSlices_disjoint
      hg r v u hcardu hdropu j k hjR hju
  have hR_VU : Disjoint R (V ∪ U) :=
    Finset.disjoint_union_right.mpr ⟨hRV, hRU⟩
  have hcardUnion :
      (pairedRestorationFanValueUnion r v u j k).card =
        R.card + (V.card + U.card) := by
    rw [pairedRestorationFanValueUnion,
      Finset.card_union_of_disjoint hR_VU,
      Finset.card_union_of_disjoint hVU]
  have hRcard : R.card = reducedCollisionWeight (m := m) r := by
    simpa [R] using card_collisionPaddingValueLayer hg r
  have hVcard := two_mul_card_restorationFanForcedValueSlice
    hg r v hcardv hdropv j hjv
  have hUcard := two_mul_card_restorationFanForcedValueSlice
    hg r u hcardu hdropu k hku
  change 2 * V.card = 2 * reducedCollisionWeight (m := m) r -
    reducedCollisionWeight (m := m) v at hVcard
  change 2 * U.card = 2 * reducedCollisionWeight (m := m) r -
    reducedCollisionWeight (m := m) u at hUcard
  have hvle : reducedCollisionWeight (m := m) v ≤
      reducedCollisionWeight (m := m) r := by
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.sub_le_sub_left hcardv m)
  have hule : reducedCollisionWeight (m := m) u ≤
      reducedCollisionWeight (m := m) r := by
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.sub_le_sub_left hcardu m)
  rw [hcardUnion, hRcard]
  omega

/-- Factor-eight decay for both targets yields a `23/8` root-weight packing. -/
theorem twentyThree_mul_weight_le_eight_mul_pairedRestorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hjR : j ∈ reducedCollisionSupport r)
    (hkR : k ∈ reducedCollisionSupport r)
    (hjv : j ∉ reducedCollisionSupport v)
    (hku : k ∉ reducedCollisionSupport u)
    (hju : j ∈ reducedCollisionSupport u)
    (hv8 : 8 * reducedCollisionWeight (m := m) v ≤
      reducedCollisionWeight (m := m) r)
    (hu8 : 8 * reducedCollisionWeight (m := m) u ≤
      reducedCollisionWeight (m := m) r) :
    23 * reducedCollisionWeight (m := m) r ≤
      8 * (pairedRestorationFanValueUnion r v u j k).card := by
  have hexact := two_mul_card_pairedRestorationFanValueUnion
    hg r v u hcardv hcardu hdropv hdropu j k
      hjR hkR hjv hku hju
  omega

/-- The paired lower union remains in the anchored subset-sum cube. -/
theorem pairedRestorationFanValueUnion_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    pairedRestorationFanValueUnion r v u j k ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxR | hxSlices
  · rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support] at hxR
    exact blockedSignatureValueLayer_subset_subsetSumRange _ hxR
  · rcases Finset.mem_union.mp hxSlices with hxV | hxU
    · exact restorationFanValueUnion_subset_subsetSumRange r v
        (restorationFanForcedValueSlice_subset_fan r v j hxV)
    · exact restorationFanValueUnion_subset_subsetSumRange r u
        (restorationFanForcedValueSlice_subset_fan r u k hxU)

/-- The full `{j,k}` upper face is disjoint from all three lower pieces. -/
theorem tailUpper_disjoint_pairedRestorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m)
    (hjR : j ∈ reducedCollisionSupport r)
    (hkR : k ∈ reducedCollisionSupport r)
    (hkv : k ∈ reducedCollisionSupport v)
    (hju : j ∈ reducedCollisionSupport u) :
    Disjoint (blockedSignatureUpperValueLayer g {j, k})
      (pairedRestorationFanValueUnion r v u j k) := by
  have hrootHit : (({j, k} : Finset (Fin m)) ∩
      reducedCollisionSupport r).Nonempty :=
    ⟨j, Finset.mem_inter.mpr ⟨by simp, hjR⟩⟩
  have hRoot :=
    blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
      hg {j, k} (reducedCollisionSupport r) hrootHit
  have hTsub : ({j, k} : Finset (Fin m)) ⊆
      reducedCollisionSupport r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hjR
    · exact hkR
  have hVhit : (({j, k} : Finset (Fin m)) ∩
      reducedCollisionSupport v).Nonempty :=
    ⟨k, Finset.mem_inter.mpr ⟨by simp, hkv⟩⟩
  have hUhit : (({j, k} : Finset (Fin m)) ∩
      reducedCollisionSupport u).Nonempty :=
    ⟨j, Finset.mem_inter.mpr ⟨by simp, hju⟩⟩
  have hV :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r v hcardv hdropv {j, k} hTsub hVhit
  have hU :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r u hcardu hdropu {j, k} hTsub hUhit
  rw [pairedRestorationFanValueUnion, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  exact ⟨hRoot.mono Finset.Subset.rfl (by
      rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]),
    hV.mono Finset.Subset.rfl
      (restorationFanForcedValueSlice_subset_fan r v j),
    hU.mono Finset.Subset.rfl
      (restorationFanForcedValueSlice_subset_fan r u k)⟩

/-- Exact upper-face enlargement of the paired directional packing. -/
theorem card_pairedRestorationFanValueUnionWithTailUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r v u : ReducedSubsetSumCollision g h)
    (hcardv : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hcardu : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hdropv : (reducedCollisionDroppedSupport r v).Nonempty)
    (hdropu : (reducedCollisionDroppedSupport r u).Nonempty)
    (j k : Fin m) (hjk : j ≠ k)
    (hjR : j ∈ reducedCollisionSupport r)
    (hkR : k ∈ reducedCollisionSupport r)
    (hkv : k ∈ reducedCollisionSupport v)
    (hju : j ∈ reducedCollisionSupport u) :
    (pairedRestorationFanValueUnionWithTailUpper r v u j k).card =
      (pairedRestorationFanValueUnion r v u j k).card + 2 ^ (m - 2) := by
  have hdisj := tailUpper_disjoint_pairedRestorationFanValueUnion
    hg r v u hcardv hcardu hdropv hdropu j k hjR hkR hkv hju
  rw [pairedRestorationFanValueUnionWithTailUpper,
    Finset.card_union_of_disjoint hdisj.symm,
    card_blockedSignatureUpperValueLayer hg]
  congr 2
  simp [hjk]

/-- The paired packing and its tail upper face remain in the anchored cube. -/
theorem pairedRestorationFanValueUnionWithTailUpper_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r v u : ReducedSubsetSumCollision g h) (j k : Fin m) :
    pairedRestorationFanValueUnionWithTailUpper r v u j k ⊆
      subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxLower | hxUpper
  · exact pairedRestorationFanValueUnion_subset_subsetSumRange
      r v u j k hxLower
  · rw [blockedSignatureUpperValueLayer] at hxUpper
    rcases Finset.mem_image.mp hxUpper with ⟨S, hS, rfl⟩
    rw [subsetSumRange]
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

end PairedPacking

section CriticalPairedPacking

/-- The live two-tail residual supplies two opposite directional fans.  Their
root/fan union has at least `23w_r/8` values; adjoining the complete negative
upper face retains that whole gain inside the anchored cube. -/
theorem genuineDominant_two_tail_exists_pairedRestorationFan_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ j k : Fin n,
    ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      j ≠ k ∧ r.val.2 = {j, k} ∧
      v ∈ criticalCanonicalReducedCollisions g ∧
      u ∈ criticalCanonicalReducedCollisions g ∧ v ≠ u ∧
      j ∉ reducedCollisionSupport v ∧
      k ∉ reducedCollisionSupport u ∧
      k ∈ reducedCollisionSupport v ∧
      j ∈ reducedCollisionSupport u ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      8 * reducedCollisionWeight (m := n) u ≤
        reducedCollisionWeight (m := n) r ∧
      2 * (pairedRestorationFanValueUnion r v u j k).card =
        6 * reducedCollisionWeight (m := n) r -
          reducedCollisionWeight (m := n) v -
          reducedCollisionWeight (m := n) u ∧
      23 * reducedCollisionWeight (m := n) r ≤
        8 * (pairedRestorationFanValueUnion r v u j k).card ∧
      (pairedRestorationFanValueUnionWithTailUpper r v u j k).card =
        (pairedRestorationFanValueUnion r v u j k).card + 2 ^ (n - 2) ∧
      23 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * (pairedRestorationFanValueUnionWithTailUpper r v u j k).card ∧
      pairedRestorationFanValueUnionWithTailUpper r v u j k ⊆
        subsetSumRange g ∧
      23 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨j, k, v, u, _z, hjk, hB, hvtarget, hutarget, hvu,
      hjv, hku, hkvB, hjuB, _hzv, _hzu, _hzr, _hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with
    ⟨jv, hjvInc⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with
    ⟨ku, hkuInc⟩
  have hjvInc' := mem_canonicalSupportEscapeIncidences_iff.mp hjvInc
  have hkuInc' := mem_canonicalSupportEscapeIncidences_iff.mp hkuInc
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hjvInc'.2.1
  have hucritical : u ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hkuInc'.2.1
  have hjB : j ∈ r.val.2 := by rw [hB]; simp
  have hkB : k ∈ r.val.2 := by rw [hB]; simp
  have hjR : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjB
  have hkR : k ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hkB
  have hvr : v ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r v hjvInc'.1 hjvInc'.2.2.1
  have hur : u ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r u hkuInc'.1 hkuInc'.2.2.1
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
  have hkv : k ∈ reducedCollisionSupport v :=
    Finset.mem_union_right _ hkvB
  have hju : j ∈ reducedCollisionSupport u :=
    Finset.mem_union_right _ hjuB
  have hexact := two_mul_card_pairedRestorationFanValueUnion
    hg r v u hcardv hcardu hdropv hdropu j k
      hjR hkR hjv hku hju
  have htwentyThree :=
    twentyThree_mul_weight_le_eight_mul_pairedRestorationFanValueUnion
      hg r v u hcardv hcardu hdropv hdropu j k
        hjR hkR hjv hku hju hvall.2.2 huall.2.2
  have htailCard := card_pairedRestorationFanValueUnionWithTailUpper
    hg r v u hcardv hcardu hdropv hdropu j k hjk
      hjR hkR hkv hju
  have htailBound :
      23 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * (pairedRestorationFanValueUnionWithTailUpper r v u j k).card := by
    rw [htailCard]
    omega
  have hsubset :=
    pairedRestorationFanValueUnionWithTailUpper_subset_subsetSumRange
      r v u j k
  have hUle :
      (pairedRestorationFanValueUnionWithTailUpper r v u j k).card ≤
        2 ^ n := by
    calc
      (pairedRestorationFanValueUnionWithTailUpper r v u j k).card ≤
          (subsetSumRange g).card := Finset.card_le_card hsubset
      _ = 2 ^ n := card_subsetSumRange g hg
  have hambient := htailBound.trans (Nat.mul_le_mul_left 8 hUle)
  exact ⟨j, k, v, u, hjk, hB, hvcritical, hucritical, hvu,
    hjv, hku, hkv, hju, hvall.2.2, huall.2.2, hexact,
    htwentyThree, htailCard, htailBound, hsubset, hambient⟩

end CriticalPairedPacking

end MinModulus
