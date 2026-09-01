/-
# Packing a fan of depth-normalized restored layers

A support-growing target has more normalization choices than the one selected
by `reducedCollisionRestorationSupport`.  If it drops at least one root
coordinate and has support depth `d`, its external support has at least
`d+1` coordinates.  Choose a `(d+1)`-set `H` there.  For every `e in H`, the
set `H \ {e}` has size `d` and is a valid restoration support.  The resulting
blocked signatures

`supp(q) \ (H \ {e})`

are pairwise distinct and all have the root support cardinality.  Together
with the root signature they index `d+2` full root-weight coordinate
subcubes.  Pairwise intersections have at most half the root weight, so the
second-moment lemma packs the whole normalized fan into the anchored cube
without treating the `2^d` restoration multiplier as repeated raw weight.
-/
import MinModulus.G1SupportStarConcentration
import MinModulus.G1LayerSecondMoment
import MinModulus.G1SignatureUpperFace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A nonempty dropped-root set leaves room for `d+1` external restoration
coordinates. -/
theorem exists_restorationFanSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    ∃ H ⊆ reducedCollisionExternalSupport r q,
      H.card = reducedCollisionSupportDepth r q + 1 := by
  have hexact :=
    card_externalSupport_eq_card_droppedSupport_add_depth r q hcard
  have hdropPos : 0 < (reducedCollisionDroppedSupport r q).card :=
    Finset.card_pos.mpr hdrop
  have hle : reducedCollisionSupportDepth r q + 1 ≤
      (reducedCollisionExternalSupport r q).card := by
    omega
  exact Finset.exists_subset_card_eq hle

/-- A fixed `(depth+1)`-set of external coordinates used to create the
restoration fan. -/
noncomputable def reducedCollisionRestorationFanSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact if hfan :
      (reducedCollisionSupport r).card ≤
          (reducedCollisionSupport q).card ∧
        (reducedCollisionDroppedSupport r q).Nonempty then
    Classical.choose (exists_restorationFanSupport r q hfan.1 hfan.2)
  else ∅

omit [DecidableEq G] in
theorem restorationFanSupport_subset_external
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionExternalSupport r q := by
  classical
  rw [reducedCollisionRestorationFanSupport, dif_pos ⟨hcard, hdrop⟩]
  exact (Classical.choose_spec
    (exists_restorationFanSupport r q hcard hdrop)).1

omit [DecidableEq G] in
theorem card_restorationFanSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (reducedCollisionRestorationFanSupport r q).card =
      reducedCollisionSupportDepth r q + 1 := by
  classical
  rw [reducedCollisionRestorationFanSupport, dif_pos ⟨hcard, hdrop⟩]
  exact (Classical.choose_spec
    (exists_restorationFanSupport r q hcard hdrop)).2

/-- The blocked signature obtained by restoring every fan coordinate except
`e`. -/
noncomputable def restorationFanBlockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (e : Fin m) : Finset (Fin m) :=
  reducedCollisionSupport q \
    ((reducedCollisionRestorationFanSupport r q).erase e)

omit [DecidableEq G] in
/-- Every fan signature has exactly the root support cardinality. -/
theorem card_restorationFanBlockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    {e : Fin m}
    (he : e ∈ reducedCollisionRestorationFanSupport r q) :
    (restorationFanBlockedSupport r q e).card =
      (reducedCollisionSupport r).card := by
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q := hHext.trans Finset.sdiff_subset
  have hEraseQ :
      (reducedCollisionRestorationFanSupport r q).erase e ⊆
        reducedCollisionSupport q := Finset.erase_subset _ _ |>.trans hHq
  rw [restorationFanBlockedSupport,
    Finset.card_sdiff_of_subset hEraseQ,
    Finset.card_erase_of_mem he,
    card_restorationFanSupport r q hcard hdrop]
  simp only [reducedCollisionSupportDepth]
  have hqle : (reducedCollisionSupport q).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport q)
  omega

omit [DecidableEq G] in
/-- Distinct fan indices give distinct blocked signatures. -/
theorem restorationFanBlockedSupport_ne
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    {e f : Fin m}
    (he : e ∈ reducedCollisionRestorationFanSupport r q)
    (_hf : f ∈ reducedCollisionRestorationFanSupport r q)
    (hef : e ≠ f) :
    restorationFanBlockedSupport r q e ≠
      restorationFanBlockedSupport r q f := by
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have heq : e ∈ reducedCollisionSupport q :=
    Finset.sdiff_subset (hHext he)
  have heLeft : e ∈ restorationFanBlockedSupport r q e := by
    exact Finset.mem_sdiff.mpr ⟨heq, by simp⟩
  have heRight : e ∉ restorationFanBlockedSupport r q f := by
    intro heC
    exact (Finset.mem_sdiff.mp heC).2 (Finset.mem_erase.mpr ⟨hef, he⟩)
  intro hEq
  exact heRight (hEq ▸ heLeft)

omit [DecidableEq G] in
/-- A fan signature differs from the root signature because every dropped
root coordinate belongs to the root but not to the target. -/
theorem restorationFanBlockedSupport_ne_rootSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (e : Fin m) :
    restorationFanBlockedSupport r q e ≠
      reducedCollisionSupport r := by
  rcases hdrop with ⟨j, hj⟩
  have hj' := Finset.mem_sdiff.mp hj
  intro hEq
  have hjC : j ∈ restorationFanBlockedSupport r q e := hEq.symm ▸ hj'.1
  exact hj'.2 (Finset.mem_sdiff.mp hjC).1

/-- The root padding value layer is the intrinsic blocked-signature layer of
the root support. -/
theorem collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    collisionPaddingValueLayer r =
      blockedSignatureValueLayer g (reducedCollisionSupport r) := by
  classical
  unfold collisionPaddingValueLayer blockedSignatureValueLayer
  congr 1
  ext S
  rw [mem_collisionPaddingSubsetLayer_iff]
  simp [blockedSignatureSubsetLayer]

/-- Equal-cardinality distinct blocked signatures have at most half-layer
intersection, whether or not they came from the original chosen restoration
support. -/
theorem two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (C D : Finset (Fin m))
    (hcard : C.card = D.card) (hne : C ≠ D) :
    2 * (blockedSignatureValueLayer g C ∩
        blockedSignatureValueLayer g D).card ≤
      2 ^ (m - C.card) := by
  let A := Finset.univ \ C
  let B := Finset.univ \ D
  have hcards : A.card = B.card := by
    simp only [A, B, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hAB : A ≠ B := by
    intro hEq
    apply hne
    ext j
    have hj := Finset.ext_iff.mp hEq j
    simp only [A, B, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
    tauto
  have hinterLe : (A ∩ B).card + 1 ≤ A.card := by
    have hproper : (A ∩ B).card ≠ A.card := by
      intro heq
      have hinterA : A ∩ B = A :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hABsub : A ⊆ B := by
        rw [← hinterA]
        exact Finset.inter_subset_right
      exact hAB (Finset.eq_of_subset_of_card_le hABsub (by omega))
    have hle : (A ∩ B).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hinterLe
  rw [card_blockedSignatureValueLayers_inter hg C D]
  change 2 * 2 ^ (A ∩ B).card ≤ 2 ^ (m - C.card)
  have hAcard : A.card = m - C.card := by
    simp [A, Finset.card_sdiff_of_subset (Finset.subset_univ C)]
  rw [← hAcard]
  simpa [pow_succ, Nat.mul_comm] using hpow

/-- Every intrinsic blocked-signature layer lies in the anchored tail
subset-sum cube. -/
theorem blockedSignatureValueLayer_subset_subsetSumRange
    {g : Fin (m + 1) → G} (C : Finset (Fin m)) :
    blockedSignatureValueLayer g C ⊆ subsetSumRange g := by
  classical
  intro x hx
  rw [blockedSignatureValueLayer] at hx
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  rw [subsetSumRange]
  exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

/-- Indices for the root layer and all `depth+1` members of one restoration
fan. -/
noncomputable def rootAndRestorationFanLayerIndices
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Option (Fin m)) := by
  classical
  exact insert none <|
    (reducedCollisionRestorationFanSupport r q).image some

/-- The normalized value layer associated to a restoration-fan index. -/
noncomputable def rootAndRestorationFanLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Option (Fin m) → Finset G
  | none => collisionPaddingValueLayer r
  | some e => blockedSignatureValueLayer g
      (restorationFanBlockedSupport r q e)

omit [DecidableEq G] in
@[simp] theorem none_mem_rootAndRestorationFanLayerIndices
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    none ∈ rootAndRestorationFanLayerIndices r q := by
  classical
  simp [rootAndRestorationFanLayerIndices]

omit [DecidableEq G] in
@[simp] theorem some_mem_rootAndRestorationFanLayerIndices_iff
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) {e : Fin m} :
    some e ∈ rootAndRestorationFanLayerIndices r q ↔
      e ∈ reducedCollisionRestorationFanSupport r q := by
  classical
  simp [rootAndRestorationFanLayerIndices]

omit [DecidableEq G] in
/-- The augmented fan has exactly `depth+2` layers. -/
theorem card_rootAndRestorationFanLayerIndices
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (rootAndRestorationFanLayerIndices r q).card =
      reducedCollisionSupportDepth r q + 2 := by
  classical
  have hnone : none ∉
      (reducedCollisionRestorationFanSupport r q).image some := by simp
  have himage :
      ((reducedCollisionRestorationFanSupport r q).image some).card =
        (reducedCollisionRestorationFanSupport r q).card := by
    apply Finset.card_image_of_injective
    intro e f hef
    exact Option.some.inj hef
  rw [rootAndRestorationFanLayerIndices,
    Finset.card_insert_of_notMem hnone, himage,
    card_restorationFanSupport r q hcard hdrop]

/-- Every normalized layer in the restoration fan has the full root padding
weight. -/
theorem card_rootAndRestorationFanLayer_eq_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (i : Option (Fin m))
    (hi : i ∈ rootAndRestorationFanLayerIndices r q) :
    (rootAndRestorationFanLayer r q i).card =
      reducedCollisionWeight (m := m) r := by
  cases i with
  | none =>
      simpa [rootAndRestorationFanLayer] using
        card_collisionPaddingValueLayer hg r
  | some e =>
      have he := (some_mem_rootAndRestorationFanLayerIndices_iff r q).mp hi
      rw [rootAndRestorationFanLayer,
        card_blockedSignatureValueLayer hg,
        card_restorationFanBlockedSupport r q hcard hdrop he]
      rfl

/-- Distinct layers in the root-augmented restoration fan overlap in at most
half of the root weight. -/
theorem two_mul_card_rootAndRestorationFanLayers_inter_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (i : Option (Fin m))
    (hi : i ∈ rootAndRestorationFanLayerIndices r q)
    (j : Option (Fin m))
    (hj : j ∈ rootAndRestorationFanLayerIndices r q)
    (hij : i ≠ j) :
    2 * (rootAndRestorationFanLayer r q i ∩
        rootAndRestorationFanLayer r q j).card ≤
      reducedCollisionWeight (m := m) r := by
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some f =>
          have hf :=
            (some_mem_rootAndRestorationFanLayerIndices_iff r q).mp hj
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (reducedCollisionSupport r)
                (restorationFanBlockedSupport r q f)
                (card_restorationFanBlockedSupport r q hcard hdrop hf).symm
                (Ne.symm <|
                  restorationFanBlockedSupport_ne_rootSupport r q hdrop f)
          simpa only [rootAndRestorationFanLayer,
            collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support,
            reducedCollisionWeight, reducedCollisionSupport] using hbound
  | some e =>
      have he :=
        (some_mem_rootAndRestorationFanLayerIndices_iff r q).mp hi
      cases j with
      | none =>
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (restorationFanBlockedSupport r q e)
                (reducedCollisionSupport r)
                (card_restorationFanBlockedSupport r q hcard hdrop he)
                (restorationFanBlockedSupport_ne_rootSupport r q hdrop e)
          rw [card_restorationFanBlockedSupport r q hcard hdrop he] at hbound
          simpa only [rootAndRestorationFanLayer,
            collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support,
            reducedCollisionWeight, reducedCollisionSupport] using hbound
      | some f =>
          have hf :=
            (some_mem_rootAndRestorationFanLayerIndices_iff r q).mp hj
          have hef : e ≠ f := by
            intro hef
            subst f
            exact hij rfl
          have hbound :=
            two_mul_card_blockedSignatureValueLayers_inter_le_of_card_eq_of_ne
              hg (restorationFanBlockedSupport r q e)
                (restorationFanBlockedSupport r q f)
                ((card_restorationFanBlockedSupport r q hcard hdrop he).trans
                  (card_restorationFanBlockedSupport
                    r q hcard hdrop hf).symm)
                (restorationFanBlockedSupport_ne
                  r q hcard hdrop he hf hef)
          rw [card_restorationFanBlockedSupport r q hcard hdrop he] at hbound
          simpa only [rootAndRestorationFanLayer, reducedCollisionWeight,
            reducedCollisionSupport] using hbound

/-- Every layer of the root-augmented restoration fan remains inside the
anchored tail subset-sum cube. -/
theorem biUnion_rootAndRestorationFanLayer_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    (rootAndRestorationFanLayerIndices r q).biUnion
        (rootAndRestorationFanLayer r q) ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  cases i with
  | none =>
      rw [rootAndRestorationFanLayer] at hxi
      rw [collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]
        at hxi
      exact blockedSignatureValueLayer_subset_subsetSumRange _ hxi
  | some e =>
      rw [rootAndRestorationFanLayer] at hxi
      exact blockedSignatureValueLayer_subset_subsetSumRange _ hxi

/-- Exact second-moment packing of all `depth+1` normalized fan layers
together with the root layer. -/
theorem restorationFan_normalized_packing
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    2 * (reducedCollisionSupportDepth r q + 2) *
        reducedCollisionWeight (m := m) r ≤
      (reducedCollisionSupportDepth r q + 3) *
        ((rootAndRestorationFanLayerIndices r q).biUnion
          (rootAndRestorationFanLayer r q)).card := by
  classical
  let F := rootAndRestorationFanLayerIndices r q
  let L := rootAndRestorationFanLayer r q
  have hF : F.Nonempty := ⟨none,
    none_mem_rootAndRestorationFanLayerIndices r q⟩
  have hbound := two_mul_card_mul_weight_le_succ_mul_familyUnion_card
    F L (reducedCollisionWeight (m := m) r) hF
      (by simp [reducedCollisionWeight])
      (fun i hi ↦ card_rootAndRestorationFanLayer_eq_rootWeight
        hg r q hcard hdrop i hi)
      (fun i hi j hj hij ↦
        two_mul_card_rootAndRestorationFanLayers_inter_le
          hg r q hcard hdrop i hi j hj hij)
  have hFcard := card_rootAndRestorationFanLayerIndices r q hcard hdrop
  simpa [F, L, hFcard, Nat.add_assoc] using hbound

/-- At depth at least three, the normalized restoration fan occupies at least
five thirds of one root-weight layer. -/
theorem five_mul_weight_le_three_mul_restorationFanUnion_of_depth_three
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (hdepth : 3 ≤ reducedCollisionSupportDepth r q) :
    5 * reducedCollisionWeight (m := m) r ≤
      3 * ((rootAndRestorationFanLayerIndices r q).biUnion
        (rootAndRestorationFanLayer r q)).card := by
  let k := reducedCollisionSupportDepth r q + 2
  let U := ((rootAndRestorationFanLayerIndices r q).biUnion
    (rootAndRestorationFanLayer r q)).card
  have hk : 5 ≤ k := by simp [k]; omega
  have hpack := restorationFan_normalized_packing hg r q hcard hdrop
  change 2 * k * reducedCollisionWeight (m := m) r ≤ (k + 1) * U
    at hpack
  have hscaled := Nat.mul_le_mul_left 3 hpack
  have hfactor : (k + 1) *
      (5 * reducedCollisionWeight (m := m) r) ≤
      (k + 1) * (3 * U) := by
    calc
      (k + 1) * (5 * reducedCollisionWeight (m := m) r) ≤
          3 * (2 * k * reducedCollisionWeight (m := m) r) := by
        nlinarith
      _ ≤ 3 * ((k + 1) * U) := hscaled
      _ = (k + 1) * (3 * U) := by ring
  exact Nat.le_of_mul_le_mul_left hfactor (by omega)

omit [DecidableEq G] in
/-- On a root-support coordinate, a fan signature records exactly target
support membership; restoration fan coordinates are all external to the
root. -/
theorem mem_restorationFanBlockedSupport_iff_of_mem_rootSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (e : Fin m) {j : Fin m}
    (hj : j ∈ reducedCollisionSupport r) :
    j ∈ restorationFanBlockedSupport r q e ↔
      j ∈ reducedCollisionSupport q := by
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have hjnotH : j ∉
      (reducedCollisionRestorationFanSupport r q).erase e := by
    intro hjH
    have hjext := hHext (Finset.mem_of_mem_erase hjH)
    exact (Finset.mem_sdiff.mp hjext).2 hj
  simp [restorationFanBlockedSupport, hjnotH]

/-- Validity transfers the elementary upper/lower face disjointness from
ordinary subsets to their subset-sum value images. -/
theorem blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (T C : Finset (Fin m)) (hTC : (T ∩ C).Nonempty) :
    Disjoint (blockedSignatureUpperValueLayer g T)
      (blockedSignatureValueLayer g C) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxUpper hxLower
  rw [blockedSignatureUpperValueLayer] at hxUpper
  rw [blockedSignatureValueLayer] at hxLower
  rcases Finset.mem_image.mp hxUpper with ⟨U, hU, hUx⟩
  rcases Finset.mem_image.mp hxLower with ⟨V, hV, hVx⟩
  have hUV : U = V := ssum_injective g hg (hUx.trans hVx.symm)
  subst V
  exact Finset.disjoint_left.mp
    (blockedSignatureUpperSubsetLayer_disjoint T C hTC) hU hV

/-- Exact cardinality of an upper blocked-signature value face. -/
theorem card_blockedSignatureUpperValueLayer
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (T : Finset (Fin m)) :
    (blockedSignatureUpperValueLayer g T).card = 2 ^ (m - T.card) := by
  classical
  rw [blockedSignatureUpperValueLayer,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer]

/-- Root-augmented restoration fan together with a forced-coordinate upper
face. -/
noncomputable def rootAndRestorationFanValueUnionWithUpper
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (T : Finset (Fin m)) : Finset G :=
  (rootAndRestorationFanLayerIndices r q).biUnion
      (rootAndRestorationFanLayer r q) ∪
    blockedSignatureUpperValueLayer g T

/-- An upper face meeting the root and target supports is disjoint from every
layer in the restoration fan. -/
theorem blockedSignatureUpperValueLayer_disjoint_restorationFanUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (T : Finset (Fin m))
    (hTsub : T ⊆ reducedCollisionSupport r)
    (hTroot : (T ∩ reducedCollisionSupport r).Nonempty)
    (hTtarget : (T ∩ reducedCollisionSupport q).Nonempty) :
    Disjoint (blockedSignatureUpperValueLayer g T)
      ((rootAndRestorationFanLayerIndices r q).biUnion
        (rootAndRestorationFanLayer r q)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxUpper hxFan
  rcases Finset.mem_biUnion.mp hxFan with ⟨i, hi, hxi⟩
  cases i with
  | none =>
      rw [rootAndRestorationFanLayer,
        collisionPaddingValueLayer_eq_blockedSignatureValueLayer_support]
        at hxi
      exact Finset.disjoint_left.mp
        (blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
          hg T (reducedCollisionSupport r) hTroot) hxUpper hxi
  | some e =>
      have hTfan :
          (T ∩ restorationFanBlockedSupport r q e).Nonempty := by
        rcases hTtarget with ⟨j, hj⟩
        have hjT := (Finset.mem_inter.mp hj).1
        have hjq := (Finset.mem_inter.mp hj).2
        have hjroot : j ∈ reducedCollisionSupport r := hTsub hjT
        exact ⟨j, Finset.mem_inter.mpr ⟨hjT,
          (mem_restorationFanBlockedSupport_iff_of_mem_rootSupport
            r q hcard hdrop e hjroot).2 hjq⟩⟩
      rw [rootAndRestorationFanLayer] at hxi
      exact Finset.disjoint_left.mp
        (blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
          hg T (restorationFanBlockedSupport r q e) hTfan) hxUpper hxi

/-- The complete restoration fan plus its disjoint upper face remains in the
anchored tail subset-sum cube. -/
theorem rootAndRestorationFanValueUnionWithUpper_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (T : Finset (Fin m)) :
    rootAndRestorationFanValueUnionWithUpper r q T ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxFan | hxUpper
  · exact biUnion_rootAndRestorationFanLayer_subset_subsetSumRange
      r q hxFan
  · rw [blockedSignatureUpperValueLayer] at hxUpper
    rcases Finset.mem_image.mp hxUpper with ⟨S, hS, rfl⟩
    rw [subsetSumRange]
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

/-- Exact normalized fan packing after adjoining a disjoint upper face. -/
theorem restorationFan_normalized_packing_with_upper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (T : Finset (Fin m))
    (hTsub : T ⊆ reducedCollisionSupport r)
    (hTroot : (T ∩ reducedCollisionSupport r).Nonempty)
    (hTtarget : (T ∩ reducedCollisionSupport q).Nonempty) :
    2 * (reducedCollisionSupportDepth r q + 2) *
          reducedCollisionWeight (m := m) r +
        (reducedCollisionSupportDepth r q + 3) * 2 ^ (m - T.card) ≤
      (reducedCollisionSupportDepth r q + 3) *
        (rootAndRestorationFanValueUnionWithUpper r q T).card := by
  let F := (rootAndRestorationFanLayerIndices r q).biUnion
    (rootAndRestorationFanLayer r q)
  let U := blockedSignatureUpperValueLayer g T
  have hdisj :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanUnion
      hg r q hcard hdrop T hTsub hTroot hTtarget
  have hcardUnion :
      (rootAndRestorationFanValueUnionWithUpper r q T).card =
        F.card + U.card := by
    rw [rootAndRestorationFanValueUnionWithUpper,
      Finset.card_union_of_disjoint hdisj.symm]
  have hpack := restorationFan_normalized_packing hg r q hcard hdrop
  have hUcard := card_blockedSignatureUpperValueLayer hg T
  calc
    2 * (reducedCollisionSupportDepth r q + 2) *
          reducedCollisionWeight (m := m) r +
        (reducedCollisionSupportDepth r q + 3) * 2 ^ (m - T.card) ≤
      (reducedCollisionSupportDepth r q + 3) * F.card +
        (reducedCollisionSupportDepth r q + 3) * 2 ^ (m - T.card) :=
      Nat.add_le_add_right hpack _
    _ = (reducedCollisionSupportDepth r q + 3) *
        (F.card + U.card) := by rw [hUcard]; ring
    _ = (reducedCollisionSupportDepth r q + 3) *
        (rootAndRestorationFanValueUnionWithUpper r q T).card := by
      rw [hcardUnion]

/-- Depth three gives the compact `5/3` normalized fan bound together with
the full disjoint upper face. -/
theorem five_mul_weight_add_three_mul_upper_le_three_mul_restorationFanUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (hdepth : 3 ≤ reducedCollisionSupportDepth r q)
    (T : Finset (Fin m))
    (hTsub : T ⊆ reducedCollisionSupport r)
    (hTroot : (T ∩ reducedCollisionSupport r).Nonempty)
    (hTtarget : (T ∩ reducedCollisionSupport q).Nonempty) :
    5 * reducedCollisionWeight (m := m) r + 3 * 2 ^ (m - T.card) ≤
      3 * (rootAndRestorationFanValueUnionWithUpper r q T).card := by
  let F := (rootAndRestorationFanLayerIndices r q).biUnion
    (rootAndRestorationFanLayer r q)
  let U := blockedSignatureUpperValueLayer g T
  have hdisj :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanUnion
      hg r q hcard hdrop T hTsub hTroot hTtarget
  have hcardUnion :
      (rootAndRestorationFanValueUnionWithUpper r q T).card =
        F.card + U.card := by
    rw [rootAndRestorationFanValueUnionWithUpper,
      Finset.card_union_of_disjoint hdisj.symm]
  have hfan := five_mul_weight_le_three_mul_restorationFanUnion_of_depth_three
    hg r q hcard hdrop hdepth
  have hUcard := card_blockedSignatureUpperValueLayer hg T
  calc
    5 * reducedCollisionWeight (m := m) r + 3 * 2 ^ (m - T.card) ≤
        3 * F.card + 3 * 2 ^ (m - T.card) :=
      Nat.add_le_add_right hfan _
    _ = 3 * (F.card + U.card) := by rw [hUcard]; ring
    _ = 3 * (rootAndRestorationFanValueUnionWithUpper r q T).card := by
      rw [hcardUnion]

section CriticalRestorationFan

/-- Both live two-tail exits retain a genuinely dropped root coordinate.  The
all-target star theorem then upgrades the selected target to depth three and
factor-eight padding loss. -/
theorem genuineDominant_two_tail_exists_dropped_eighthWeight_growth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalReducedCollisions (g := g) hh ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      (reducedCollisionDroppedSupport r v).Nonempty ∧
      3 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 3 ≤
        (reducedCollisionSupport v).card ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  rcases genuineDominant_two_tail_escape_growth_or_anchor_exchange
      hqodd g hg r hr hres hBcard with hgrow | hexchange
  · obtain ⟨v, hvtarget, hvB⟩ := hgrow
    rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨j, hjv⟩
    have hjv' := mem_canonicalSupportEscapeIncidences_iff.mp hjv
    have hvcanonical := hjv'.2.1
    have hvr := reducedCollision_ne_of_right_mem_of_avoids
      r v hjv'.1 hjv'.2.2.1
    have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
      simpa [hh, criticalCanonicalReducedCollisions] using hvcanonical
    have hall := genuineDominant_two_tail_all_other_eighthWeight_growth
      hqodd g hg r hr hres hBcard v hvcritical hvr
    have hdrop : (reducedCollisionDroppedSupport r v).Nonempty := by
      exact ⟨j, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ hjv'.1, hjv'.2.2.1⟩⟩
    exact ⟨v, hvcanonical, hvr, hvB, hdrop,
      hall.1, hall.2.1, hall.2.2⟩
  · obtain ⟨v, hvcanonical, hvr, hvB, _hvimbalance,
        _hrBv, hdropA⟩ := hexchange
    have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
      simpa [hh, criticalCanonicalReducedCollisions] using hvcanonical
    have hall := genuineDominant_two_tail_all_other_eighthWeight_growth
      hqodd g hg r hr hres hBcard v hvcritical hvr
    have hdrop : (reducedCollisionDroppedSupport r v).Nonempty := by
      rcases hdropA with ⟨j, hj⟩
      have hj' := Finset.mem_sdiff.mp hj
      exact ⟨j, Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ hj'.1, hj'.2⟩⟩
    exact ⟨v, hvcanonical, hvr, hvB, hdrop,
      hall.1, hall.2.1, hall.2.2⟩

/-- The live two-tail residual contains a depth-indexed normalized fan whose
exact second-moment bound specializes to a `5/3` root-weight expansion. -/
theorem genuineDominant_two_tail_exists_restorationFan_normalized_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      (reducedCollisionDroppedSupport r v).Nonempty ∧
      3 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 3 ≤
        (reducedCollisionSupport v).card ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      2 * (reducedCollisionSupportDepth r v + 2) *
          reducedCollisionWeight (m := n) r ≤
        (reducedCollisionSupportDepth r v + 3) *
          ((rootAndRestorationFanLayerIndices r v).biUnion
            (rootAndRestorationFanLayer r v)).card ∧
      5 * reducedCollisionWeight (m := n) r ≤
        3 * ((rootAndRestorationFanLayerIndices r v).biUnion
          (rootAndRestorationFanLayer r v)).card ∧
      (rootAndRestorationFanLayerIndices r v).biUnion
          (rootAndRestorationFanLayer r v) ⊆ subsetSumRange g := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨v, hv, hvr, hvB, hdrop, hdepth, hplus, heighth⟩ :=
    genuineDominant_two_tail_exists_dropped_eighthWeight_growth
      hqodd g hg r hr hres hBcard
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by omega
  exact ⟨v, hvcritical, hvr, hvB, hdrop, hdepth, hplus, heighth,
    restorationFan_normalized_packing hg r v hcard hdrop,
    five_mul_weight_le_three_mul_restorationFanUnion_of_depth_three
      hg r v hcard hdrop hdepth,
    biUnion_rootAndRestorationFanLayer_subset_subsetSumRange r v⟩

/-- The normalized fan from either live exit is disjoint from the full
negative-tail upper face.  Thus the global expansion retains both the fan
gain and the complete `2^(n-2)` face. -/
theorem genuineDominant_two_tail_exists_restorationFan_tailFace_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      (reducedCollisionDroppedSupport r v).Nonempty ∧
      3 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 3 ≤
        (reducedCollisionSupport v).card ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      2 * (reducedCollisionSupportDepth r v + 2) *
            reducedCollisionWeight (m := n) r +
          (reducedCollisionSupportDepth r v + 3) * 2 ^ (n - 2) ≤
        (reducedCollisionSupportDepth r v + 3) *
          (rootAndRestorationFanValueUnionWithUpper r v r.val.2).card ∧
      5 * reducedCollisionWeight (m := n) r + 3 * 2 ^ (n - 2) ≤
        3 * (rootAndRestorationFanValueUnionWithUpper r v r.val.2).card ∧
      rootAndRestorationFanValueUnionWithUpper r v r.val.2 ⊆
        subsetSumRange g ∧
      5 * reducedCollisionWeight (m := n) r + 3 * 2 ^ (n - 2) ≤
        3 * 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨v, hv, hvr, hvB, hdrop, hdepth, hplus, heighth⟩ :=
    genuineDominant_two_tail_exists_dropped_eighthWeight_growth
      hqodd g hg r hr hres hBcard
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by omega
  have hBsub : r.val.2 ⊆ reducedCollisionSupport r := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hBnonempty : r.val.2.Nonempty := Finset.card_pos.mp (by omega)
  have hBroot : (r.val.2 ∩ reducedCollisionSupport r).Nonempty := by
    rcases hBnonempty with ⟨j, hj⟩
    exact ⟨j, Finset.mem_inter.mpr ⟨hj, hBsub hj⟩⟩
  have hBtarget : (r.val.2 ∩ reducedCollisionSupport v).Nonempty := by
    have hinter := canonicalReducedCollision_negative_tails_inter
      g hg hh (half_ne_zero hN hM) r v
        (mem_canonicalReducedCollisions_iff.mp hr')
        (mem_canonicalReducedCollisions_iff.mp hv)
    rcases hinter with ⟨j, hj⟩
    exact ⟨j, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hj).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp hj).2⟩⟩
  have hexact := restorationFan_normalized_packing_with_upper
    hg r v hcard hdrop r.val.2 hBsub hBroot hBtarget
  have hcompact :=
    five_mul_weight_add_three_mul_upper_le_three_mul_restorationFanUnion
      hg r v hcard hdrop hdepth r.val.2 hBsub hBroot hBtarget
  have hsubset :=
    rootAndRestorationFanValueUnionWithUpper_subset_subsetSumRange
      r v r.val.2
  have hUle :
      (rootAndRestorationFanValueUnionWithUpper r v r.val.2).card ≤
        2 ^ n := by
    calc
      (rootAndRestorationFanValueUnionWithUpper r v r.val.2).card ≤
          (subsetSumRange g).card := Finset.card_le_card hsubset
      _ = 2 ^ n := card_subsetSumRange g hg
  have hambient :
      5 * reducedCollisionWeight (m := n) r + 3 * 2 ^ (n - 2) ≤
        3 * 2 ^ n := by
    rw [hBcard] at hcompact
    exact hcompact.trans (Nat.mul_le_mul_left 3 hUle)
  rw [hBcard] at hexact hcompact
  exact ⟨v, hvcritical, hvr, hvB, hdrop, hdepth, hplus, heighth,
    hexact, hcompact, hsubset, hambient⟩

end CriticalRestorationFan

end MinModulus
