/-
# Charging the anchor exchange through the positive upper face

The three-private-slice count gives one extra half-layer beyond the two
selected escape signatures.  When the source positive tail is adjoined, the
exchange layer can overlap that upper face.  This file measures the overlap
exactly enough to feed the private-slice gain into the global hybrid/crossing
budget.

After scaling by `2^|A_r|`, the exchange contamination costs at most one root
weight.  Hence the gain is neutral when `|A_r| = 1`, but a full extra root
weight survives when `|A_r| = 2`.
-/
import MinModulus.G1AnchorExchangePrivateSlices
import MinModulus.G1SignatureHybridBound

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The ordinary escape-signature lower union, enlarged by one extra blocked
signature, the negative-tail upper face, and finally the positive-tail upper
face. -/
noncomputable def rootEscapeExtraBlockedSignatureSubsetUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (E : Finset (Fin m)) :
    Finset (Finset (Fin m)) :=
  rootAndBlockedSignatureSubsetUnionWithUpper r.val.2
      (reducedCollisionSupport r)
      (insert E (canonicalSupportEscapeBlockedSignatures hh r)) ∪
    blockedSignatureUpperSubsetLayer r.val.1

/-- Adding one equal-codimension extra signature to the escape family can
only add its own lower Boolean layer. -/
theorem rootAndBlockedSignatureSubsetUnionWithUpper_insert_subset
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (E : Finset (Fin m)) :
    rootAndBlockedSignatureSubsetUnionWithUpper r.val.2
        (reducedCollisionSupport r)
        (insert E (canonicalSupportEscapeBlockedSignatures hh r)) ⊆
      rootAndBlockedSignatureSubsetUnionWithUpper r.val.2
          (reducedCollisionSupport r)
          (canonicalSupportEscapeBlockedSignatures hh r) ∪
        blockedSignatureSubsetLayer E := by
  classical
  intro U hU
  rcases Finset.mem_union.mp hU with hLower | hUpper
  · rcases Finset.mem_union.mp hLower with hRoot | hFamily
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hRoot))
    · rcases Finset.mem_biUnion.mp hFamily with ⟨C, hC, hUC⟩
      rcases Finset.mem_insert.mp hC with rfl | hCS
      · exact Finset.mem_union_right _ hUC
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨C, hCS, hUC⟩)))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ hUpper)

/-- A private-slice lower bound for two escape signatures and one extra
canonical signature improves the global hybrid bound.  Positive-upper
contamination from ordinary escape signatures is charged to crossing mass;
the extra signature costs at most one root weight after scaling. -/
theorem anchorExchange_privateSlice_hybrid_bound
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r v u w : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hA : r.val.1.Nonempty)
    (hvtarget : v ∈ canonicalSupportEscapeTargets hh r)
    (hutarget : u ∈ canonicalSupportEscapeTargets hh r)
    (hwcanonical : w ∈ canonicalReducedCollisions (g := g) hh)
    (hprivate : 5 * reducedCollisionWeight (m := m) r ≤
      2 * (rootThreeBlockedSignatureValueUnion r v u w).card) :
    2 ^ r.val.1.card *
        (3 * reducedCollisionWeight (m := m) r +
          2 * 2 ^ (m - r.val.1.card) +
          2 * 2 ^ (m - r.val.2.card)) ≤
      2 * (2 ^ r.val.1.card * 2 ^ m) +
        2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        2 * reducedCollisionWeight (m := m) r := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let C := restoredCollisionBlockedSupport r v
  let D := restoredCollisionBlockedSupport r u
  let E := restoredCollisionBlockedSupport r w
  let S' := insert E S
  let Lower := rootAndBlockedSignatureSubsetUnion R S'
  let Tail := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S'
  let BaseTail := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let Extra := blockedSignatureSubsetLayer E
  let Total := Tail ∪ UA
  let J := positiveUpperSignatureContamination hh r
  let crossMass :=
    (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
      reducedCollisionWeight (m := m) p.1 *
        reducedCollisionWeight (m := m) p.2)
  let W := reducedCollisionWeight (m := m) r
  let P := 2 ^ r.val.1.card
  have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
    rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨j, hj⟩
    exact (mem_canonicalSupportEscapeIncidences_iff.mp hj).2.1
  have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
    rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨j, hj⟩
    exact (mem_canonicalSupportEscapeIncidences_iff.mp hj).2.1
  have hC : C ∈ S := by
    exact mem_canonicalSupportEscapeBlockedSignatures_iff.mpr
      ⟨v, hvtarget, rfl⟩
  have hD : D ∈ S := by
    exact mem_canonicalSupportEscapeBlockedSignatures_iff.mpr
      ⟨u, hutarget, rfl⟩
  have hselectedSubset :
      rootAndBlockedSignatureSubsetUnion R {C, D, E} ⊆ Lower := by
    intro U hU
    rcases Finset.mem_union.mp hU with hRoot | hFamily
    · exact Finset.mem_union_left _ hRoot
    · rcases Finset.mem_biUnion.mp hFamily with ⟨Q, hQ, hUQ⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨Q, ?_, hUQ⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl | rfl
      · exact Finset.mem_insert_of_mem hC
      · exact Finset.mem_insert_of_mem hD
      · exact Finset.mem_insert_self E S
  have hselectedCard :
      (rootAndBlockedSignatureSubsetUnion R {C, D, E}).card =
        (rootThreeBlockedSignatureValueUnion r v u w).card := by
    rw [rootThreeBlockedSignatureValueUnion,
      Finset.card_image_of_injective _ (ssum_injective g hg)]
  have hlower : 5 * W ≤ 2 * Lower.card := by
    have hp : 5 * W ≤
        2 * (rootAndBlockedSignatureSubsetUnion R {C, D, E}).card := by
      simpa [W, hselectedCard] using hprivate
    exact hp.trans
      (Nat.mul_le_mul_left 2 (Finset.card_mono hselectedSubset))
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBR : (r.val.2 ∩ R).Nonempty := by
    obtain ⟨j, hj⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr
      ⟨hj, Finset.mem_union_right _ hj⟩⟩
  have hBinterS : ∀ Q ∈ S, (r.val.2 ∩ Q).Nonempty := by
    intro Q hQ
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hQ
  have hwmin := hrmin w hwcanonical
  have hBE : (r.val.2 ∩ E).Nonempty := by
    obtain ⟨j, hj⟩ := canonicalReducedCollision_negative_tails_inter
      g hg hh hh0 r w
        (mem_canonicalReducedCollisions_iff.mp hr)
        (mem_canonicalReducedCollisions_iff.mp hwcanonical)
    have hjr := (Finset.mem_inter.mp hj).1
    have hjw := (Finset.mem_inter.mp hj).2
    refine ⟨j, Finset.mem_inter.mpr ⟨hjr, ?_⟩⟩
    exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r w hwmin (Finset.mem_union_right _ hjr)).mpr
        (Finset.mem_union_right _ hjw)
  have hBinter : ∀ Q ∈ S', (r.val.2 ∩ Q).Nonempty := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQS
    · exact hBE
    · exact hBinterS Q hQS
  have htailCard : Tail.card = Lower.card +
      (blockedSignatureSubsetLayer r.val.2).card := by
    simpa [Tail, Lower, R, S'] using
      card_rootAndBlockedSignatureSubsetUnionWithUpper
        r.val.2 R S' hBR hBinter
  have htail : 5 * W +
        2 * (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 * Tail.card := by
    have hUB : (blockedSignatureUpperSubsetLayer r.val.2).card =
        (blockedSignatureSubsetLayer r.val.2).card :=
      card_blockedSignatureUpperSubsetLayer r.val.2
    rw [htailCard, hUB]
    omega
  have hTailSubset : Tail ⊆ BaseTail ∪ Extra := by
    simpa [Tail, BaseTail, Extra, R, S, E] using
      rootAndBlockedSignatureSubsetUnionWithUpper_insert_subset hh r E
  have hInterSubset : Tail ∩ UA ⊆
      (BaseTail ∩ UA) ∪ (Extra ∩ UA) := by
    intro V hV
    have hVTail := (Finset.mem_inter.mp hV).1
    have hVUA := (Finset.mem_inter.mp hV).2
    rcases Finset.mem_union.mp (hTailSubset hVTail) with hVBase | hVExtra
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hVBase, hVUA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hVExtra, hVUA⟩)
  have hrootCard : (blockedSignatureSubsetLayer R).card = W := by
    rw [card_blockedSignatureSubsetLayer]
    rfl
  have hbaseInter : (BaseTail ∩ UA).card ≤ J.card + W := by
    have hbase := card_positiveUpper_inter_tailEnriched_le hh r hA
    rw [hrootCard] at hbase
    simpa [BaseTail, UA, J, Finset.inter_comm] using hbase
  have hInter : (Tail ∩ UA).card ≤
      J.card + W + (Extra ∩ UA).card := by
    calc
      (Tail ∩ UA).card ≤
          ((BaseTail ∩ UA) ∪ (Extra ∩ UA)).card :=
        Finset.card_mono hInterSubset
      _ ≤ (BaseTail ∩ UA).card + (Extra ∩ UA).card :=
        Finset.card_union_le _ _
      _ ≤ J.card + W + (Extra ∩ UA).card := by omega
  have hEcard : E.card = R.card := by
    simpa [E, R] using card_restoredCollisionBlockedSupport r w hwmin
  have hExtraScale : P * (Extra ∩ UA).card ≤ W := by
    by_cases hAE : (r.val.1 ∩ E).Nonempty
    · have hdisj := blockedSignatureUpperSubsetLayer_disjoint
        r.val.1 E hAE
      have hempty : Extra ∩ UA = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        simpa [Extra, UA] using hdisj.symm
      simp [hempty]
    · have hAEDisj : Disjoint r.val.1 E := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact Finset.not_nonempty_iff_eq_empty.mp hAE
      have hscale := pow_card_mul_card_upper_inter_blocked_eq_blocked
        r.val.1 E hAEDisj
      have hblockedCard : (blockedSignatureSubsetLayer E).card = W := by
        rw [card_blockedSignatureSubsetLayer, hEcard]
        simpa [card_blockedSignatureSubsetLayer] using hrootCard
      have hscale' : P * (Extra ∩ UA).card = W := by
        simpa [P, Extra, UA, Finset.inter_comm, hblockedCard] using hscale
      exact hscale'.le
  have hJscale : P * J.card ≤ crossMass := by
    simpa [P, J, crossMass] using
      pow_positiveCard_mul_contamination_le_crossMass
        hg hh hh0 r hr hrmin
  have hInterScale : P * (Tail ∩ UA).card ≤
      crossMass + P * W + W := by
    calc
      P * (Tail ∩ UA).card ≤ P * (J.card + W + (Extra ∩ UA).card) :=
        Nat.mul_le_mul_left P hInter
      _ = P * J.card + P * W + P * (Extra ∩ UA).card := by ring
      _ ≤ crossMass + P * W + W :=
        Nat.add_le_add (Nat.add_le_add_right hJscale _) hExtraScale
  have htotalCube : Total.card ≤ 2 ^ m := by
    have hsubset : Total ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro V _
      exact Finset.mem_powerset.mpr (Finset.subset_univ V)
    calc
      Total.card ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
        Finset.card_mono hsubset
      _ = 2 ^ m := by
        rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have hdecomp : Tail.card + UA.card =
      Total.card + (Tail ∩ UA).card := by
    simpa [Total] using (Finset.card_union_add_card_inter Tail UA).symm
  have hmass : 5 * W +
        2 * (blockedSignatureUpperSubsetLayer r.val.2).card +
        2 * UA.card ≤
      2 * (2 ^ m + (Tail ∩ UA).card) := by
    calc
      5 * W + 2 * (blockedSignatureUpperSubsetLayer r.val.2).card +
          2 * UA.card ≤ 2 * Tail.card + 2 * UA.card := by omega
      _ = 2 * (Tail.card + UA.card) := by ring
      _ = 2 * (Total.card + (Tail ∩ UA).card) := by rw [hdecomp]
      _ ≤ 2 * (2 ^ m + (Tail ∩ UA).card) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add_right htotalCube _)
  have hmassScaled := Nat.mul_le_mul_left P hmass
  have hUpperA : UA.card = 2 ^ (m - r.val.1.card) := by
    dsimp only [UA]
    rw [card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
  have hUpperB : (blockedSignatureUpperSubsetLayer r.val.2).card =
      2 ^ (m - r.val.2.card) := by
    rw [card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
  dsimp only [P, W, crossMass] at hmassScaled hInterScale ⊢
  rw [hUpperA, hUpperB] at hmassScaled
  ring_nf at hmassScaled hInterScale ⊢
  omega

/-- Exact net gain after moving the extra-signature contamination to the
right and cancelling it.  The private exchange contributes
`(2^|A_r| - 2) w_r` beyond twice the old hybrid inequality.  Thus a singleton
positive tail absorbs the gain exactly, while every larger positive tail
retains a genuine padding-weighted surplus. -/
theorem anchorExchange_privateSlice_hybrid_surplus
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r v u w : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hA : r.val.1.Nonempty)
    (hvtarget : v ∈ canonicalSupportEscapeTargets hh r)
    (hutarget : u ∈ canonicalSupportEscapeTargets hh r)
    (hwcanonical : w ∈ canonicalReducedCollisions (g := g) hh)
    (hprivate : 5 * reducedCollisionWeight (m := m) r ≤
      2 * (rootThreeBlockedSignatureValueUnion r v u w).card) :
    2 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card))) +
        (2 ^ r.val.1.card - 2) *
          reducedCollisionWeight (m := m) r ≤
      2 * (2 ^ r.val.1.card * 2 ^ m) +
        2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) := by
  have hbound := anchorExchange_privateSlice_hybrid_bound
    hg hh hh0 r v u w hr hrmin hA hvtarget hutarget hwcanonical hprivate
  let P := 2 ^ r.val.1.card
  let K := P - 2
  have hcardPos : 1 ≤ r.val.1.card := Finset.one_le_card.mpr hA
  have hP : 2 ≤ P := by
    have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hcardPos
    simpa [P] using hp
  have hPK : P = K + 2 := by
    dsimp only [K]
    exact (Nat.sub_add_cancel hP).symm
  change 2 * (P *
        (reducedCollisionWeight (m := m) r +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card))) +
        K * reducedCollisionWeight (m := m) r ≤
      2 * (P * 2 ^ m) +
        2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2)
  change P *
        (3 * reducedCollisionWeight (m := m) r +
          2 * 2 ^ (m - r.val.1.card) +
          2 * 2 ^ (m - r.val.2.card)) ≤
      2 * (P * 2 ^ m) +
        2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        2 * reducedCollisionWeight (m := m) r at hbound
  rw [hPK] at hbound ⊢
  ring_nf at hbound ⊢
  omega

section CriticalPositiveFace

/-- In the two-positive/two-negative profile, the private anchor-exchange
slice leaves one full root weight beyond the previous hybrid bound, unless a
selected escape target already has a larger negative tail. -/
theorem genuineDominant_two_two_tail_escape_growth_or_privateSlice_hybrid
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 2) (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    (∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card) ∨
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) +
        reducedCollisionWeight (m := n) r ≤
      2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g := by
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
  rcases genuineDominant_two_tail_escape_growth_or_privateSlice_charge
      hqodd g hg r hr hres hBcard with hgrow | hprivate
  · exact Or.inl hgrow
  · obtain ⟨v, u, w, hvtarget, hutarget, hwcanonical, _hwr,
      _hwBcard, _hwimbalance, hcharge, _hsubset⟩ := hprivate
    have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hr
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hrmin : ∀ a ∈ canonicalReducedCollisions (g := g) hh,
        (reducedCollisionSupport r).card ≤
          (reducedCollisionSupport a).card := by
      simpa [hh, criticalCanonicalReducedCollisions,
        reducedCollisionSupport] using hdominant.2.1
    have hA : r.val.1.Nonempty := Finset.card_pos.mp (by omega)
    have hhybrid := anchorExchange_privateSlice_hybrid_bound
      hg hh (half_ne_zero hN hM) r v u w hr' hrmin hA
        hvtarget hutarget hwcanonical hcharge
    have hhybrid' :
        2 ^ r.val.1.card *
            (3 * reducedCollisionWeight (m := n) r +
              2 * 2 ^ (n - r.val.1.card) +
              2 * 2 ^ (n - r.val.2.card)) ≤
          2 * (2 ^ r.val.1.card * 2 ^ n) +
            2 * criticalCanonicalCrossMass g +
            2 * reducedCollisionWeight (m := n) r := by
      simpa [hh, criticalCanonicalCrossMass,
        criticalCanonicalPositiveNegativeCrossPairs] using hhybrid
    right
    rw [hAcard, hBcard] at hhybrid' ⊢
    norm_num at hhybrid' ⊢
    ring_nf at hhybrid' ⊢
    omega

/-- Combining the surviving quarter-layer with the strict small-crossing
complement gives the strengthened critical sandwich for the `(2,2)` tail
profile. -/
theorem genuineDominant_two_two_tail_escape_growth_or_privateSlice_sandwich
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 2) (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    (∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card) ∨
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) +
        reducedCollisionWeight (m := n) r) <
      4 * (2 ^ r.val.1.card * 2 ^ n) +
        criticalHalfGap n s * criticalHalfGap n s := by
  rcases genuineDominant_two_two_tail_escape_growth_or_privateSlice_hybrid
      hqodd g hg r hr hres hAcard hBcard with hgrow | hbound
  · exact Or.inl hgrow
  · right
    have hsmall := hres.1.2
    omega

end CriticalPositiveFace

end MinModulus
