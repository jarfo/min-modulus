/-
# Three private half-slices from the anchor exchange

In the exact two-singleton fan, the first selected target uniquely allows one
root-tail coordinate, the second uniquely allows the other, and the
anchor-exchange target uniquely allows the retained root-positive coordinate.
The three corresponding containing-coordinate half-cubes are pairwise
disjoint and disjoint from the root cube.  Together they occupy five halves
of one dominant padding layer.
-/
import MinModulus.G1AnchorExchangeSignature
import MinModulus.G1SignatureSubcubeCoverage

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A light exact triangle whose third edge is a canonical collision produces
an anchor-exchange collision.  The new negative tail contains the two old
edge endpoints, while the light vertex lies in the old positive tail and is
absent from the new support. -/
theorem exists_canonical_anchorExchange_of_light_triangle
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    {cAB cBD : Fin (m + 1) → ℤ}
    (hcAB : Witness g h cAB) (hcBD : Witness g h cBD)
    (a b d : Fin m) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a.succ ∨ i = b.succ)
    (hBD : ∀ i, cBD i = -1 ↔ i = b.succ ∨ i = d.succ)
    (hDA : ∀ i, subsetCollisionCoeffs r.val.1 r.val.2 i = -1 ↔
      i = d.succ ∨ i = a.succ)
    (hDAb : subsetCollisionCoeffs r.val.1 r.val.2 b.succ = 1)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h) :
    ∃ w : ReducedSubsetSumCollision g h,
      w ∈ canonicalReducedCollisions (g := g) hh ∧
      3 ≤ w.val.2.card ∧ 2 ≤ reducedCollisionImbalance w ∧
      a ∈ w.val.2 ∧ d ∈ w.val.2 ∧
      b ∈ r.val.1 ∧ b ∉ reducedCollisionSupport w := by
  classical
  have hrcard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp hr)
  have hcDA : Witness g h (subsetCollisionCoeffs r.val.1 r.val.2) :=
    witness_of_subsetSum_eq_add g hh0 hrcard r.property.2
  have hdetail :=
    common_touched_or_exists_three_omissions_of_light_triangle
      g hg hh hcAB hcBD hcDA a.succ b.succ d.succ
        ((Fin.succ_injective _).ne hab)
        ((Fin.succ_injective _).ne hbd)
        ((Fin.succ_injective _).ne hda)
        hAB hBD hDA hDAb
  rcases hdetail with htouch | ⟨x, c, hxd, hxa, _hxb, _hrx,
      hc, hcb, hca, hcd, hcx⟩
  · exact False.elim (hno ⟨b.succ, htouch⟩)
  · obtain ⟨e, hce⟩ :=
      exists_coeff_ge_two_of_omit_other_and_zero_at_exact_pair
        g hg hh hcAB hc a.succ b.succ hAB hca hcb
    have he0 : e = 0 := by
      cases e using Fin.cases with
      | zero => rfl
      | succ y =>
          have hle := hallLight c hc y
          omega
    subst e
    have hceil : ∀ y : Fin m, c y.succ ≤ 1 := hallLight c hc
    obtain ⟨w, hwcanonical, hwcoeff, hwimbalance, hwcard⟩ :=
      exists_canonicalReducedCollision_of_anchorHeavy_three_omissions
        g hh hc hceil a.succ d.succ x
          ((Fin.succ_injective _).ne (Ne.symm hda))
          (Ne.symm hxd) hxa hca hcd hcx hce
    have haW : a ∈ w.val.2 := by
      have hacoeff : subsetCollisionCoeffs w.val.1 w.val.2 a.succ = -1 := by
        rw [hwcoeff]
        exact hca
      exact (Finset.mem_sdiff.mp
        ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
          w.val.1 w.val.2 a).mp hacoeff)).1
    have hdW : d ∈ w.val.2 := by
      have hdcoeff : subsetCollisionCoeffs w.val.1 w.val.2 d.succ = -1 := by
        rw [hwcoeff]
        exact hcd
      exact (Finset.mem_sdiff.mp
        ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
          w.val.1 w.val.2 d).mp hdcoeff)).1
    have hbA : b ∈ r.val.1 := by
      by_contra hbA
      have hbB : b ∉ r.val.2 := by
        intro hbB
        have : subsetCollisionCoeffs r.val.1 r.val.2 b.succ = -1 := by
          simp [subsetCollisionCoeffs, hbA, hbB]
        omega
      have : subsetCollisionCoeffs r.val.1 r.val.2 b.succ = 0 := by
        simp [subsetCollisionCoeffs, hbA, hbB]
      omega
    have hwzero : subsetCollisionCoeffs w.val.1 w.val.2 b.succ = 0 := by
      rw [hwcoeff]
      exact hcb
    have hbW : b ∉ reducedCollisionSupport w := by
      intro hbW
      rcases Finset.mem_union.mp hbW with hbWA | hbWB
      · have hbnotB : b ∉ w.val.2 := by
          intro hbWB
          exact Finset.disjoint_left.mp w.property.1 hbWA hbWB
        have hwone : subsetCollisionCoeffs w.val.1 w.val.2 b.succ = 1 := by
          simp [subsetCollisionCoeffs, hbWA, hbnotB]
        omega
      · have hbnotA : b ∉ w.val.1 := by
          intro hbWA
          exact Finset.disjoint_left.mp w.property.1 hbWA hbWB
        have hwneg : subsetCollisionCoeffs w.val.1 w.val.2 b.succ = -1 := by
          simp [subsetCollisionCoeffs, hbnotA, hbWB]
        omega
    exact ⟨w, hwcanonical, hwcard, hwimbalance,
      haW, hdW, hbA, hbW⟩

/-- Three equal-codimension signatures with three respective private allowed
coordinates contribute three disjoint half-cubes beyond the root cube. -/
theorem five_mul_root_le_two_mul_root_three_private_signature_union
    (R C D E : Finset (Fin m)) (j k l : Fin m)
    (hCR : C.card = R.card) (hDR : D.card = R.card)
    (hER : E.card = R.card)
    (hjR : j ∈ R) (hjC : j ∉ C) (hjD : j ∈ D) (hjE : j ∈ E)
    (hkR : k ∈ R) (hkC : k ∈ C) (hkD : k ∉ D) (hkE : k ∈ E)
    (hlR : l ∈ R) (hlC : l ∈ C) (hlD : l ∈ D) (hlE : l ∉ E) :
    5 * (blockedSignatureSubsetLayer R).card ≤
      2 * (rootAndBlockedSignatureSubsetUnion R {C, D, E}).card := by
  classical
  let HC := blockedSignatureContainingSubsetLayer C j
  let HD := blockedSignatureContainingSubsetLayer D k
  let HE := blockedSignatureContainingSubsetLayer E l
  let K := ((blockedSignatureSubsetLayer R ∪ HC) ∪ HD) ∪ HE
  have _hjk : j ≠ k := by
    intro hjk
    subst k
    exact hjC hkC
  have _hjl : j ≠ l := by
    intro hjl
    subst l
    exact hjC hlC
  have _hkl : k ≠ l := by
    intro hkl
    subst l
    exact hkD hlD
  have hRootC : Disjoint (blockedSignatureSubsetLayer R) HC :=
    (blockedSignatureContainingSubsetLayer_disjoint C R j hjR).symm
  have hRootD : Disjoint (blockedSignatureSubsetLayer R) HD :=
    (blockedSignatureContainingSubsetLayer_disjoint D R k hkR).symm
  have hRootE : Disjoint (blockedSignatureSubsetLayer R) HE :=
    (blockedSignatureContainingSubsetLayer_disjoint E R l hlR).symm
  have hCD : Disjoint HC HD :=
    (blockedSignatureContainingSubsetLayer_disjoint C D j hjD).mono_right
      (blockedSignatureContainingSubsetLayer_subset D k)
  have hCE : Disjoint HC HE :=
    (blockedSignatureContainingSubsetLayer_disjoint C E j hjE).mono_right
      (blockedSignatureContainingSubsetLayer_subset E l)
  have hDE : Disjoint HD HE :=
    (blockedSignatureContainingSubsetLayer_disjoint D E k hkE).mono_right
      (blockedSignatureContainingSubsetLayer_subset E l)
  have hRootC_D : Disjoint (blockedSignatureSubsetLayer R ∪ HC) HD := by
    exact Finset.disjoint_union_left.mpr ⟨hRootD, hCD⟩
  have hRootCD_E :
      Disjoint ((blockedSignatureSubsetLayer R ∪ HC) ∪ HD) HE := by
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hRootE, hCE⟩, hDE⟩
  have hp : 0 < m - R.card := by
    have hjAllowed : j ∈ (Finset.univ : Finset (Fin m)) \ C := by simp [hjC]
    have hpos : 0 < ((Finset.univ : Finset (Fin m)) \ C).card :=
      Finset.card_pos.mpr ⟨j, hjAllowed⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C),
      Finset.card_univ, hCR] at hpos
    simpa using hpos
  have hhalfC : 2 * HC.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HC.card = 2 ^ (m - C.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer C j hjC,
      hCR]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hhalfD : 2 * HD.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HD.card = 2 ^ (m - D.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer D k hkD,
      hDR]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hhalfE : 2 * HE.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HE.card = 2 ^ (m - E.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer E l hlE,
      hER]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hKcard : 2 * K.card =
      5 * (blockedSignatureSubsetLayer R).card := by
    have hcard : K.card = (blockedSignatureSubsetLayer R).card +
        HC.card + HD.card + HE.card := by
      dsimp only [K]
      rw [Finset.card_union_of_disjoint hRootCD_E,
        Finset.card_union_of_disjoint hRootC_D,
        Finset.card_union_of_disjoint hRootC]
    omega
  have hKsubset : K ⊆
      rootAndBlockedSignatureSubsetUnion R {C, D, E} := by
    intro U hU
    rcases Finset.mem_union.mp hU with hURCD | hUHE
    · rcases Finset.mem_union.mp hURCD with hURC | hUHD
      · rcases Finset.mem_union.mp hURC with hUR | hUHC
        · exact Finset.mem_union_left _ hUR
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨C, by simp,
              blockedSignatureContainingSubsetLayer_subset C j hUHC⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨D, by simp,
            blockedSignatureContainingSubsetLayer_subset D k hUHD⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨E, by simp,
          blockedSignatureContainingSubsetLayer_subset E l hUHE⟩)
  rw [← hKcard]
  exact Nat.mul_le_mul_left 2 (Finset.card_mono hKsubset)

section CriticalPrivateSlices

/-- Value image of the root signature cube together with the two selected
target signatures and one anchor-exchange signature. -/
noncomputable def rootThreeBlockedSignatureValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r v u w : ReducedSubsetSumCollision g h) : Finset G :=
  (rootAndBlockedSignatureSubsetUnion (reducedCollisionSupport r)
    {restoredCollisionBlockedSupport r v,
      restoredCollisionBlockedSupport r u,
      restoredCollisionBlockedSupport r w}).image (ssum g)

/-- The same three-signature union with the opposite source-tail upper face
adjoined. -/
noncomputable def rootThreeBlockedSignatureValueUnionWithUpper
    {g : Fin (m + 1) → G} {h : G}
    (r v u w : ReducedSubsetSumCollision g h) : Finset G :=
  (rootAndBlockedSignatureSubsetUnionWithUpper r.val.2
    (reducedCollisionSupport r)
    {restoredCollisionBlockedSupport r v,
      restoredCollisionBlockedSupport r u,
      restoredCollisionBlockedSupport r w}).image (ssum g)

/-- The exact two-singleton fan either already has selected target-tail
growth, or its three private signatures occupy at least five halves of the
dominant padding weight inside the anchored subset-sum cube. -/
theorem genuineDominant_two_tail_escape_growth_or_privateSlice_charge
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
    (∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card) ∨
    ∃ v u w : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧
      u ∈ canonicalSupportEscapeTargets hh r ∧
      w ∈ canonicalReducedCollisions (g := g) hh ∧ w ≠ r ∧
      3 ≤ w.val.2.card ∧ 2 ≤ reducedCollisionImbalance w ∧
      5 * reducedCollisionWeight (m := n) r ≤
        2 * (rootThreeBlockedSignatureValueUnion r v u w).card ∧
      rootThreeBlockedSignatureValueUnion r v u w ⊆ subsetSumRange g := by
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
  obtain ⟨j, k, v, u, z, hjk, hrB, hvtarget, hutarget, _hvu,
      hjvAvoid, hkuAvoid, hkv, hju, hzv, hzu, hzr, hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases hshape with hexact | hvgrow | hugrow
  · have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hr
    rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨jv, hjvInc⟩
    rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨ju, hjuInc⟩
    have hvcanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjvInc).2.1
    have hucanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjuInc).2.1
    have hzj : z ≠ j := by
      intro hzj
      subst z
      exact hzr (by rw [hrB]; simp)
    have hzk : z ≠ k := by
      intro hzk
      subst z
      exact hzr (by rw [hrB]; simp)
    have hvjzero : subsetCollisionCoeffs v.val.1 v.val.2 j.succ = 0 := by
      have hjA : j ∉ v.val.1 := fun hjA ↦
        hjvAvoid (Finset.mem_union_left _ hjA)
      have hjB : j ∉ v.val.2 := fun hjB ↦
        hjvAvoid (Finset.mem_union_right _ hjB)
      simp [subsetCollisionCoeffs, hjA, hjB]
    have hukzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0 := by
      have hkA : k ∉ u.val.1 := fun hkA ↦
        hkuAvoid (Finset.mem_union_left _ hkA)
      have hkB : k ∉ u.val.2 := fun hkB ↦
        hkuAvoid (Finset.mem_union_right _ hkB)
      simp [subsetCollisionCoeffs, hkA, hkB]
    have hrzNe : subsetCollisionCoeffs r.val.1 r.val.2 z.succ ≠ 0 := by
      intro hrzero
      exact canonical_exactTriangle_two_zero_not_allZero_zmod
        hN hM g hg r v u hrcanonical hvcanonical hucanonical
          hjk hzj hzk hrB hexact.1
          (by simpa [pair_comm] using hexact.2)
          hrzero hvjzero hukzero
    have hrzNotNeg :
        subsetCollisionCoeffs r.val.1 r.val.2 z.succ ≠ -1 := by
      intro hrneg
      have hzB := (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 z).mp hrneg
      exact hzr (Finset.mem_sdiff.mp hzB).1
    have hrzone : subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 1 := by
      have hb := subsetCollisionCoeffs_tail_bounds r.val.1 r.val.2 z
      omega
    let cv := subsetCollisionCoeffs v.val.1 v.val.2
    let cu := subsetCollisionCoeffs u.val.1 u.val.2
    have hvcard := canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
    have hucard := canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hucanonical)
    have hcv : Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) cv :=
      witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
        hvcard v.property.2
    have hcu : Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) cu :=
      witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
        hucard u.property.2
    have hV := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) v hvcanonical hexact.1
    have hU := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) u hucanonical
        (by simpa [pair_comm] using hexact.2)
    have hR := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) r hrcanonical hrB
    have hallLight : AllHalfWitnessesTailLight g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
      intro c hc y
      by_contra hy
      have hy2 : 2 ≤ c y.succ := by omega
      exact hres.2.2 ⟨c, hc, y, hy2⟩
    have hno : ¬∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
          c e ≠ 0 := by
      simpa [CriticalCommonTouched] using hres.2.1
    obtain ⟨w, hwcanonical, hwBcard, hwimbalance,
        hkw, hjw, hzrA, hzw⟩ :=
      exists_canonical_anchorExchange_of_light_triangle
        g hg (half_add_half hN) (half_ne_zero hN hM) r hrcanonical
          hcv hcu k z j (Ne.symm hzk) hzj hjk
          (by simpa [cv] using hV)
          (by
            intro i
            simpa [cu, or_comm] using hU i)
          (by simpa using hR)
          hrzone hno hallLight
    have hwr : w ≠ r := by
      intro hwr
      subst w
      exact hzw (Finset.mem_union_left _ hzrA)
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hrmin : ∀ a ∈ canonicalReducedCollisions (g := g) hh,
        (reducedCollisionSupport r).card ≤
          (reducedCollisionSupport a).card := by
      simpa [hh, criticalCanonicalReducedCollisions,
        reducedCollisionSupport] using hdominant.2.1
    have hvmin := hrmin v hvcanonical
    have humin := hrmin u hucanonical
    have hwmin := hrmin w hwcanonical
    let R := reducedCollisionSupport r
    let C := restoredCollisionBlockedSupport r v
    let D := restoredCollisionBlockedSupport r u
    let E := restoredCollisionBlockedSupport r w
    have hCR : C.card = R.card := by
      simpa [C, R] using card_restoredCollisionBlockedSupport r v hvmin
    have hDR : D.card = R.card := by
      simpa [D, R] using card_restoredCollisionBlockedSupport r u humin
    have hER : E.card = R.card := by
      simpa [E, R] using card_restoredCollisionBlockedSupport r w hwmin
    have hjR : j ∈ R := by
      exact Finset.mem_union_right _ (by rw [hrB]; simp)
    have hkR : k ∈ R := by
      exact Finset.mem_union_right _ (by rw [hrB]; simp)
    have hzR : z ∈ R := Finset.mem_union_left _ hzrA
    have hjC : j ∉ C := by
      intro hjC'
      exact hjvAvoid
        ((mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r v hvmin hjR).mp hjC')
    have hkC : k ∈ C :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r v hvmin hkR).mpr (Finset.mem_union_right _ hkv)
    have hzC : z ∈ C :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r v hvmin hzR).mpr (Finset.mem_union_right _ hzv)
    have hjD : j ∈ D :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r u humin hjR).mpr (Finset.mem_union_right _ hju)
    have hkD : k ∉ D := by
      intro hkD'
      exact hkuAvoid
        ((mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r u humin hkR).mp hkD')
    have hzD : z ∈ D :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r u humin hzR).mpr (Finset.mem_union_right _ hzu)
    have hjE : j ∈ E :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r w hwmin hjR).mpr (Finset.mem_union_right _ hjw)
    have hkE : k ∈ E :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r w hwmin hkR).mpr (Finset.mem_union_right _ hkw)
    have hzE : z ∉ E := by
      intro hzE'
      exact hzw
        ((mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r w hwmin hzR).mp hzE')
    have hprivate :=
      five_mul_root_le_two_mul_root_three_private_signature_union
        R C D E j k z hCR hDR hER
          hjR hjC hjD hjE hkR hkC hkD hkE hzR hzC hzD hzE
    have hrootCard : (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := n) r := by
      rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
        card_collisionPaddingSubsetLayer]
    have hvalueCard :
        (rootAndBlockedSignatureSubsetUnion R {C, D, E}).card =
          (rootThreeBlockedSignatureValueUnion r v u w).card := by
      rw [rootThreeBlockedSignatureValueUnion,
        Finset.card_image_of_injective _ (ssum_injective g hg)]
    have hcharge : 5 * reducedCollisionWeight (m := n) r ≤
        2 * (rootThreeBlockedSignatureValueUnion r v u w).card := by
      simpa [hrootCard, hvalueCard, R, C, D, E] using hprivate
    have hsubset : rootThreeBlockedSignatureValueUnion r v u w ⊆
        subsetSumRange g := by
      intro x hx
      rw [rootThreeBlockedSignatureValueUnion] at hx
      rcases Finset.mem_image.mp hx with ⟨U, _hU, rfl⟩
      exact Finset.mem_image.mpr ⟨U, Finset.mem_univ _, rfl⟩
    exact Or.inr ⟨v, u, w, hvtarget, hutarget,
      by simpa [hh] using hwcanonical, hwr, hwBcard, hwimbalance,
      hcharge, hsubset⟩
  · exact Or.inl ⟨v, hvtarget, hvgrow⟩
  · exact Or.inl ⟨u, hutarget, hugrow⟩

/-- The three-private-slice charge remains disjoint from the opposite
source-tail upper face.  In the two-tail profile this adds a full
`2^(n-2)` face to the `5/2`-layer lower bound. -/
theorem genuineDominant_two_tail_escape_growth_or_privateSlice_tailFace_charge
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
    (∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card) ∨
    ∃ v u w : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalSupportEscapeTargets hh r ∧
      u ∈ canonicalSupportEscapeTargets hh r ∧
      w ∈ canonicalReducedCollisions (g := g) hh ∧ w ≠ r ∧
      3 ≤ w.val.2.card ∧ 2 ≤ reducedCollisionImbalance w ∧
      5 * reducedCollisionWeight (m := n) r + 2 * 2 ^ (n - 2) ≤
        2 * (rootThreeBlockedSignatureValueUnionWithUpper r v u w).card ∧
      rootThreeBlockedSignatureValueUnionWithUpper r v u w ⊆
        subsetSumRange g := by
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
  · obtain ⟨v, u, w, hvtarget, hutarget, hwcanonical, hwr,
      hwBcard, hwimbalance, hcharge, _hlowerSubset⟩ := hprivate
    have hrcanonical : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hr
    rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨jv, hjvInc⟩
    rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨ju, hjuInc⟩
    have hvcanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjvInc).2.1
    have hucanonical :=
      (mem_canonicalSupportEscapeIncidences_iff.mp hjuInc).2.1
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hrmin : ∀ a ∈ canonicalReducedCollisions (g := g) hh,
        (reducedCollisionSupport r).card ≤
          (reducedCollisionSupport a).card := by
      simpa [hh, criticalCanonicalReducedCollisions,
        reducedCollisionSupport] using hdominant.2.1
    have hvmin := hrmin v hvcanonical
    have humin := hrmin u hucanonical
    have hwmin := hrmin w hwcanonical
    let R := reducedCollisionSupport r
    let C := restoredCollisionBlockedSupport r v
    let D := restoredCollisionBlockedSupport r u
    let E := restoredCollisionBlockedSupport r w
    have hBnonempty : r.val.2.Nonempty := Finset.card_pos.mp (by omega)
    have hBR : (r.val.2 ∩ R).Nonempty := by
      obtain ⟨x, hx⟩ := hBnonempty
      exact ⟨x, Finset.mem_inter.mpr
        ⟨hx, Finset.mem_union_right _ hx⟩⟩
    have hBC : (r.val.2 ∩ C).Nonempty := by
      obtain ⟨x, hx⟩ := canonicalReducedCollision_negative_tails_inter
        g hg (half_add_half hN) (half_ne_zero hN hM) r v
          (mem_canonicalReducedCollisions_iff.mp hrcanonical)
          (mem_canonicalReducedCollisions_iff.mp hvcanonical)
      have hxr := (Finset.mem_inter.mp hx).1
      have hxv := (Finset.mem_inter.mp hx).2
      refine ⟨x, Finset.mem_inter.mpr ⟨hxr, ?_⟩⟩
      exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r v hvmin (Finset.mem_union_right _ hxr)).mpr
          (Finset.mem_union_right _ hxv)
    have hBD : (r.val.2 ∩ D).Nonempty := by
      obtain ⟨x, hx⟩ := canonicalReducedCollision_negative_tails_inter
        g hg (half_add_half hN) (half_ne_zero hN hM) r u
          (mem_canonicalReducedCollisions_iff.mp hrcanonical)
          (mem_canonicalReducedCollisions_iff.mp hucanonical)
      have hxr := (Finset.mem_inter.mp hx).1
      have hxu := (Finset.mem_inter.mp hx).2
      refine ⟨x, Finset.mem_inter.mpr ⟨hxr, ?_⟩⟩
      exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r u humin (Finset.mem_union_right _ hxr)).mpr
          (Finset.mem_union_right _ hxu)
    have hBE : (r.val.2 ∩ E).Nonempty := by
      obtain ⟨x, hx⟩ := canonicalReducedCollision_negative_tails_inter
        g hg (half_add_half hN) (half_ne_zero hN hM) r w
          (mem_canonicalReducedCollisions_iff.mp hrcanonical)
          (mem_canonicalReducedCollisions_iff.mp hwcanonical)
      have hxr := (Finset.mem_inter.mp hx).1
      have hxw := (Finset.mem_inter.mp hx).2
      refine ⟨x, Finset.mem_inter.mpr ⟨hxr, ?_⟩⟩
      exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r w hwmin (Finset.mem_union_right _ hxr)).mpr
          (Finset.mem_union_right _ hxw)
    have hinter : ∀ A ∈ ({C, D, E} : Finset (Finset (Fin n))),
        (r.val.2 ∩ A).Nonempty := by
      intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl | rfl
      · exact hBC
      · exact hBD
      · exact hBE
    have hupperCard :
        (rootThreeBlockedSignatureValueUnionWithUpper r v u w).card =
          (rootThreeBlockedSignatureValueUnion r v u w).card +
            2 ^ (n - r.val.2.card) := by
      rw [rootThreeBlockedSignatureValueUnionWithUpper,
        rootThreeBlockedSignatureValueUnion,
        Finset.card_image_of_injective _ (ssum_injective g hg),
        Finset.card_image_of_injective _ (ssum_injective g hg),
        card_rootAndBlockedSignatureSubsetUnionWithUpper
          r.val.2 R {C, D, E} hBR hinter,
        card_blockedSignatureSubsetLayer]
    have hupperCharge :
        5 * reducedCollisionWeight (m := n) r + 2 * 2 ^ (n - 2) ≤
          2 * (rootThreeBlockedSignatureValueUnionWithUpper r v u w).card := by
      rw [hupperCard, hBcard]
      omega
    have hupperSubset :
        rootThreeBlockedSignatureValueUnionWithUpper r v u w ⊆
          subsetSumRange g := by
      intro x hx
      rw [rootThreeBlockedSignatureValueUnionWithUpper] at hx
      rcases Finset.mem_image.mp hx with ⟨U, _hU, rfl⟩
      exact Finset.mem_image.mpr ⟨U, Finset.mem_univ _, rfl⟩
    exact Or.inr ⟨v, u, w, hvtarget, hutarget, hwcanonical, hwr,
      hwBcard, hwimbalance, hupperCharge, hupperSubset⟩

end CriticalPrivateSlices

end MinModulus
