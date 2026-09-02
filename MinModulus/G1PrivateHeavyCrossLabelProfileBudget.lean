/-
# One-budget aggregation across incoming labels

The fixed-label weighted charge cannot simply be summed over all labels: one
profile pair may share several omissions.  In the surviving branch, however,
the global three-distinct-omissions alternative is absent, so every witness
has at most two omissions.  Hence an ordered profile pair occurs under at most
two common labels.

We aggregate through raw reduced collisions.  Tail-light coefficient profiles
map injectively to raw collisions, avoiding the sign ambiguity of canonical
orientation.  The full raw collision off-diagonal is controlled by four times
the canonical square, and therefore by canonical crossing mass plus the
existing diagonal concentration term.  This yields a single global budget
with universal constants, independent of the number of cycle labels.
-/
import MinModulus.G1PrivateHeavyWeightedProfileCrossing

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A bounded-fiber map transports a weight depending only on the image with
the same multiplicity bound. -/
theorem sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (w : β → ℕ)
    (hf : ∀ x ∈ S, f x ∈ T) (K : ℕ)
    (hfiber : ∀ y ∈ T, (S.filter fun x ↦ f x = y).card ≤ K) :
    S.sum (fun x ↦ w (f x)) ≤ K * T.sum w := by
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun x ↦ w (f x))]
  calc
    (∑ y ∈ T, ∑ x ∈ S with f x = y, w (f x)) ≤
        ∑ y ∈ T, K * w y := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        (∑ x ∈ S with f x = y, w (f x)) =
            (S.filter fun x ↦ f x = y).card * w y := by
          rw [Finset.sum_const_nat]
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ ≤ K * w y := Nat.mul_le_mul_right _ (hfiber y hy)
    _ = K * T.sum w := by
      rw [Finset.mul_sum]

/-- Distinct complete tail-light incoming avoiding profiles on the whole
cycle, without first choosing an omission label. -/
noncomputable def minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) : Finset (Fin (m + 1) → ℤ) := by
  classical
  exact (Finset.univ.filter fun i : Fin d ↦
    ∀ k : Fin m,
      minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i k.succ ≤ 1).image
    (minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : Fin (m + 1) → ℤ) :
    r ∈ minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d ↔
      ∃ i : Fin d,
        (∀ k : Fin m,
          minimalSupportPrivateShiftCycleIncomingAvoidingWitness
            g hno hmin a i k.succ ≤ 1) ∧
        minimalSupportPrivateShiftCycleIncomingAvoidingWitness
          g hno hmin a i = r := by
  classical
  simp [minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles]

omit [DecidableEq G] in
theorem incomingAvoidingLightProfile_isWitness
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) : Witness g h r.val := by
  obtain ⟨i, _hiLight, hir⟩ :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles_iff
      g hno hmin a d r.val).mp r.property
  rw [← hir]
  exact minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
    g hno hmin a i

omit [DecidableEq G] in
theorem incomingAvoidingLightProfile_tailLight
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) : ∀ k : Fin m, r.val k.succ ≤ 1 := by
  obtain ⟨_i, hiLight, hir⟩ :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles_iff
      g hno hmin a d r.val).mp r.property
  intro k
  rw [← hir]
  exact hiLight k

/-- Raw reduced collision attached to one global incoming light profile. -/
noncomputable def incomingAvoidingLightProfileRawCollision
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) : ReducedSubsetSumCollision g h :=
  reducedCollisionOfTailLightWitness g
    (incomingAvoidingLightProfile_isWitness g hno hmin a d r)
    (incomingAvoidingLightProfile_tailLight g hno hmin a d r)

omit [DecidableEq G] in
/-- Reduction is globally injective on complete tail-light incoming profiles;
no common omission is needed before canonical orientation. -/
theorem incomingAvoidingLightProfileRawCollision_injective
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    Function.Injective
      (incomingAvoidingLightProfileRawCollision
        g hno hmin a d) := by
  intro r u hru
  apply Subtype.ext
  calc
    r.val = subsetCollisionCoeffs
        (incomingAvoidingLightProfileRawCollision
          g hno hmin a d r).val.1
        (incomingAvoidingLightProfileRawCollision
          g hno hmin a d r).val.2 := by
      symm
      exact reducedCollisionOfTailLightWitness_coeffs g
        (incomingAvoidingLightProfile_isWitness g hno hmin a d r)
        (incomingAvoidingLightProfile_tailLight g hno hmin a d r)
    _ = subsetCollisionCoeffs
        (incomingAvoidingLightProfileRawCollision
          g hno hmin a d u).val.1
        (incomingAvoidingLightProfileRawCollision
          g hno hmin a d u).val.2 := by rw [hru]
    _ = u.val := reducedCollisionOfTailLightWitness_coeffs g
      (incomingAvoidingLightProfile_isWitness g hno hmin a d u)
      (incomingAvoidingLightProfile_tailLight g hno hmin a d u)

omit [DecidableEq G] in
/-- In the complement of the global three-omission frontier, every witness
has at most two omission coordinates. -/
theorem card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
    (g : Fin (m + 1) → G) {h : G}
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (c : Fin (m + 1) → ℤ) (hc : Witness g h c) :
    (witnessOmissionCoordinates c).card ≤ 2 := by
  by_contra hnot
  have hcard : 3 ≤ (witnessOmissionCoordinates c).card := by omega
  have hnonempty : (witnessOmissionCoordinates c).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hnonempty
  have herase := Finset.card_erase_add_one hx
  have htwo : 1 < ((witnessOmissionCoordinates c).erase x).card := by
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp htwo
  have hy' := Finset.mem_of_mem_erase hy
  have hz' := Finset.mem_of_mem_erase hz
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
  apply hthree
  exact ⟨c, x, y, z, hc, hyx.symm, hzx.symm, hyz,
    (witnessOmissionCoordinates_exact c x).2 hx,
    (witnessOmissionCoordinates_exact c y).2 hy',
    (witnessOmissionCoordinates_exact c z).2 hz'⟩

/-- Ordered pairs of distinct global incoming light profiles together with a
coordinate omitted by both profiles. -/
noncomputable def incomingAvoidingLightProfileCommonOmissionPairIncidences
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    Finset (Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) := by
  classical
  let P := minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    g hno hmin a d
  exact ((Finset.univ : Finset (Fin (m + 1))).product P.attach.offDiag).filter
    fun t ↦ t.2.1.val t.1 = -1 ∧ t.2.2.val t.1 = -1

omit [DecidableEq G] in
@[simp] theorem mem_incomingAvoidingLightProfileCommonOmissionPairIncidences_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (t : Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) :
    t ∈ incomingAvoidingLightProfileCommonOmissionPairIncidences
        g hno hmin a d ↔
      t.2.1 ≠ t.2.2 ∧ t.2.1.val t.1 = -1 ∧
        t.2.2.val t.1 = -1 := by
  classical
  simp [incomingAvoidingLightProfileCommonOmissionPairIncidences]

/-- The raw collision pair underlying one common-omission profile-pair
incidence. -/
noncomputable def incomingAvoidingLightProfileIncidenceRawPair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (t : Fin (m + 1) ×
      (↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d))) :
    ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h :=
  (incomingAvoidingLightProfileRawCollision
      g hno hmin a d t.2.1,
    incomingAvoidingLightProfileRawCollision
      g hno hmin a d t.2.2)

/-- Fiber of common-omission incidences over one raw collision pair. -/
noncomputable def incomingAvoidingLightProfileIncidenceRawPairFiber
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact (incomingAvoidingLightProfileCommonOmissionPairIncidences
    g hno hmin a d).filter fun t ↦
      incomingAvoidingLightProfileIncidenceRawPair
        g hno hmin a d t = p

omit [DecidableEq G] in
/-- Once three-omission witnesses have been split off, at most two common
omission labels map a fixed ordered profile pair to the same raw collision
pair. -/
theorem card_commonOmissionPairIncidence_rawPairFiber_le_two
    (g : Fin (m + 1) → G) {h : G}
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) :
    (incomingAvoidingLightProfileIncidenceRawPairFiber
      g hno hmin a d p).card ≤ 2 := by
  classical
  let P := minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    g hno hmin a d
  let J := incomingAvoidingLightProfileCommonOmissionPairIncidences
    g hno hmin a d
  let raw := incomingAvoidingLightProfileRawCollision
    g hno hmin a d
  let pair : Fin (m + 1) × (↥P × ↥P) →
      ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h :=
    fun t ↦ (raw t.2.1, raw t.2.2)
  let F := incomingAvoidingLightProfileIncidenceRawPairFiber
    g hno hmin a d p
  by_cases hF : F.Nonempty
  · obtain ⟨t0, ht0F⟩ := hF
    have ht0 := (Finset.mem_filter.mp ht0F).1
    have ht0Pair := (Finset.mem_filter.mp ht0F).2
    let cp := subsetCollisionCoeffs p.1.val.1 p.1.val.2
    let O := witnessOmissionCoordinates cp
    have hcp : cp = t0.2.1.val := by
      have hfirst := congrArg Prod.fst ht0Pair
      change raw t0.2.1 = p.1 at hfirst
      calc
        cp = subsetCollisionCoeffs (raw t0.2.1).val.1
            (raw t0.2.1).val.2 := by
          dsimp [cp]
          rw [← hfirst]
        _ = t0.2.1.val := reducedCollisionOfTailLightWitness_coeffs g
          (incomingAvoidingLightProfile_isWitness
            g hno hmin a d t0.2.1)
          (incomingAvoidingLightProfile_tailLight
            g hno hmin a d t0.2.1)
    have hOWitness : Witness g h cp := by
      rw [hcp]
      exact incomingAvoidingLightProfile_isWitness
        g hno hmin a d t0.2.1
    have hOcard : O.card ≤ 2 := by
      exact card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
        g hthree cp hOWitness
    have hlabelInj : Set.InjOn
        (fun t : Fin (m + 1) × (↥P × ↥P) ↦ t.1)
        (↑F : Set (Fin (m + 1) × (↥P × ↥P))) := by
      intro t ht u hu hlabel
      apply Prod.ext
      · exact hlabel
      · apply Prod.ext
        · apply incomingAvoidingLightProfileRawCollision_injective
            g hno hmin a d
          have htPair := (Finset.mem_filter.mp ht).2
          have huPair := (Finset.mem_filter.mp hu).2
          exact congrArg Prod.fst (htPair.trans huPair.symm)
        · apply incomingAvoidingLightProfileRawCollision_injective
            g hno hmin a d
          have htPair := (Finset.mem_filter.mp ht).2
          have huPair := (Finset.mem_filter.mp hu).2
          exact congrArg Prod.snd (htPair.trans huPair.symm)
    have hlabelsSubset : F.image
        (fun t : Fin (m + 1) × (↥P × ↥P) ↦ t.1) ⊆ O := by
      intro z hz
      obtain ⟨t, htF, rfl⟩ := Finset.mem_image.mp hz
      have htJ := (Finset.mem_filter.mp htF).1
      have htPair := (Finset.mem_filter.mp htF).2
      have htInc :=
        (mem_incomingAvoidingLightProfileCommonOmissionPairIncidences_iff
          g hno hmin a d t).mp htJ
      have htFirst := congrArg Prod.fst htPair
      change raw t.2.1 = p.1 at htFirst
      apply (witnessOmissionCoordinates_exact cp t.1).1
      calc
        cp t.1 = subsetCollisionCoeffs (raw t.2.1).val.1
            (raw t.2.1).val.2 t.1 := by
          dsimp [cp]
          rw [← htFirst]
        _ = t.2.1.val t.1 := congrFun
          (reducedCollisionOfTailLightWitness_coeffs g
            (incomingAvoidingLightProfile_isWitness
              g hno hmin a d t.2.1)
            (incomingAvoidingLightProfile_tailLight
              g hno hmin a d t.2.1)) t.1
        _ = -1 := htInc.2.1
    have himageCard : (F.image
        (fun t : Fin (m + 1) × (↥P × ↥P) ↦ t.1)).card = F.card :=
      Finset.card_image_of_injOn hlabelInj
    change F.card ≤ 2
    rw [← himageCard]
    exact (Finset.card_le_card hlabelsSubset).trans hOcard
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 2
    simp [hFempty]

/-- The weighted raw collision off-diagonal is controlled by canonical
crossing mass and the canonical diagonal concentration term. -/
theorem sum_allRawCollisionOffDiagWeights_le_cross_and_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0) :
    (Finset.univ.offDiag : Finset
        (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h)).sum
        (fun p ↦ reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) ≤
      8 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      4 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  classical
  let R := (Finset.univ : Finset (ReducedSubsetSumCollision g h))
  let C := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    weight p.1 * weight p.2
  let X := (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
  let D := C.sum fun r ↦ weight r * weight r
  have hoffSubset : R.offDiag ⊆ R ×ˢ R := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    exact Finset.mem_product.mpr ⟨hp'.1, hp'.2.1⟩
  have hproduct : (R ×ˢ R).sum pairWeight = R.sum weight * R.sum weight := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have htotal : R.sum weight = 2 * C.sum weight := by
    simpa [R, C, weight] using
      sum_reducedCollisionWeight_eq_two_mul_canonical
        (g := g) hh hh0
  have hcanonical : C.sum weight * C.sum weight ≤ 2 * X + D := by
    simpa [C, X, D, weight, pairWeight] using
      square_sum_canonicalWeights_le_two_crossMass_add_diagonal
        g hg hh hh0
  change R.offDiag.sum pairWeight ≤ 8 * X + 4 * D
  calc
    R.offDiag.sum pairWeight ≤ (R ×ˢ R).sum pairWeight :=
      Finset.sum_le_sum_of_subset hoffSubset
    _ = R.sum weight * R.sum weight := hproduct
    _ = 4 * (C.sum weight * C.sum weight) := by rw [htotal]; ring
    _ ≤ 4 * (2 * X + D) := Nat.mul_le_mul_left 4 hcanonical
    _ = 8 * X + 4 * D := by ring

/-- One global weighted budget for all labels simultaneously.  The factor two
is exactly the maximum number of omissions of either profile after the
three-omission frontier has been removed. -/
theorem sum_commonOmissionProfilePairRawWeights_le_cross_and_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    (incomingAvoidingLightProfileCommonOmissionPairIncidences
        g hno hmin a d).sum (fun t ↦
      reducedCollisionWeight (m := m)
          (incomingAvoidingLightProfileIncidenceRawPair
            g hno hmin a d t).1 *
        reducedCollisionWeight (m := m)
          (incomingAvoidingLightProfileIncidenceRawPair
            g hno hmin a d t).2) ≤
      16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      8 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  classical
  let J := incomingAvoidingLightProfileCommonOmissionPairIncidences
    g hno hmin a d
  let rawPair := incomingAvoidingLightProfileIncidenceRawPair
    g hno hmin a d
  let R := (Finset.univ : Finset (ReducedSubsetSumCollision g h))
  let T := R.offDiag
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  let X := (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
  let D := (canonicalReducedCollisions (g := g) hh).sum fun r ↦
    reducedCollisionWeight (m := m) r *
      reducedCollisionWeight (m := m) r
  have hmaps : ∀ t ∈ J, rawPair t ∈ T := by
    intro t ht
    apply Finset.mem_offDiag.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    have htInc :=
      (mem_incomingAvoidingLightProfileCommonOmissionPairIncidences_iff
        g hno hmin a d t).mp ht
    exact (incomingAvoidingLightProfileRawCollision_injective
      g hno hmin a d).ne htInc.1
  have hfiber : ∀ p ∈ T,
      (J.filter fun t ↦ rawPair t = p).card ≤ 2 := by
    intro p _hp
    simpa [J, rawPair,
      incomingAvoidingLightProfileIncidenceRawPairFiber] using
      card_commonOmissionPairIncidence_rawPairFiber_le_two
        g hthree hno hmin a d p
  have hmapBound : J.sum (fun t ↦ pairWeight (rawPair t)) ≤
      2 * T.sum pairWeight :=
    sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
      J T rawPair pairWeight hmaps 2 hfiber
  have hrawBound : T.sum pairWeight ≤ 8 * X + 4 * D := by
    simpa [T, R, X, D, pairWeight] using
      sum_allRawCollisionOffDiagWeights_le_cross_and_diagonal
        g hg hh hh0
  change J.sum (fun t ↦ pairWeight (rawPair t)) ≤ 16 * X + 8 * D
  calc
    J.sum (fun t ↦ pairWeight (rawPair t)) ≤ 2 * T.sum pairWeight :=
      hmapBound
    _ ≤ 2 * (8 * X + 4 * D) := Nat.mul_le_mul_left 2 hrawBound
    _ = 16 * X + 8 * D := by ring

/-- Source-zero profile multiplicities inherit the same one-budget
cross-label charge. -/
theorem sum_commonOmissionProfilePairFiberPowers_le_cross_and_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (incomingAvoidingLightProfileCommonOmissionPairIncidences
        g hno hmin a d).sum (fun t ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.1.val).card - 1) *
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d t.2.2.val).card - 1)) ≤
      16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      8 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  classical
  let J := incomingAvoidingLightProfileCommonOmissionPairIncidences
    g hno hmin a d
  let raw := incomingAvoidingLightProfileRawCollision
    g hno hmin a d
  let rawPair := incomingAvoidingLightProfileIncidenceRawPair
    g hno hmin a d
  let fiberWeight : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d) → ℕ := fun r ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r.val).card - 1)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hweight : ∀ r, fiberWeight r ≤
      reducedCollisionWeight (m := m) (raw r) := by
    intro r
    have hpow :=
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle r.val
          (incomingAvoidingLightProfile_isWitness g hno hmin a d r)
          (incomingAvoidingLightProfile_tailLight g hno hmin a d r)
    calc
      fiberWeight r ≤ reducedCollisionWeight (m := m)
          (canonicalizeReducedCollision hh (raw r)) := by
        simpa only [fiberWeight, raw, canonicalCollisionOfTailLightWitness,
          incomingAvoidingLightProfileRawCollision] using hpow
      _ = reducedCollisionWeight (m := m) (raw r) :=
        canonicalizeReducedCollision_weight hh (raw r)
  have hcharged :=
    sum_commonOmissionProfilePairRawWeights_le_cross_and_diagonal
      g hg hh hh0 hthree hno hmin a d
  change J.sum (fun t ↦ fiberWeight t.2.1 * fiberWeight t.2.2) ≤ _
  calc
    J.sum (fun t ↦ fiberWeight t.2.1 * fiberWeight t.2.2) ≤
        J.sum (fun t ↦ pairWeight (rawPair t)) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact Nat.mul_le_mul (hweight t.2.1) (hweight t.2.2)
    _ ≤ 16 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
          (fun p ↦ reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        8 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r) := by
      simpa [J, rawPair, pairWeight] using hcharged

end MinModulus
