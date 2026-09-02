/-
# Comparing an internal-heavy star witness with its private witness

Outside the stronger capacity arm, the star-avoiding witness is heavy at an
internal coordinate `e ∈ B`.  Compare it with the canonical private witness
owned by `e`.  If the two witnesses agree, the entire fixed leaf reservoir
transfers to that private witness.  If they differ, validity supplies a
directed coefficient gap from the avoiding witness to the private witness.

Privacy and the fixed reservoir localize that gap completely: it is the owner,
the star center, a leaf, or a genuinely fresh external coordinate.  The last
case pays the stronger ambient capacity bound.  The other cases respectively
force owner coefficient at least four, external heaviness at the center, or a
positive incidence on a fixed leaf.
-/
import MinModulus.G1PrivateHeavySelfHeavyStarHeavyLocation

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Adding a fresh external coordinate to the center and a fixed external
reservoir pays one further unit of ambient capacity. -/
theorem card_transversal_add_reservoir_add_two_le_of_fresh_external
    (B L : Finset (Fin (m + 1))) (z i : Fin (m + 1))
    (hLC : L ⊆ (Finset.univ \ B).erase z)
    (hzB : z ∉ B) (hiB : i ∉ B) (hiz : i ≠ z) (hiL : i ∉ L) :
    B.card + L.card + 2 ≤ m + 1 := by
  let C := (Finset.univ \ B).erase z
  have hiC : i ∈ C :=
    Finset.mem_erase.mpr ⟨hiz,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩⟩
  have hinsert : insert i L ⊆ C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxL
    · exact hiC
    · exact hLC hxL
  have hcardInsert : (insert i L).card = L.card + 1 := by
    rw [Finset.card_insert_of_notMem hiL]
  have hleC : L.card + 1 ≤ C.card := by
    rw [← hcardInsert]
    exact Finset.card_le_card hinsert
  have hzCompl : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  have hCcard : C.card + 1 = (Finset.univ \ B).card :=
    Finset.card_erase_add_one hzCompl
  have hComplCard : (Finset.univ \ B).card = m + 1 - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp
  have hBcard : B.card ≤ m + 1 := by
    simpa using Finset.card_le_univ B
  dsimp only [C] at hleC hCcard
  omega

/-- The private witness at an internal heavy coordinate of the avoiding star
falls into five explicit structured alternatives. -/
theorem minimalSupportPrivateSelfHeavyStar_internalHeavy_privateComparison
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (hzB : z ∉ B)
    (k : Fin m) (hkB : k.succ ∈ B)
    (hk : 2 ≤ supportAvoidingWitnessAt g hno z k.succ) :
    let owner : ↥B := ⟨k.succ, hkB⟩
    let p := minimalSupportPrivateWitness g h hmin owner
    (2 ≤ p k.succ ∧
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessOmissionCoordinates p).card) ∨
      4 ≤ p k.succ ∨
      2 ≤ p z ∨
      (∃ l ∈ minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz,
        1 ≤ p l) ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 2 ≤
        m + 1 := by
  let owner : ↥B := ⟨k.succ, hkB⟩
  let p := minimalSupportPrivateWitness g h hmin owner
  let c := supportAvoidingWitnessAt g hno z
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  let L := minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz
  change 2 ≤ c k.succ at hk
  have hp : Witness g h p := minimalSupportPrivateWitness_isWitness g h hmin owner
  have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno z
  have hLcard : L.card = E.card :=
    card_minimalSupportPrivateSelfHeavyStarLeaves
      g hg h hh hne hunique hmin hno z hz
  have hLC : L ⊆ (Finset.univ \ B).erase z :=
    minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase
      g h hmin z hz
  have hLO : L ⊆ witnessOmissionCoordinates c :=
    minimalSupportPrivateSelfHeavyStarLeaves_subset_avoidingOmissions
      g hg h hh hmin hno z hz
  by_cases heq : p = c
  · left
    have hpHeavy : 2 ≤ p k.succ := by rw [heq]; exact hk
    have hLOp : L ⊆ witnessOmissionCoordinates p := by
      rw [heq]
      exact hLO
    refine ⟨hpHeavy, ?_⟩
    rw [← hLcard]
    exact Finset.card_le_card hLOp
  · obtain ⟨i, hiGap⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hc hp (Ne.symm heq)
    by_cases hie : i = k.succ
    · right; left
      subst i
      change 4 ≤ p k.succ
      omega
    · by_cases hiz : i = z
      · right; right; left
        subst i
        have hcz : c z = 0 := supportAvoidingWitnessAt_eq_zero g hno z
        change 2 ≤ p z
        omega
      · by_cases hiL : i ∈ L
        · right; right; right; left
          have hiO := hLO hiL
          have hci : c i = -1 :=
            (witnessOmissionCoordinates_exact c i).mpr hiO
          refine ⟨i, hiL, ?_⟩
          change 1 ≤ p i
          omega
        · by_cases hiB : i ∈ B
          · have hownerNe : i ≠ owner := by
              intro hio
              apply hie
              simpa [owner] using hio
            have hpzero := minimalSupportPrivateWitness_eq_zero_of_ne
              g h hmin owner hiB hownerNe
            change p i = 0 at hpzero
            have hcfloor := hc.2.1 i
            exact False.elim (by omega)
          · right; right; right; right
            have hcap := card_transversal_add_reservoir_add_two_le_of_fresh_external
              B L z i hLC hzB hiB hiz hiL
            rw [hLcard] at hcap
            exact hcap

/-- The four non-capacity outcomes of comparing an internal-heavy avoiding
witness with the private witness at its heavy coordinate. -/
def MinimalSupportPrivateSelfHeavyStarPrivateComparisonOutcome
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (_hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (k : Fin m) (hkB : k.succ ∈ B) : Prop :=
  let owner : ↥B := ⟨k.succ, hkB⟩
  let p := minimalSupportPrivateWitness g h hmin owner
  (2 ≤ p k.succ ∧
      (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
        (witnessOmissionCoordinates p).card) ∨
    4 ≤ p k.succ ∨
    2 ≤ p z ∨
    ∃ l ∈ minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz,
      1 ≤ p l

/-- The local comparison is exactly a structured private-witness outcome or
the stronger ambient capacity bound. -/
theorem minimalSupportPrivateSelfHeavyStar_privateComparisonOutcome_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (hzB : z ∉ B)
    (k : Fin m) (hkB : k.succ ∈ B)
    (hk : 2 ≤ supportAvoidingWitnessAt g hno z k.succ) :
    MinimalSupportPrivateSelfHeavyStarPrivateComparisonOutcome
        g h hmin hno z hz k hkB ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 2 ≤
        m + 1 := by
  rcases minimalSupportPrivateSelfHeavyStar_internalHeavy_privateComparison
      g hg h hh hne hunique hmin hno z hz hzB k hkB hk with
    htransfer | hfour | hcenter | hleaf | hcapacity
  · exact Or.inl (Or.inl htransfer)
  · exact Or.inl (Or.inr (Or.inl hfour))
  · exact Or.inl (Or.inr (Or.inr (Or.inl hcenter)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr hleaf)))
  · exact Or.inr hcapacity

/-- Global endpoint after comparing the normalized internal-heavy witness
with its private witness.  The former internal-heavy residual is replaced by
four explicit private-witness coefficient patterns. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_privateComparison
    [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      (∃ z : Fin (m + 1), z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        ∃ r : ReducedSubsetSumCollision g h,
          r ∈ canonicalReducedCollisions (g := g) hh ∧
          (minimalSupportPrivateSelfHeavyExactTwoVertices
            g h hmin).card ≤ r.val.2.card + 1 ∧
          2 ^ ((minimalSupportPrivateSelfHeavyExactTwoVertices
                g h hmin).card - 1) *
              reducedCollisionWeight (m := m) r ≤
            (blockedSignatureUpperValueLayer g r.val.1).card ∧
          (subsetCollisionCoeffs r.val.1 r.val.2 =
              supportAvoidingWitnessAt g hno z ∨
            subsetCollisionCoeffs r.val.1 r.val.2 =
              -supportAvoidingWitnessAt g hno z)) ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 2 ≤
        m + 1 ∨
      ∃ z : Fin (m + 1),
      ∃ hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
        minimalSupportPrivateWitness g h hmin b.val z = -1,
      ∃ k : Fin m,
        z ∉ B ∧ supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz).card =
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          (Finset.univ \ B).erase z ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z) ∧
        ∃ hkB : k.succ ∈ B,
          2 ≤ supportAvoidingWitnessAt g hno z k.succ ∧
          MinimalSupportPrivateSelfHeavyStarPrivateComparisonOutcome
            g h hmin hno z hz k hkB := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_internalHeavy
        g hg h hh hne hunique hmin hno with
    hsmall | hface | hcapacity | ⟨z, hz, k, hzB, hz0, hLcard, hLC, hLO,
      hkB, hk⟩
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hface)
  · exact Or.inr (Or.inr (Or.inl hcapacity))
  · rcases
        minimalSupportPrivateSelfHeavyStar_privateComparisonOutcome_or_capacity
          g hg h hh hne hunique hmin hno z hz hzB k hkB hk with
      houtcome | hcapacity
    · exact Or.inr (Or.inr (Or.inr
        ⟨z, hz, k, hzB, hz0, hLcard, hLC, hLO, hkB, hk, houtcome⟩))
    · exact Or.inr (Or.inr (Or.inl hcapacity))

end MinModulus
