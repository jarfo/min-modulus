/-
# Avoiding a self-heavy omission star

If the exact-two self-heavy omission pairs form a star with center `z`, every
pair has a unique non-center leaf.  Injectivity of the owner-to-pair map makes
these leaves distinct.

No common touch supplies a half witness `r` with `r z = 0`.  Witness
combination between `r` and each star witness must find a common omission.
It cannot use `z`, so it must use that pair's leaf.  Hence all distinct leaves
are omissions of one witness, converting the cardinality of the self-heavy
star into exact negative coefficient mass.
-/
import MinModulus.G1PrivateHeavySelfHeavyOmissionStar

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A canonical half witness avoiding an arbitrary prescribed coordinate. -/
noncomputable def supportAvoidingWitnessAt
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    (z : Fin (m + 1)) : Fin (m + 1) → ℤ :=
  Classical.choose (exists_supportWitness_zero_at_of_noCommonTouch g hno z)

theorem supportAvoidingWitnessAt_isWitness
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    (z : Fin (m + 1)) :
    Witness g h (supportAvoidingWitnessAt g hno z) :=
  (Classical.choose_spec
    (exists_supportWitness_zero_at_of_noCommonTouch g hno z)).1

theorem supportAvoidingWitnessAt_eq_zero
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    (z : Fin (m + 1)) :
    supportAvoidingWitnessAt g hno z z = 0 :=
  (Classical.choose_spec
    (exists_supportWitness_zero_at_of_noCommonTouch g hno z)).2

/-- A star pair has a non-center member. -/
theorem exists_minimalSupportPrivateSelfHeavyStarLeaf
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    ∃ w : Fin (m + 1), w ∈
      (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).erase z := by
  have hb :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin b.val).mp b.property
  have hcard :
      (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).card = 2 := by
    simpa [minimalSupportPrivateSelfHeavyOmissionPair] using hb.2
  have hzmem : z ∈ minimalSupportPrivateSelfHeavyOmissionPair g h hmin b := by
    have hcoeff := hz b.val b.property
    exact (witnessOmissionCoordinates_exact
      (minimalSupportPrivateWitness g h hmin b.val.val) z).mp hcoeff
  have herase := Finset.card_erase_add_one hzmem
  have heraseCard :
      ((minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).erase z).card = 1 := by
    omega
  exact Finset.card_pos.mp (by rw [heraseCard]; decide)

/-- The selected non-center leaf of one exact-two self-heavy star pair. -/
noncomputable def minimalSupportPrivateSelfHeavyStarLeaf
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    Fin (m + 1) :=
  Classical.choose
    (exists_minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b)

theorem minimalSupportPrivateSelfHeavyStarLeaf_mem_erase
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b ∈
      (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).erase z :=
  Classical.choose_spec
    (exists_minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b)

/-- Each omission pair is exactly the center together with its selected leaf. -/
theorem minimalSupportPrivateSelfHeavyOmissionPair_eq_center_leaf
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    minimalSupportPrivateSelfHeavyOmissionPair g h hmin b =
      {z, minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b} := by
  have hb :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin b.val).mp b.property
  have hcard :
      (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).card = 2 := by
    simpa [minimalSupportPrivateSelfHeavyOmissionPair] using hb.2
  have hzmem : z ∈ minimalSupportPrivateSelfHeavyOmissionPair g h hmin b := by
    exact (witnessOmissionCoordinates_exact
      (minimalSupportPrivateWitness g h hmin b.val.val) z).mp
        (hz b.val b.property)
  have hleafErase := minimalSupportPrivateSelfHeavyStarLeaf_mem_erase
    g h hmin z hz b
  have hleaf := Finset.mem_of_mem_erase hleafErase
  have hleafNe :
      z ≠ minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b :=
    Ne.symm (Finset.mem_erase.mp hleafErase).1
  exact finset_eq_pair_of_card_eq_two_of_mem
    hcard hzmem hleaf hleafNe

/-- Under no common touch, distinct star owners have distinct leaves. -/
theorem minimalSupportPrivateSelfHeavyStarLeaf_injective
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    Function.Injective
      (minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz) := by
  intro b u hleaf
  apply minimalSupportPrivateSelfHeavyOmissionPair_injective
    g hg h hh hne hunique hmin hno
  rw [minimalSupportPrivateSelfHeavyOmissionPair_eq_center_leaf
      g h hmin z hz b,
    minimalSupportPrivateSelfHeavyOmissionPair_eq_center_leaf
      g h hmin z hz u,
    hleaf]

/-- The avoiding witness at the center omits every selected star leaf. -/
theorem supportAvoidingWitnessAt_starLeaf_eq_neg_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    supportAvoidingWitnessAt g hno z
        (minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b) = -1 := by
  let c := minimalSupportPrivateWitness g h hmin b.val.val
  let r := supportAvoidingWitnessAt g hno z
  let w := minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b
  have hcz : c z ≠ 0 := by
    have := hz b.val b.property
    change c z = -1 at this
    omega
  obtain ⟨i, hci, hri⟩ := exists_common_omission_of_witness_ne_zero_zero
    g hg hh
      (minimalSupportPrivateWitness_isWitness g h hmin b.val.val)
      (supportAvoidingWitnessAt_isWitness g hno z)
      hcz (supportAvoidingWitnessAt_eq_zero g hno z)
  have hiPair : i ∈ minimalSupportPrivateSelfHeavyOmissionPair g h hmin b := by
    exact (witnessOmissionCoordinates_exact c i).mp hci
  have hpair := minimalSupportPrivateSelfHeavyOmissionPair_eq_center_leaf
    g h hmin z hz b
  have hi : i = z ∨ i = w := by
    simpa [hpair, w] using hiPair
  rcases hi with hiz | hiw
  · subst i
    have hrz := supportAvoidingWitnessAt_eq_zero g hno z
    change r z = 0 at hrz
    change r z = -1 at hri
    omega
  · subst i
    exact hri

/-- A self-heavy omission star injects into the exact omission set of one
center-avoiding witness. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingOmissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
      (witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z)).card := by
  classical
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  let O := witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z)
  let enc : ↥E → ↥O := fun b ↦
    ⟨minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b,
      (witnessOmissionCoordinates_exact
        (supportAvoidingWitnessAt g hno z) _).mp
          (supportAvoidingWitnessAt_starLeaf_eq_neg_one
            g hg h hh hmin hno z hz b)⟩
  have henc : Function.Injective enc := by
    intro b u hbu
    apply minimalSupportPrivateSelfHeavyStarLeaf_injective
      g hg h hh hne hunique hmin hno z hz
    exact congrArg Subtype.val hbu
  have hcard := Fintype.card_le_of_injective enc henc
  change E.card ≤ O.card
  simpa using hcard

/-- Global star alternative: the exact-two self-heavy layer is bounded by
three, or by the omission count of one witness vanishing at an external star
center. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_avoidingOmissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessOmissionCoordinates
            (supportAvoidingWitnessAt g hno z)).card := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_commonOmission
        g hg h hh hne hunique hmin hno with hsmall | ⟨z, hzB, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨z, hzB, supportAvoidingWitnessAt_eq_zero g hno z,
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingOmissions
        g hg h hh hne hunique hmin hno z hz⟩

end MinModulus
