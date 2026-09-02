/-
# The higher-omission self-heavy layer

The self-heavy private family splits exactly into witnesses with two
omissions and witnesses with at least three omissions.  This file records
that partition quantitatively and uses it to normalize the first two outputs
of the internal star/private comparison into an actual member of the global
higher-omission family.

Thus a large exact-two star no longer returns an isolated transfer or a
coefficient-four statement: both become a named global owner population that
can be counted by omission incidences in the next layer.
-/
import MinModulus.G1PrivateHeavySelfHeavyStarPrivateComparison

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Self-heavy private owners whose canonical witness has at least three
omissions. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyVertices g h hmin).filter (fun b ↦
    3 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin ↔
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin ∧
        3 ≤ (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastThreeVertices]

/-- Exact-two and at-least-three owners exhaust the self-heavy family. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_union_atLeastThree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin ∪
        minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin =
      minimalSupportPrivateSelfHeavyVertices g h hmin := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact
        (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
          g h hmin b).mp hb |>.1
    · exact
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b).mp hb |>.1
  · intro hb
    have htwo : 2 ≤ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card :=
      two_le_card_minimalSupportPrivateSelfHeavy_omissions g h hmin hb
    by_cases heq : (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card = 2
    · exact Finset.mem_union_left _
        ((mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
          g h hmin b).mpr ⟨hb, heq⟩)
    · exact Finset.mem_union_right _
        ((mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b).mpr ⟨hb, by omega⟩)

/-- The exact-two and higher-omission layers are disjoint. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_disjoint_atLeastThree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Disjoint (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)
      (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbTwo hbThree
  have htwo :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin b).mp hbTwo
  have hthree :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin b).mp hbThree
  omega

/-- Exact cardinal decomposition of the global self-heavy population. -/
theorem card_minimalSupportPrivateSelfHeavyVertices_eq_exactTwo_add_atLeastThree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportPrivateSelfHeavyVertices g h hmin).card =
      (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card +
        (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).card := by
  rw [← minimalSupportPrivateSelfHeavy_exactTwo_union_atLeastThree
    g h hmin]
  exact Finset.card_union_of_disjoint
    (minimalSupportPrivateSelfHeavy_exactTwo_disjoint_atLeastThree
      g h hmin)

/-- Any lower bound for the full self-heavy population yields, with only a
factor two, a lower bound for one of its two structural layers. -/
theorem le_two_mul_exactTwo_or_le_two_mul_atLeastThree_of_le_selfHeavy
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (K : ℕ)
    (hK : K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      K ≤ 2 *
        (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).card := by
  rw [card_minimalSupportPrivateSelfHeavyVertices_eq_exactTwo_add_atLeastThree
    g h hmin] at hK
  omega

/-- An owner-heavy non-anchor private witness with at least three omissions
is a member of the global higher-omission self-heavy layer. -/
theorem exists_minimalSupportPrivateSelfHeavyAtLeastThree_owner
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (k : Fin m) (hkB : k.succ ∈ B)
    (hk : 2 ≤ minimalSupportPrivateWitness g h hmin
      (⟨k.succ, hkB⟩ : ↥B) k.succ)
    (homit : 3 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin
        (⟨k.succ, hkB⟩ : ↥B))).card) :
    ∃ b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin,
      b.val.val = k.succ := by
  let owner : ↥B := ⟨k.succ, hkB⟩
  have htail : owner ∈ minimalSupportPrivateTailHeavyVertices g h hmin := by
    apply (mem_minimalSupportPrivateTailHeavyVertices_iff
      g h hmin owner).mpr
    exact ⟨k, hk⟩
  let b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin) :=
    ⟨owner, htail⟩
  have hself : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
    apply (mem_minimalSupportPrivateSelfHeavyVertices_iff
      g h hmin b).mpr
    apply minimalSupportPrivateHeavyCoordinate_eq_owner_of_nonzero_ownerHeavy
      g h hmin b (Fin.succ_ne_zero k)
    exact hk
  refine ⟨b, ?_, rfl⟩
  apply (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
    g h hmin b).mpr
  exact ⟨hself, homit⟩

/-- The two owner-side outputs of the star/private comparison both produce
an actual global higher-omission self-heavy owner once the exact-two star has
more than three members. -/
theorem minimalSupportPrivateSelfHeavyStar_privateComparison_ownerHigher_or_center_or_leaf
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (k : Fin m) (hkB : k.succ ∈ B)
    (hfour : 4 ≤
      (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card)
    (houtcome : MinimalSupportPrivateSelfHeavyStarPrivateComparisonOutcome
      g h hmin hno z hz k hkB) :
    (∃ b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin,
        b.val.val = k.succ ∧
          ((minimalSupportPrivateSelfHeavyExactTwoVertices
              g h hmin).card ≤
              (witnessOmissionCoordinates
                (minimalSupportPrivateWitness g h hmin b.val)).card ∨
            4 ≤ minimalSupportPrivateWitness g h hmin b.val b.val)) ∨
      2 ≤ minimalSupportPrivateWitness g h hmin
        (⟨k.succ, hkB⟩ : ↥B) z ∨
      ∃ l ∈ minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz,
        1 ≤ minimalSupportPrivateWitness g h hmin
          (⟨k.succ, hkB⟩ : ↥B) l := by
  let owner : ↥B := ⟨k.succ, hkB⟩
  let p := minimalSupportPrivateWitness g h hmin owner
  rcases houtcome with htransfer | hownerFour | hcenter | hleaf
  · change 2 ≤ p k.succ ∧
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessOmissionCoordinates p).card at htransfer
    have homit : 3 ≤ (witnessOmissionCoordinates p).card := by
      exact le_trans (by omega) htransfer.2
    obtain ⟨b, hb, hbval⟩ :=
      exists_minimalSupportPrivateSelfHeavyAtLeastThree_owner
        g h hmin k hkB htransfer.1 homit
    left
    refine ⟨b, hb, hbval, Or.inl ?_⟩
    have hbowner : b.val = owner := by
      apply Subtype.ext
      simpa [owner] using hbval
    simpa [p, hbowner] using htransfer.2
  · change 4 ≤ p k.succ at hownerFour
    have hnotomit : p k.succ ≠ -1 := by omega
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates
      g (minimalSupportPrivateWitness_isWitness g h hmin owner) hnotomit
    have homit : 3 ≤ (witnessOmissionCoordinates p).card := by
      change p k.succ ≤ ((witnessOmissionCoordinates p).card : ℤ) at hupper
      have hfourCard : 4 ≤ (witnessOmissionCoordinates p).card := by
        exact_mod_cast (hownerFour.trans hupper)
      omega
    have hownerTwo : 2 ≤ minimalSupportPrivateWitness g h hmin
        (⟨k.succ, hkB⟩ : ↥B) k.succ := by
      have : 2 ≤ p k.succ := by omega
      simpa [p, owner] using this
    obtain ⟨b, hb, hbval⟩ :=
      exists_minimalSupportPrivateSelfHeavyAtLeastThree_owner
        g h hmin k hkB hownerTwo (by simpa [p, owner] using homit)
    left
    refine ⟨b, hb, hbval, Or.inr ?_⟩
    have hbowner : b.val = owner := by
      apply Subtype.ext
      simpa [owner] using hbval
    simpa [p, hbowner] using hownerFour
  · exact Or.inr (Or.inl hcenter)
  · exact Or.inr (Or.inr hleaf)

/-- Global higher-omission normalization of the exact-two star branch.  The
old transfer and coefficient-four outputs are merged into one actual member
of the global at-least-three layer. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_higherOwner_or_center_or_leaf
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
          4 ≤ (minimalSupportPrivateSelfHeavyExactTwoVertices
            g h hmin).card ∧
          ((∃ b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices
                g h hmin,
              b.val.val = k.succ ∧
                ((minimalSupportPrivateSelfHeavyExactTwoVertices
                    g h hmin).card ≤
                    (witnessOmissionCoordinates
                      (minimalSupportPrivateWitness g h hmin b.val)).card ∨
                  4 ≤ minimalSupportPrivateWitness
                    g h hmin b.val b.val)) ∨
            2 ≤ minimalSupportPrivateWitness g h hmin
              (⟨k.succ, hkB⟩ : ↥B) z ∨
            ∃ l ∈ minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz,
              1 ≤ minimalSupportPrivateWitness g h hmin
                (⟨k.succ, hkB⟩ : ↥B) l) := by
  classical
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  by_cases hsmall : E.card ≤ 3
  · exact Or.inl hsmall
  have hfour : 4 ≤ E.card := by omega
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_privateComparison
        g hg h hh hne hunique hmin hno with
    hsmall' | hface | hcapacity |
      ⟨z, hz, k, hzB, hz0, hLcard, hLC, hLO, hkB, hk, houtcome⟩
  · exact False.elim (hsmall hsmall')
  · exact Or.inr (Or.inl hface)
  · exact Or.inr (Or.inr (Or.inl hcapacity))
  · have hrefined :=
      minimalSupportPrivateSelfHeavyStar_privateComparison_ownerHigher_or_center_or_leaf
        g h hmin hno z hz k hkB hfour houtcome
    exact Or.inr (Or.inr (Or.inr
      ⟨z, hz, k, hzB, hz0, hLcard, hLC, hLO, hkB, hk, hfour, hrefined⟩))

end MinModulus
