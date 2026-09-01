/-
# Genuine heavy escape iteration

The heavy omission escape is reached only after common touch has failed, but
the first package did not retain that global negation.  Keeping it allows the
escape to iterate.  Every external omission has its own avoiding witness; two
successive avoiding witnesses must share a further omission, distinct from
the two preceding coordinates, or witness combination would make them exact
negatives.
-/
import MinModulus.G1MinimalTransversalEscape

namespace MinModulus

/-- The actual heavy residual retains global failure of common touch together
with the omission-transversal escape package. -/
def CriticalGenuineHeavyOmissionEscape
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ¬ CriticalCommonTouched g ∧ CriticalHeavyOmissionEscape g

/-- The final critical trichotomy with the no-common-touch field retained in
the heavy branch. -/
theorem critical_largeCross_or_commonTouched_or_genuineHeavyOmissionEscape
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalGenuineHeavyOmissionEscape g := by
  rcases critical_largeCross_or_commonTouched_or_heavy
      hn hq g hg hcritical with hcross | htouch | hheavy
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · by_cases htouch : CriticalCommonTouched g
    · exact Or.inr (Or.inl htouch)
    · exact Or.inr (Or.inr ⟨htouch,
        criticalHeavyOmissionEscape_of_not_commonTouched
          g hg hheavy htouch⟩)

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Two witnesses that successively avoid `b` and `z`, while the first omits
`z`, must share a further omission distinct from both `b` and `z`. -/
theorem exists_fresh_common_omission_of_successive_avoidance
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {e f : Fin m → ℤ} (he : Witness g h e) (hf : Witness g h f)
    {b z : Fin m} (heb : e b = 0) (hez : e z = -1) (hfz : f z = 0) :
    ∃ w : Fin m, w ≠ b ∧ w ≠ z ∧ e w = -1 ∧ f w = -1 := by
  have hcommon : ∃ w : Fin m, e w = -1 ∧ f w = -1 := by
    by_contra hnone
    have hshare : ∀ i, ¬ (e i = -1 ∧ f i = -1) := by
      intro i hi
      exact hnone ⟨i, hi⟩
    have hneg := witness_combination g hg hh he hf hshare
    have hz := congrFun hneg z
    simp only [Pi.neg_apply, hez] at hz
    omega
  obtain ⟨w, hew, hfw⟩ := hcommon
  have hwb : w ≠ b := by
    intro hwb
    subst w
    omega
  have hwz : w ≠ z := by
    intro hwz
    subst w
    omega
  exact ⟨w, hwb, hwz, hew, hfw⟩

/-- The iterated heavy structure: every root omission starts a path
`b → z → w` through three pairwise-distinct coordinates, realized by two
successive avoiding half-witnesses. -/
def CriticalGenuineHeavyTwoStepEscape
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ∃ c : Fin (n + 1) → ℤ,
    Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      (∃ k : Fin n, 2 ≤ c k.succ) ∧
      ¬ CriticalCommonTouched g ∧
      ∀ b : Fin (n + 1), c b = -1 →
        ∃ e f : Fin (n + 1) → ℤ, ∃ z w : Fin (n + 1),
          Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) e ∧
          Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) f ∧
          z ≠ b ∧ w ≠ b ∧ w ≠ z ∧
          c z = -1 ∧ e b = 0 ∧ e z = -1 ∧
          f z = 0 ∧ e w = -1 ∧ f w = -1

/-- A genuine heavy omission escape iterates to the non-backtracking two-step
package. -/
theorem criticalGenuineHeavyTwoStepEscape_of_omissionEscape
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyOmissionEscape g) :
    CriticalGenuineHeavyTwoStepEscape g := by
  obtain ⟨hno, c, hc, hheavy, _htrans, hesc⟩ := hescape
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hh :
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) +
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) = 0 :=
    half_add_half hN
  refine ⟨c, hc, hheavy, hno, ?_⟩
  intro b hcb
  obtain ⟨e, he, heb, z, hzb, hcz, hez⟩ := hesc b hcb
  have havoid : ∃ f : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) f ∧
        f z = 0 := by
    by_contra hnone
    apply hno
    refine ⟨z, ?_⟩
    intro f hf
    by_contra hfz
    exact hnone ⟨f, hf, hfz⟩
  obtain ⟨f, hf, hfz⟩ := havoid
  obtain ⟨w, hwb, hwz, hew, hfw⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh he hf heb hez hfz
  exact ⟨e, f, z, w, he, hf, hzb, hwb, hwz,
    hcz, heb, hez, hfz, hew, hfw⟩

/-- The global critical frontier with the iterated heavy branch exposed. -/
theorem critical_largeCross_or_commonTouched_or_genuineHeavyTwoStepEscape
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalGenuineHeavyTwoStepEscape g := by
  rcases critical_largeCross_or_commonTouched_or_genuineHeavyOmissionEscape
      hn hq g hg hcritical with hcross | htouch | hescape
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr
      (criticalGenuineHeavyTwoStepEscape_of_omissionEscape g hg hescape))

/-- The iterated genuine-heavy branch supplies the sharp one-coordinate
critical deletion step.  After the structural work above, this is the exact
remaining heavy-side obligation. -/
def CriticalGenuineHeavyTwoStepEscapeDeleteStep : Prop :=
  ∀ {n s q : ℕ} (_hn : 1 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    CriticalGenuineHeavyTwoStepEscape g →
    AdmitsValidTuple n (2 ^ s * q)

/-- Large-crossing deletion plus deletion from the genuine two-step heavy
escape gives the complete critical deletion interface. -/
theorem criticalRangeDeleteStep_of_largeCross_and_genuineHeavyTwoStep
    (hcross : CriticalLargeCrossingDeleteStep)
    (hheavy : CriticalGenuineHeavyTwoStepEscapeDeleteStep) :
    CriticalRangeDeleteStep := by
  intro n s q hq hcritical hvalid
  by_cases hn : 1 ≤ n
  · obtain ⟨g, hg⟩ := hvalid
    rcases critical_largeCross_or_commonTouched_or_genuineHeavyTwoStepEscape
        hn hq g hg hcritical with hlarge | htouch | hescape
    · exact hcross hn hq g hg hcritical hlarge
    · obtain ⟨j, hj⟩ := htouch
      have hM : 0 < 2 ^ s * q :=
        mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
      have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
        rw [pow_succ]
        ring
      exact exists_validTuple_half_of_delete
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q) hN hM hg j hj
    · exact hheavy hn hq g hg hcritical hescape
  · have hnzero : n = 0 := by omega
    subst n
    have hqpos := Odd.pos hq
    simp [stratumBound] at hcritical
    omega

/-- Updated exact global interface: large-crossing deletion, genuine
two-step-heavy deletion, G2, and G3 imply Conjecture 1. -/
theorem global_lower_bound_of_largeCross_and_genuineHeavyTwoStep
    (hcross : CriticalLargeCrossingDeleteStep)
    (hheavy : CriticalGenuineHeavyTwoStepEscapeDeleteStep)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_deleteStep
    (criticalRangeDeleteStep_of_largeCross_and_genuineHeavyTwoStep
      hcross hheavy) hG2 hG3 hn hN hv

end MinModulus
