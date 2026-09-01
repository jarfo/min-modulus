/-
# Minimal witness-labelled avoidance cycles

Minimize the positive return time of the witness-preserving avoidance
successor.  The resulting period is at least three, its edge states within one
period are pairwise distinct, and its length is bounded by the square of the
ambient coordinate count.  This removes repetitions introduced by the finite
orbit argument before the cycle's witness algebra is analyzed.
-/
import MinModulus.G1AvoidanceCycleAlgebra

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A bridge cycle whose period is the least positive return time of its base
edge state. -/
def IsMinimalWitnessAvoidanceBridgeCycle
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  IsWitnessAvoidanceBridgeCycle g hg hh hno p d ∧
    ∀ e : ℕ, 0 < e →
      (witnessAvoidanceBridgeNext g hg hh hno)^[e] p = p → d ≤ e

/-- A positive return time for a non-backtracking edge successor cannot be
one or two. -/
theorem three_le_period_of_nonbacktracking_edgeState
    (g : Fin m → G) {h : G}
    (T : WitnessAvoidanceEdgeState g h → WitnessAvoidanceEdgeState g h)
    (hfst : ∀ p, (T p).val.1 = p.val.2)
    (hback : ∀ p, (T p).val.2 ≠ p.val.1)
    (p : WitnessAvoidanceEdgeState g h) {d : ℕ}
    (hdpos : 0 < d) (hperiod : T^[d] p = p) :
    3 ≤ d := by
  have hd1 : d ≠ 1 := by
    intro hd
    have hfix : T p = p := by
      simpa [hd, Function.iterate_succ_apply] using hperiod
    have hfstEq := congrArg (fun q ↦ q.val.1) hfix
    have hnext := hfst p
    have hne := witnessAvoidanceEdgeState_fst_ne_snd p
    rw [hnext] at hfstEq
    exact hne hfstEq.symm
  have hd2 : d ≠ 2 := by
    intro hd
    have hfix : T (T p) = p := by
      simpa [hd, Function.iterate_succ_apply] using hperiod
    have hfstEq := congrArg (fun q ↦ q.val.1) hfix
    have hnext := hfst (T p)
    have hne := hback p
    rw [hnext] at hfstEq
    exact hne hfstEq
  omega

/-- If `p` has period `d` and two iterates before `d` agree, their index
difference is also a period of `p`. -/
theorem iterate_sub_is_period_of_eq_of_period
    {α : Type*} (T : α → α) {p : α} {d a b : ℕ}
    (hperiod : T^[d] p = p) (had : a ≤ d) (hab : a ≤ b)
    (heq : T^[a] p = T^[b] p) :
    T^[b - a] p = p := by
  calc
    T^[b - a] p = T^[b - a] (T^[d] p) := by rw [hperiod]
    _ = T^[(b - a) + d] p :=
      (Function.iterate_add_apply T (b - a) d p).symm
    _ = T^[(d - a) + b] p := by
      congr 1
      omega
    _ = T^[d - a] (T^[b] p) :=
      Function.iterate_add_apply T (d - a) b p
    _ = T^[d - a] (T^[a] p) := by rw [heq]
    _ = T^[(d - a) + a] p :=
      (Function.iterate_add_apply T (d - a) a p).symm
    _ = T^[d] p := by rw [Nat.sub_add_cancel had]
    _ = p := hperiod

/-- Every initial edge reaches a bridge cycle with least positive period. -/
theorem exists_minimalWitnessAvoidanceBridgeCycle
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p₀ : WitnessAvoidanceEdgeState g h) :
    ∃ p : WitnessAvoidanceEdgeState g h, ∃ d : ℕ,
      IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d := by
  classical
  obtain ⟨p, d₀, hd₀⟩ :=
    exists_witnessAvoidanceBridgeCycle g hg hh hno p₀
  let T := witnessAvoidanceBridgeNext g hg hh hno
  have hex : ∃ e : ℕ, 0 < e ∧ T^[e] p = p :=
    ⟨d₀, by have := hd₀.1; omega, hd₀.2.1⟩
  let d := Nat.find hex
  have hdspec : 0 < d ∧ T^[d] p = p := Nat.find_spec hex
  have hdthree : 3 ≤ d :=
    three_le_period_of_nonbacktracking_edgeState g T
      (witnessAvoidanceBridgeNext_fst g hg hh hno)
      (witnessAvoidanceBridgeNext_snd_ne_fst g hg hh hno)
      p hdspec.1 hdspec.2
  refine ⟨p, d, ⟨hdthree, hdspec.2, ?_⟩, ?_⟩
  · intro k
    exact witnessAvoidanceBridgeNext_has_doubleOmission g hg hh hno (T^[k] p)
  · intro e he heq
    exact Nat.find_min' hex ⟨he, heq⟩

/-- The edge states in one minimal bridge period are pairwise distinct. -/
theorem minimalWitnessAvoidanceBridgeCycle_iterates_injective
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d) :
    Function.Injective (fun k : Fin d ↦
      (witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p) := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  intro a b habEq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hab | hba
  · have hsmall := iterate_sub_is_period_of_eq_of_period T
      hmin.1.2.1 (Nat.le_of_lt a.isLt) hab.le habEq
    have hleast := hmin.2 (b.val - a.val) (Nat.sub_pos_of_lt hab) hsmall
    omega
  · have hsmall := iterate_sub_is_period_of_eq_of_period T
      hmin.1.2.1 (Nat.le_of_lt b.isLt) hba.le habEq.symm
    have hleast := hmin.2 (a.val - b.val) (Nat.sub_pos_of_lt hba) hsmall
    omega

/-- A minimal bridge period is bounded by the number of avoidance edge
states. -/
theorem minimalWitnessAvoidanceBridgeCycle_period_le_card
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d) :
    d ≤ Fintype.card (WitnessAvoidanceEdgeState g h) := by
  simpa using Fintype.card_le_of_injective
    (fun k : Fin d ↦ (witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p)
    (minimalWitnessAvoidanceBridgeCycle_iterates_injective
      g hg hh hno hmin)

/-- Avoidance edge states inject into ordered coordinate pairs. -/
theorem card_witnessAvoidanceEdgeState_le_square
    (g : Fin m → G) (h : G) :
    Fintype.card (WitnessAvoidanceEdgeState g h) ≤ m * m := by
  have hcard := Fintype.card_le_of_injective
    (fun p : WitnessAvoidanceEdgeState g h ↦ p.val) Subtype.val_injective
  simpa using hcard

/-- Quantitative bound for a minimal witness-labelled avoidance period. -/
theorem minimalWitnessAvoidanceBridgeCycle_period_le_square
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d) :
    d ≤ m * m :=
  (minimalWitnessAvoidanceBridgeCycle_period_le_card
    g hg hh hno hmin).trans (card_witnessAvoidanceEdgeState_le_square g h)

/-- The genuine critical heavy residual contains a minimal witness-labelled
avoidance cycle. -/
theorem criticalGenuineHeavyTwoStepEscape_exists_minimalBridgeCycle
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d := by
  obtain ⟨hno, p₀, _d₀, _hcycle⟩ :=
    criticalGenuineHeavyTwoStepEscape_exists_bridgeCycle g hg hescape
  obtain ⟨p, d, hmin⟩ := exists_minimalWitnessAvoidanceBridgeCycle g hg
    (half_add_half (by rw [pow_succ]; ring)) hno p₀
  exact ⟨hno, p, d, hmin⟩

end MinModulus
