/-
# Global collapse of the heavy-target shift branch

The full-transversal source split makes a stronger observation available.
Every selected shift edge has a deterministic omission shared by the private
witnesses at its source and target.  If the target private witness is
tail-heavy, that one omission already invokes the general tail-heavy
normalization: the target has either three distinct omissions or is a
tail-heavy pure edge.

Outside critical large crossing there is at most one tail-light private
owner.  A fixed-point-free self-map of a nonempty transversal cannot send
every source into that one owner: applying the map once more would fix it.
Thus some source has a heavy target, and the entire long-cycle branch
collapses immediately to one of the two established structural profiles.
-/
import MinModulus.G1PrivateHeavyTransversalGlobalProfiles

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The deterministic common-omission label of the private witnesses at the
two endpoints of the selected shift edge out of `b`. -/
noncomputable def minimalSupportTransversalShiftEdgeLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) : Fin (m + 1) :=
  minimalSupportPrivateShiftCycleEdgeLabel
    g hg hh hno hmin b (d := 1) 0

omit [DecidableEq G] in
/-- The direct shift-edge label is external and omitted by both endpoint
private witnesses. -/
theorem minimalSupportTransversalShiftEdgeLabel_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) :
    let z := minimalSupportTransversalShiftEdgeLabel
      g hg hh hno hmin b
    z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) z = -1 := by
  simpa [minimalSupportTransversalShiftEdgeLabel,
    minimalSupportPrivateShiftCycleVertex] using
      (minimalSupportPrivateShiftCycleEdgeLabel_spec
        g hg hh hno hmin b (d := 1) (0 : Fin 1))

omit [DecidableEq G] in
/-- One heavy selected target already lies in the three-omission or pure-edge
structural frontier; no periodic-cycle analysis is needed for this step. -/
theorem shiftHeavyTargetSource_threeDistinctOmissions_or_tailHeavyPureEdge
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (hb : b ∈ minimalSupportTransversalShiftHeavyTargetSources
      g h hno hmin) :
    WitnessThreeDistinctOmissions g h ∨
      WitnessTailHeavyPureEdge g h := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  have huHeavy : u ∈ minimalSupportPrivateTailHeavyVertices g h hmin :=
    (mem_minimalSupportTransversalShiftHeavyTargetSources_iff
      g h hno hmin b).mp hb
  obtain ⟨k, hk⟩ :=
    (mem_minimalSupportPrivateTailHeavyVertices_iff
      g h hmin u).mp huHeavy
  have huz : minimalSupportPrivateWitness g h hmin u z = -1 := by
    simpa [u, z] using
      (minimalSupportTransversalShiftEdgeLabel_spec
        g hg hh hno hmin b).2.2
  exact tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
    g (minimalSupportPrivateWitness_isWitness g h hmin u) z huz k hk

omit [DecidableEq G] in
/-- If there is at most one light private owner, fixed-point-freeness forces a
heavy selected target on every nonempty transversal. -/
theorem exists_shiftHeavyTargetSource_of_nonempty_of_light_card_le_one
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hB : B.Nonempty)
    (hlight :
      (minimalSupportPrivateTailLightVertices g h hmin).card ≤ 1) :
    (minimalSupportTransversalShiftHeavyTargetSources
      g h hno hmin).Nonempty := by
  classical
  let H := minimalSupportTransversalShiftHeavyTargetSources g h hno hmin
  let L := minimalSupportPrivateTailLightVertices g h hmin
  by_contra hH
  obtain ⟨b, hbB⟩ := hB
  let b₀ : ↥B := ⟨b, hbB⟩
  let T := minimalSupportTransversalShiftTarget g hno hmin
  have htargetLight : ∀ c : ↥B, T c ∈ L := by
    intro c
    apply (mem_minimalSupportPrivateTailLightVertices_iff
      g h hmin (T c)).mpr
    intro k
    by_contra hk
    have hcHeavy : c ∈ H :=
      (mem_minimalSupportTransversalShiftHeavyTargetSources_iff
        g h hno hmin c).mpr
          ((mem_minimalSupportPrivateTailHeavyVertices_iff
            g h hmin (T c)).mpr ⟨k, by omega⟩)
    exact hH ⟨c, hcHeavy⟩
  have hTb₀ : T b₀ ∈ L := htargetLight b₀
  have hTTb₀ : T (T b₀) ∈ L := htargetLight (T b₀)
  have hfixed : T (T b₀) = T b₀ :=
    (Finset.card_le_one.mp hlight) _ hTTb₀ _ hTb₀
  exact minimalSupportTransversalShiftTarget_ne
    g hno hmin (T b₀) hfixed

/-- Critical global endpoint: under the same depth hypothesis used by the
cycle program, the private-target branch needs no cycle bound.  It is already
large crossing, a three-omission witness, or a tail-heavy pure edge. -/
theorem critical_largeCross_or_threeDistinctOmissions_or_tailHeavyPureEdge_of_transversal
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  rcases critical_largeCross_or_privateTailLightVertices_card_le_one
      hq g hg hmin hB with hlarge | hlight
  · exact Or.inl hlarge
  · have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb⟩ :=
      exists_shiftHeavyTargetSource_of_nonempty_of_light_card_le_one
        g hno hmin hBnonempty hlight
    rcases shiftHeavyTargetSource_threeDistinctOmissions_or_tailHeavyPureEdge
        g hg (half_add_half (by rw [pow_succ]; ring))
          hno hmin b hb with hthree | hpure
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr hpure)

end MinModulus
