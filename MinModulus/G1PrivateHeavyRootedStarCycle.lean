/-
# Common-omission labels on a simple private transversal cycle

The rooted omission-star count retains one source owner.  The canonical
private/avoiding shift supplies a second compatible structure: a least-period
cycle with pairwise-distinct private owners.  Label every directed cycle edge
by a common omission of its two private endpoint witnesses.

Because the cycle sources are distinct, one edge-label fiber injects linearly
into the corresponding private-omission vertex fiber.  This improves the
quadratic fiber loss for the complete ordered-pair graph on the structured
cycle subfamily and exposes the exact adjacent private witnesses associated
with every repeated label.
-/
import MinModulus.G1PrivateHeavyRootedOmissionStar

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The `k`th private owner on a displayed canonical shift cycle. -/
noncomputable def minimalSupportPrivateShiftCycleVertex
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k : Fin d) : ↥B :=
  (minimalSupportTransversalShiftTarget g hno hmin)^[k.val] a

/-- The directed edge from a cycle vertex to its canonical shift target,
packaged as an ordered pair of distinct transversal owners. -/
noncomputable def minimalSupportPrivateShiftCycleEdgePair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k : Fin d) :
    MinimalSupportDistinctOrderedPair B :=
  ⟨(minimalSupportPrivateShiftCycleVertex g hno hmin a k,
      minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a k)),
    (minimalSupportTransversalShiftTarget_ne g hno hmin _).symm⟩

/-- The common-omission label carried by one directed cycle edge. -/
noncomputable def minimalSupportPrivateShiftCycleEdgeLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k : Fin d) : Fin (m + 1) :=
  minimalSupportPrivateCommonOmissionLabel g hg hh hmin
    (minimalSupportPrivateShiftCycleEdgePair g hno hmin a k)

/-- A cycle-edge label is external and is omitted by both adjacent private
witnesses. -/
theorem minimalSupportPrivateShiftCycleEdgeLabel_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k : Fin d) :
    let b := minimalSupportPrivateShiftCycleVertex g hno hmin a k
    let u := minimalSupportTransversalShiftTarget g hno hmin b
    let z := minimalSupportPrivateShiftCycleEdgeLabel
      g hg hh hno hmin a k
    z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      minimalSupportPrivateWitness g h hmin u z = -1 := by
  dsimp
  exact minimalSupportPrivateCommonOmissionLabel_spec g hg hh hmin
    (minimalSupportPrivateShiftCycleEdgePair g hno hmin a k)

/-- Labels realized by the directed edges of one displayed cycle. -/
noncomputable def minimalSupportPrivateShiftCycleEdgeLabels
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateShiftCycleEdgeLabel
      g hg hh hno hmin a (d := d))

@[simp] theorem mem_minimalSupportPrivateShiftCycleEdgeLabels_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) :
    z ∈ minimalSupportPrivateShiftCycleEdgeLabels
        g hg hh hno hmin a d ↔
      ∃ k : Fin d,
        minimalSupportPrivateShiftCycleEdgeLabel
          g hg hh hno hmin a k = z := by
  classical
  simp [minimalSupportPrivateShiftCycleEdgeLabels]

/-- Every cycle-edge label lies outside the transversal. -/
theorem minimalSupportPrivateShiftCycleEdgeLabels_disjoint
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    Disjoint
      (minimalSupportPrivateShiftCycleEdgeLabels
        g hg hh hno hmin a d) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨k, rfl⟩ :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabels_iff
      g hg hh hno hmin a d z).mp hz
  exact (minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a k).1 hzB

/-- Directed cycle edges receiving a fixed common-omission label. -/
noncomputable def minimalSupportPrivateShiftCycleEdgeLabelFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun k ↦
    minimalSupportPrivateShiftCycleEdgeLabel
      g hg hh hno hmin a k = z)

@[simp] theorem mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) (k : Fin d) :
    k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
        g hg hh hno hmin a d z ↔
      minimalSupportPrivateShiftCycleEdgeLabel
        g hg hh hno hmin a k = z := by
  classical
  simp [minimalSupportPrivateShiftCycleEdgeLabelFiber]

/-- The edge-label fibers partition all `d` directed cycle edges exactly. -/
theorem card_cycle_eq_sum_minimalSupportPrivateShiftCycleEdgeLabelFibers
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    d = ∑ z ∈ minimalSupportPrivateShiftCycleEdgeLabels
          g hg hh hno hmin a d,
        (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
  classical
  let label := minimalSupportPrivateShiftCycleEdgeLabel
    g hg hh hno hmin a (d := d)
  calc
    d = (Finset.univ : Finset (Fin d)).card := by simp
    _ = ∑ z ∈ (Finset.univ : Finset (Fin d)).image label,
          ((Finset.univ : Finset (Fin d)).filter
            (fun k ↦ label k = z)).card :=
      Finset.card_eq_sum_card_image label Finset.univ
    _ = ∑ z ∈ minimalSupportPrivateShiftCycleEdgeLabels
            g hg hh hno hmin a d,
          (minimalSupportPrivateShiftCycleEdgeLabelFiber
            g hg hh hno hmin a d z).card := by
      rfl

/-- On a least-period cycle, sources of distinct edge indices are distinct. -/
theorem minimalSupportPrivateShiftCycleVertex_injective
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    Function.Injective
      (minimalSupportPrivateShiftCycleVertex g hno hmin a (d := d)) :=
  minimalFixedPointFreeCycle_iterates_injective
    (minimalSupportTransversalShiftTarget g hno hmin) hcycle

/-- A fixed edge-label fiber embeds linearly into the private-owner vertex
fiber omitting the same coordinate. -/
theorem card_minimalSupportPrivateShiftCycleEdgeLabelFiber_le_vertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (z : Fin (m + 1)) :
    (minimalSupportPrivateShiftCycleEdgeLabelFiber
        g hg hh hno hmin a d z).card ≤
      (minimalSupportPrivateOmissionVertices g hmin z).card := by
  classical
  let F := minimalSupportPrivateShiftCycleEdgeLabelFiber
    g hg hh hno hmin a d z
  let V := minimalSupportPrivateOmissionVertices g hmin z
  let enc : ↥F → ↥V := fun k ↦ by
    have hkLabel :=
      (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
        g hg hh hno hmin a d z k.val).mp k.property
    have hspec := minimalSupportPrivateShiftCycleEdgeLabel_spec
      g hg hh hno hmin a k.val
    exact ⟨minimalSupportPrivateShiftCycleVertex
        g hno hmin a k.val,
      (mem_minimalSupportPrivateOmissionVertices_iff
        g hmin z _).mpr (by simpa [hkLabel] using hspec.2.1)⟩
  have henc : Function.Injective enc := by
    intro k l hkl
    apply Subtype.ext
    exact minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle (congrArg Subtype.val hkl)
  have hcard := Fintype.card_le_of_injective enc henc
  change F.card ≤ V.card
  simpa using hcard

/-- The transversal and all cycle-edge labels fit disjointly in the ambient
coordinate set. -/
theorem card_minimalSupport_add_privateShiftCycleEdgeLabels_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) :
    B.card + (minimalSupportPrivateShiftCycleEdgeLabels
      g hg hh hno hmin a d).card ≤ m + 1 := by
  classical
  let Z := minimalSupportPrivateShiftCycleEdgeLabels
    g hg hh hno hmin a d
  have hdisj : Disjoint Z B :=
    minimalSupportPrivateShiftCycleEdgeLabels_disjoint
      g hg hh hno hmin a d
  have hunion : (B ∪ Z).card = B.card + Z.card := by
    rw [Finset.card_union_of_disjoint hdisj.symm]
  have hle : (B ∪ Z).card ≤ m + 1 := by
    simpa using Finset.card_le_univ (B ∪ Z)
  change B.card + Z.card ≤ m + 1
  rw [← hunion]
  exact hle

/-- Cycle-edge pigeonhole with linear reuse: either many external labels fit
beside `B`, or one omission is carried by more than `r` distinct cycle
sources and hence by more than `r` private owners. -/
theorem minimalSupportPrivateShiftCycle_capacity_or_largeVertexFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (L r : ℕ) (hcount : L * r < d) :
    B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        r < (minimalSupportPrivateOmissionVertices g hmin z).card := by
  classical
  let label := minimalSupportPrivateShiftCycleEdgeLabel
    g hg hh hno hmin a (d := d)
  let labels := minimalSupportPrivateShiftCycleEdgeLabels
    g hg hh hno hmin a d
  by_cases hmany : L ≤ labels.card
  · left
    exact (Nat.add_le_add_left hmany B.card).trans
      (card_minimalSupport_add_privateShiftCycleEdgeLabels_le
        g hg hh hno hmin a d)
  · right
    have hlabelsLe : labels.card ≤ L := Nat.le_of_lt (Nat.lt_of_not_ge hmany)
    have hmul : labels.card * r < (Finset.univ : Finset (Fin d)).card := by
      simpa using lt_of_le_of_lt
        (Nat.mul_le_mul_right r hlabelsLe) hcount
    have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin d)),
        label k ∈ labels := by
      intro k _hk
      simp [label, labels, minimalSupportPrivateShiftCycleEdgeLabels]
    obtain ⟨z, hzLabels, hzFiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    have hzLabel : z ∈ minimalSupportPrivateShiftCycleEdgeLabels
        g hg hh hno hmin a d := by
      simpa [labels] using hzLabels
    obtain ⟨k, hkz⟩ :=
      (mem_minimalSupportPrivateShiftCycleEdgeLabels_iff
        g hg hh hno hmin a d z).mp hzLabel
    have hzExternal : z ∉ B := by
      rw [← hkz]
      exact (minimalSupportPrivateShiftCycleEdgeLabel_spec
        g hg hh hno hmin a k).1
    have hfiber : r <
        (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
      simpa [label, minimalSupportPrivateShiftCycleEdgeLabelFiber] using hzFiber
    exact ⟨z, hzExternal, hfiber.trans_le
      (card_minimalSupportPrivateShiftCycleEdgeLabelFiber_le_vertices
        g hg hh hno hmin a hcycle z)⟩

/-- Critical operational endpoint for a least-period private shift cycle.
Outside external-label capacity, a repeated cycle-edge label either forces
the established large-crossing conclusion or retains a tail-heavy private
owner omitting that same label. -/
theorem critical_privateShiftCycle_capacity_or_largeCross_or_tailHeavy
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (L r : ℕ) (hr : 1 ≤ r) (hcount : L * r < d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ z : Fin (n + 1), z ∉ B ∧
        ∃ b : ↥B,
          b ∈ minimalSupportPrivateOmissionVertices g hmin z ∧
          ∃ k : Fin n,
            2 ≤ minimalSupportPrivateWitness g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin b k.succ := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  rcases minimalSupportPrivateShiftCycle_capacity_or_largeVertexFiber
      g hg (half_add_half hN) hno hmin a hcycle L r hcount with
    hcapacity | hfiber
  · exact Or.inl hcapacity
  · obtain ⟨z, hzB, hzlarge⟩ := hfiber
    have hV : 2 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card := by
      omega
    rcases minimalSupportPrivateOmissionVertices_tailLight_or_exists_tailHeavy
        g _ hmin z with hlight | hheavy
    · exact Or.inr (Or.inl
        (critical_largeCross_of_two_light_privateOmissionVertices
          hq g hg hmin z hlight hV hB))
    · exact Or.inr (Or.inr ⟨z, hzB, hheavy⟩)

end MinModulus
