/-
# Exact geometry of the retained pure target

The provenance-rich target collapse identifies a canonical private witness
at the selected target and retains the deterministic external edge label as
one endpoint of an exact pure edge.  Privacy now determines how this edge can
meet the minimal transversal: it meets it in exactly its target owner.

Since the retained edge label is outside the transversal, the owner is either
the coefficient-`2` center or the other endpoint.  In either case the third
support coordinate is also outside the transversal.  Thus the pure arm does
not merely return a broad profile: it produces two distinct external
coordinates and the capacity bound `B.card + 2 <= m + 1`.
-/
import MinModulus.G1PrivateHeavyProtectedStructuralSplit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- The coefficient support of a canonical private witness meets its minimal
transversal in exactly the owner coordinate. -/
theorem minimalSupportPrivateWitness_support_inter_eq_singleton
    (g : Fin m → G) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) :
    B ∩ coefficientSupport (minimalSupportPrivateWitness g h hmin b) =
      {b.1} := by
  classical
  ext a
  simp only [Finset.mem_inter, mem_coefficientSupport_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨haB, hca⟩
    by_contra hab
    exact hca (minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b haB hab)
  · intro hab
    subst a
    exact ⟨b.property, minimalSupportPrivateWitness_ne_zero g h hmin b⟩

omit [DecidableEq G] in
/-- Exact owner/external-coordinate geometry in the retained pure target.
The returned `x` and `e` are the very coordinates in the pure-pair witness,
not merely coordinates reconstructed from its broad profile. -/
theorem minimalSupportTransversalShiftTargetPurePair_owner_or_external
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b)) :
    ∃ x : Fin (m + 1), ∃ e : Fin m,
      x ≠ minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b ∧
      e.succ ≠ minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b ∧
      e.succ ≠ x ∧
      (∀ y, minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) y = -1 ↔
        y = minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b ∨
          y = x) ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) =
        pureEdgeCoeffs e.succ
          (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b) x ∧
      (((minimalSupportTransversalShiftTarget g hno hmin b :
            Fin (m + 1)) = e.succ ∧ x ∉ B) ∨
        ((minimalSupportTransversalShiftTarget g hno hmin b :
            Fin (m + 1)) = x ∧ e.succ ∉ B)) := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  let c := minimalSupportPrivateWitness g h hmin u
  obtain ⟨x, e, hxz, hez, hex, homit, heTwo, hshape⟩ := hpure
  refine ⟨x, e, hxz, hez, hex, homit, heTwo, hshape, ?_⟩
  have hcu : c u ≠ 0 := minimalSupportPrivateWitness_ne_zero g h hmin u
  have hshapeC : c = pureEdgeCoeffs e.succ z x := by
    simpa [c, u, z] using hshape
  have huSupport : (u : Fin (m + 1)) ∈
      ({e.succ, z, x} : Finset (Fin (m + 1))) := by
    rw [hshapeC] at hcu
    exact pureEdgeCoeffs_ne_zero_mem e.succ z x u hcu
  simp only [Finset.mem_insert, Finset.mem_singleton] at huSupport
  have hzB : z ∉ B :=
    (minimalSupportTransversalShiftEdgeLabel_spec
      g hg hh hno hmin b).1
  rcases huSupport with hue | huz | hux
  · left
    refine ⟨hue, ?_⟩
    intro hxB
    have hxu : x ≠ (u : Fin (m + 1)) := by
      intro hxu
      apply hex
      exact hue.symm.trans hxu.symm
    have hxZero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin u hxB hxu
    have hxZeroC : c x = 0 := by simpa [c] using hxZero
    have hxOmit : c x = -1 := by
      simpa [c, u, z] using (homit x).2 (Or.inr rfl)
    rw [hxZeroC] at hxOmit
    omega
  · have huB : (u : Fin (m + 1)) ∈ B := u.property
    rw [huz] at huB
    exact (hzB huB).elim
  · right
    refine ⟨hux, ?_⟩
    intro heB
    have heu : e.succ ≠ (u : Fin (m + 1)) := by
      intro heu
      apply hex
      exact heu.trans hux
    have heZero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin u heB heu
    have heZeroC : c e.succ = 0 := by simpa [c] using heZero
    have heTwoC : c e.succ = 2 := by
      simpa [c, u] using heTwo
    rw [heZeroC] at heTwoC
    omega

omit [DecidableEq G] in
/-- The retained pure target supplies two distinct coordinates outside the
minimal transversal: the edge label and whichever of the center/other
endpoint is not the target owner. -/
theorem minimalSupportTransversalShiftTargetPurePair_card_add_two_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b)) :
    B.card + 2 ≤ m + 1 := by
  classical
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  obtain ⟨x, e, hxz, hez, _hex, _homit, _heTwo, _hshape,
      howner⟩ :=
    minimalSupportTransversalShiftTargetPurePair_owner_or_external
      g hg hh hno hmin b hpure
  have hzB : z ∉ B :=
    (minimalSupportTransversalShiftEdgeLabel_spec
      g hg hh hno hmin b).1
  have capacity (y : Fin (m + 1)) (hyB : y ∉ B) (hyz : y ≠ z) :
      B.card + 2 ≤ m + 1 := by
    have hzInsert : z ∉ insert y B := by
      simp [hzB, Ne.symm hyz]
    have hcard := Finset.card_le_card
      (Finset.subset_univ (insert z (insert y B)))
    rw [Finset.card_insert_of_notMem hzInsert,
      Finset.card_insert_of_notMem hyB] at hcard
    simpa using hcard
  rcases howner with ⟨_owner, hxB⟩ | ⟨_owner, heB⟩
  · exact capacity x hxB hxz
  · exact capacity e.succ heB hez

/-- The provenance-rich heavy-target residual with the new pure-arm capacity
retained.  The three-omission arm is unchanged; the pure arm now records that
the transversal misses at least two ambient coordinates. -/
def MinimalSupportTransversalHeavyTargetPureGeometryResidual
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Prop :=
  ∃ b : ↥B,
    b ∈ minimalSupportTransversalShiftHeavyTargetSources g h hno hmin ∧
      let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
      MinimalSupportTransversalShiftTargetThreeOmissionsAt
          g h hno hmin b z ∨
        (MinimalSupportTransversalShiftTargetPurePairAt
            g h hno hmin b z ∧ B.card + 2 ≤ m + 1)

omit [DecidableEq G] in
/-- Refine the old structural residual by adding the exact pure-arm capacity
bound, without weakening the three-omission arm. -/
theorem MinimalSupportTransversalHeavyTargetStructuralResidual.pureGeometry
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hres : MinimalSupportTransversalHeavyTargetStructuralResidual
      g hg hh hno hmin) :
    MinimalSupportTransversalHeavyTargetPureGeometryResidual
      g hg hh hno hmin := by
  obtain ⟨b, hb, hthree | hpure⟩ := hres
  · exact ⟨b, hb, Or.inl hthree⟩
  · exact ⟨b, hb, Or.inr ⟨hpure,
      minimalSupportTransversalShiftTargetPurePair_card_add_two_le
        g hg hh hno hmin b hpure⟩⟩

omit [DecidableEq G] in
/-- Forgetting the new capacity field recovers the preceding structural
residual exactly. -/
theorem MinimalSupportTransversalHeavyTargetPureGeometryResidual.structural
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hres : MinimalSupportTransversalHeavyTargetPureGeometryResidual
      g hg hh hno hmin) :
    MinimalSupportTransversalHeavyTargetStructuralResidual
      g hg hh hno hmin := by
  obtain ⟨b, hb, hthree | ⟨hpure, _hcap⟩⟩ := hres
  · exact ⟨b, hb, Or.inl hthree⟩
  · exact ⟨b, hb, Or.inr hpure⟩

/-- The full protected private-heavy residual with pure-target geometry
attached to the same minimal transversal and recursive tuple. -/
def ProfilePrivateHeavyTargetPureGeometryProtectedResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0) : Prop :=
  ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0,
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
        ProfilePrivateHeavyProtectedPayload
            (N := N) (M := M) (K := K) g B ∧
          MinimalSupportTransversalHeavyTargetPureGeometryResidual
            g hg hh hno hmin

omit [DecidableEq G] in
/-- Upgrade the large-transversal protected structural branch with the exact
pure-owner dichotomy and its two-external-coordinate capacity. -/
theorem ProfilePrivateHeavyTargetStructuralProtectedResidual.pureGeometry
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hres : ProfilePrivateHeavyTargetStructuralProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureGeometryProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  obtain ⟨hno, B, hmin, hpayload, hstruct⟩ := hres
  exact ⟨hno, B, hmin, hpayload,
    hstruct.pureGeometry g hg hh hno hmin⟩

end MinModulus
