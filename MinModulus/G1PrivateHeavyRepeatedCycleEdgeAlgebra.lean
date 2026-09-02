/-
# Repeated-label algebra on two private shift-cycle edges

The cycle count produces a fiber of directed edges carrying one external
common-omission label.  This module keeps two distinct members of that fiber
simultaneously.  Their sources and targets are distinct along a least-period
cycle, and all four endpoint private witnesses omit the repeated label.

At critical depth, the two target owners either already give the selected
tail-light crossing charge, or one of those exact targets is tail-heavy.  In
the latter case the fixed-edge algebra retains its canonical private and
avoiding witnesses.  This is the first lossless two-edge interface for the
next coefficient/profile comparison.
-/
import MinModulus.G1PrivateHeavyCycleEdgeAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The targets of distinct edge indices on a least-period cycle are
distinct.  Applying `T^[d-1]` recovers each source from its target. -/
theorem minimalSupportPrivateShiftCycleTarget_injective
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    Function.Injective (fun k : Fin d ↦
      minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a k)) := by
  let T := minimalSupportTransversalShiftTarget g hno hmin
  have hdpos : 0 < d :=
    lt_of_lt_of_le (by decide : 0 < 2) hcycle.1
  have hrecover : ∀ k : Fin d,
      (T^[d - 1]) (T (T^[k.val] a)) = T^[k.val] a := by
    intro k
    have hperiod : (T^[d]) (T^[k.val] a) = T^[k.val] a := by
      calc
        (T^[d]) (T^[k.val] a) = T^[d + k.val] a :=
          (Function.iterate_add_apply T d k.val a).symm
        _ = T^[k.val + d] a :=
          congrArg (fun e : ℕ ↦ T^[e] a) (Nat.add_comm d k.val)
        _ = (T^[k.val]) (T^[d] a) :=
          Function.iterate_add_apply T k.val d a
        _ = T^[k.val] a := by rw [hcycle.2.1]
    calc
      (T^[d - 1]) (T (T^[k.val] a)) =
          (T^[(d - 1) + 1]) (T^[k.val] a) :=
        (Function.iterate_succ_apply T (d - 1) (T^[k.val] a)).symm
      _ = (T^[d]) (T^[k.val] a) :=
        congrArg (fun e : ℕ ↦ (T^[e]) (T^[k.val] a))
          (Nat.sub_add_cancel hdpos)
      _ = T^[k.val] a := hperiod
  intro k l hkl
  change T (T^[k.val] a) = T (T^[l.val] a) at hkl
  apply minimalSupportPrivateShiftCycleVertex_injective
    g hno hmin a hcycle
  change T^[k.val] a = T^[l.val] a
  calc
    T^[k.val] a = (T^[d - 1]) (T (T^[k.val] a)) :=
      (hrecover k).symm
    _ = (T^[d - 1]) (T (T^[l.val] a)) := congrArg (T^[d - 1]) hkl
    _ = T^[l.val] a := hrecover l

/-- The target of edge `k` is the source at the cyclic successor index. -/
theorem minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (k : Fin d) :
    minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a k) =
      minimalSupportPrivateShiftCycleVertex g hno hmin a (finRotate d k) := by
  let T := minimalSupportTransversalShiftTarget g hno hmin
  change T (T^[k.val] a) = T^[(finRotate d k).val] a
  have hdpos : 0 < d :=
    lt_of_lt_of_le (by decide : 0 < 2) hcycle.1
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  by_cases hk : k = Fin.last u
  · subst k
    rw [finRotate_last]
    change T (T^[u] a) = a
    rw [← Function.iterate_succ_apply' T u a]
    exact hcycle.2.1
  · have hklt : k.val < u := Fin.val_lt_last hk
    rw [finRotate_of_lt hklt]
    simpa using (Function.iterate_succ_apply' T k.val a).symm

/-- If an iterate based at a vertex of a least-period cycle has positive
period `e`, then the displayed least period is at most `e`. -/
theorem minimalFixedPointFreeCycle_period_le_of_iterate_period
    {α : Type*} (T : α → α) {a : α} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (k : Fin d) {e : ℕ} (hepos : 0 < e)
    (he : (T^[e]) (T^[k.val] a) = T^[k.val] a) :
    d ≤ e := by
  have heq := congrArg (T^[d - k.val]) he
  simp only [← Function.iterate_add_apply] at heq
  have hk : k.val ≤ d := Nat.le_of_lt k.isLt
  have hleft : d - k.val + (e + k.val) = e + d := by omega
  have hright : d - k.val + k.val = d := Nat.sub_add_cancel hk
  have heq' : (T^[e + d]) a = (T^[d]) a := by
    simpa [hleft, hright] using heq
  apply hcycle.2.2 e hepos
  calc
    (T^[e]) a = (T^[e]) ((T^[d]) a) := by rw [hcycle.2.1]
    _ = (T^[e + d]) a :=
      (Function.iterate_add_apply T e d a).symm
    _ = (T^[d]) a := heq'
    _ = a := hcycle.2.1

/-- On a cycle of length at least three, two distinct directed edges cannot
be the two orientations of the same endpoint pair. -/
theorem minimalSupportPrivateShiftCycle_not_reverse_of_three_le
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hd : 3 ≤ d) {k l : Fin d}
    (hforward : minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a k) =
      minimalSupportPrivateShiftCycleVertex g hno hmin a l) :
    minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a l) ≠
      minimalSupportPrivateShiftCycleVertex g hno hmin a k := by
  let T := minimalSupportTransversalShiftTarget g hno hmin
  intro hback
  have hperiodTwo : (T^[2]) (T^[k.val] a) = T^[k.val] a := by
    change T (T (T^[k.val] a)) = T^[k.val] a
    calc
      T (T (T^[k.val] a)) = T (T^[l.val] a) := by
        exact congrArg T hforward
      _ = T^[k.val] a := hback
  have hdle : d ≤ 2 :=
    minimalFixedPointFreeCycle_period_le_of_iterate_period
      T hcycle k (by decide) hperiodTwo
  omega

/-- The private owners touched by two directed cycle edges. -/
noncomputable def minimalSupportPrivateShiftCycleEdgePairEndpointOwners
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k l : Fin d) : Finset ↥B :=
  {minimalSupportPrivateShiftCycleVertex g hno hmin a k,
    minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a k),
    minimalSupportPrivateShiftCycleVertex g hno hmin a l,
    minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a l)}

/-- Two distinct edges on a cycle of length at least three touch at least
three distinct private owners. -/
theorem three_le_card_minimalSupportPrivateShiftCycleEdgePairEndpointOwners
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hd : 3 ≤ d) {k l : Fin d} (hkl : k ≠ l) :
    3 ≤ (minimalSupportPrivateShiftCycleEdgePairEndpointOwners
      g hno hmin a k l).card := by
  let bk := minimalSupportPrivateShiftCycleVertex g hno hmin a k
  let uk := minimalSupportTransversalShiftTarget g hno hmin bk
  let bl := minimalSupportPrivateShiftCycleVertex g hno hmin a l
  let ul := minimalSupportTransversalShiftTarget g hno hmin bl
  have hbkbl : bk ≠ bl := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle heq)
  have hbkuk : bk ≠ uk :=
    (minimalSupportTransversalShiftTarget_ne g hno hmin bk).symm
  have hblul : bl ≠ ul :=
    (minimalSupportTransversalShiftTarget_ne g hno hmin bl).symm
  by_cases hukbl : uk = bl
  · have hulbk : ul ≠ bk :=
      minimalSupportPrivateShiftCycle_not_reverse_of_three_le
        g hno hmin a hcycle hd hukbl
    have hthree : ({bk, bl, ul} : Finset ↥B).card = 3 := by
      simp [hbkbl, Ne.symm hulbk, hblul]
    calc
      3 = ({bk, bl, ul} : Finset ↥B).card := hthree.symm
      _ ≤ (minimalSupportPrivateShiftCycleEdgePairEndpointOwners
          g hno hmin a k l).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners, bk]
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
            bl]
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
            bl, ul]
  · have hthree : ({bk, uk, bl} : Finset ↥B).card = 3 := by
      simp [hbkuk, hbkbl, hukbl]
    calc
      3 = ({bk, uk, bl} : Finset ↥B).card := hthree.symm
      _ ≤ (minimalSupportPrivateShiftCycleEdgePairEndpointOwners
          g hno hmin a k l).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners, bk]
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
            bk, uk]
        · simp [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
            bl]

/-- Two distinct members of one edge-label fiber retain distinct sources,
distinct targets, and four endpoint private witnesses omitting the same
external coordinate. -/
theorem minimalSupportPrivateShiftCycle_repeatedLabelPair_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    {z : Fin (m + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hkl : k ≠ l) :
    let bk := minimalSupportPrivateShiftCycleVertex g hno hmin a k
    let bl := minimalSupportPrivateShiftCycleVertex g hno hmin a l
    let uk := minimalSupportTransversalShiftTarget g hno hmin bk
    let ul := minimalSupportTransversalShiftTarget g hno hmin bl
    bk ≠ bl ∧ uk ≠ ul ∧ z ∉ B ∧
      minimalSupportPrivateWitness g h hmin bk z = -1 ∧
      minimalSupportPrivateWitness g h hmin uk z = -1 ∧
      minimalSupportPrivateWitness g h hmin bl z = -1 ∧
      minimalSupportPrivateWitness g h hmin ul z = -1 := by
  dsimp
  have hkLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z k).mp hk
  have hlLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z l).mp hl
  have hkSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a k
  have hlSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a l
  rw [hkLabel] at hkSpec
  rw [hlLabel] at hlSpec
  have hsource : minimalSupportPrivateShiftCycleVertex g hno hmin a k ≠
      minimalSupportPrivateShiftCycleVertex g hno hmin a l := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle heq)
  have htarget :
      minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ≠
        minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleTarget_injective
      g hno hmin a hcycle heq)
  refine ⟨hsource, htarget, ?_⟩
  exact
    ⟨hkSpec.1, hkSpec.2.1, hkSpec.2.2, hlSpec.2.1, hlSpec.2.2⟩

/-- Every endpoint owner of two equal-labelled edges belongs to the private
owner fiber omitting that common label. -/
theorem minimalSupportPrivateShiftCycleEdgePairEndpointOwners_subset_omissionVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} {z : Fin (m + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z) :
    minimalSupportPrivateShiftCycleEdgePairEndpointOwners
        g hno hmin a k l ⊆
      minimalSupportPrivateOmissionVertices g hmin z := by
  have hkLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z k).mp hk
  have hlLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z l).mp hl
  have hkSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a k
  have hlSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a l
  rw [hkLabel] at hkSpec
  rw [hlLabel] at hlSpec
  intro b hb
  simp only [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
    Finset.mem_insert, Finset.mem_singleton] at hb
  apply (mem_minimalSupportPrivateOmissionVertices_iff g hmin z b).mpr
  rcases hb with rfl | rfl | rfl | rfl
  · exact hkSpec.2.1
  · exact hkSpec.2.2
  · exact hlSpec.2.1
  · exact hlSpec.2.2

/-- Two repeated-label edges on a cycle of length at least three force at
least three distinct private owners to omit their common external label. -/
theorem three_le_card_minimalSupportPrivateOmissionVertices_of_repeatedCycleLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hd : 3 ≤ d) {z : Fin (m + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hkl : k ≠ l) :
    3 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card := by
  exact (three_le_card_minimalSupportPrivateShiftCycleEdgePairEndpointOwners
    g hno hmin a hcycle hd hkl).trans
      (Finset.card_le_card
        (minimalSupportPrivateShiftCycleEdgePairEndpointOwners_subset_omissionVertices
          g hg hh hno hmin a hk hl))

/-- Tail-heavy owners among the endpoints of two cycle edges. -/
noncomputable def minimalSupportPrivateShiftCycleEdgePairHeavyEndpointOwners
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k l : Fin d) : Finset ↥B :=
  minimalSupportPrivateShiftCycleEdgePairEndpointOwners
      g hno hmin a k l ∩
    minimalSupportPrivateTailHeavyVertices g h hmin

/-- Three distinct cycle-edge endpoints at critical depth either contain two
tail-heavy private owners or their complementary light pair already forces
the critical crossing bound. -/
theorem critical_privateShiftCycleEdgePair_cross_or_twoHeavyEndpoints
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
    (hd : 3 ≤ d) {k l : Fin d} (hkl : k ≠ l)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      2 ≤ (minimalSupportPrivateShiftCycleEdgePairHeavyEndpointOwners
        g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
          hno hmin a k l).card := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  let S := minimalSupportPrivateShiftCycleEdgePairEndpointOwners
    g hno hmin a k l
  let H := minimalSupportPrivateTailHeavyVertices g h hmin
  let SH := S ∩ H
  by_cases hheavy : 2 ≤ SH.card
  · right
    change 2 ≤ SH.card
    exact hheavy
  · left
    let L := S \ H
    have hScard : 3 ≤ S.card := by
      simpa [S] using
        three_le_card_minimalSupportPrivateShiftCycleEdgePairEndpointOwners
          g hno hmin a hcycle hd hkl
    have hSHle : SH.card ≤ 1 := by omega
    have hpartition := Finset.card_sdiff_add_card_inter S H
    have hLcard : 2 ≤ L.card := by
      change 2 ≤ (S \ H).card
      change (S \ H).card + (S ∩ H).card = S.card at hpartition
      change (S ∩ H).card ≤ 1 at hSHle
      omega
    have hlight : MinimalSupportSelectedPrivateWitnessesTailLight
        g h hmin L := by
      intro b hb e
      have hbDiff : b ∈ S \ H := by simpa [L] using hb
      have hbNotHeavy : b ∉ H := (Finset.mem_sdiff.mp hbDiff).2
      have hbNoHeavy : ¬ ∃ e : Fin n,
          2 ≤ minimalSupportPrivateWitness g h hmin b e.succ := by
        intro hex
        exact hbNotHeavy
          ((mem_minimalSupportPrivateTailHeavyVertices_iff
            g h hmin b).mpr hex)
      by_contra hle
      apply hbNoHeavy
      exact ⟨e, by omega⟩
    exact critical_largeCross_of_two_selectedPrivateTailLight
      hq g hg hmin L hlight hLcard hB

/-- Repeated-label specialization: outside critical crossing, two distinct
equal-labelled edges on a cycle of length at least three expose at least two
tail-heavy endpoint owners, and every endpoint remains in the same external
omission fiber. -/
theorem critical_repeatedPrivateShiftCycleLabel_cross_or_twoHeavyEndpoints
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
    (hd : 3 ≤ d) {z : Fin (n + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hkl : k ≠ l)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      (2 ≤ (minimalSupportPrivateShiftCycleEdgePairHeavyEndpointOwners
          g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
            hno hmin a k l).card ∧
        minimalSupportPrivateShiftCycleEdgePairEndpointOwners
            g hno hmin a k l ⊆
          minimalSupportPrivateOmissionVertices g hmin z ∧
        3 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card) := by
  rcases critical_privateShiftCycleEdgePair_cross_or_twoHeavyEndpoints
      hq g hg hno hmin a hcycle hd hkl hB with hcross | hheavy
  · exact Or.inl hcross
  · exact Or.inr ⟨hheavy,
      minimalSupportPrivateShiftCycleEdgePairEndpointOwners_subset_omissionVertices
        g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a hk hl,
      three_le_card_minimalSupportPrivateOmissionVertices_of_repeatedCycleLabel
        g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a
          hcycle hd hk hl hkl⟩

/-- The two target owners associated with distinct cycle edges. -/
noncomputable def minimalSupportPrivateShiftCycleTargetPair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k l : Fin d) : Finset ↥B :=
  {minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a k),
    minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a l)}

theorem card_minimalSupportPrivateShiftCycleTargetPair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    {k l : Fin d} (hkl : k ≠ l) :
    (minimalSupportPrivateShiftCycleTargetPair
      g hno hmin a k l).card = 2 := by
  have htarget :
      minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ≠
        minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleTarget_injective
      g hno hmin a hcycle heq)
  simp [minimalSupportPrivateShiftCycleTargetPair, htarget]

/-- Cycle-edge pigeonhole specialized to genuine repetition.  Unlike the
owner-fiber endpoint, this preserves the actual pair of cycle edges needed
for the subsequent edge algebra. -/
theorem minimalSupportPrivateShiftCycle_capacity_or_repeatedEdgeLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (L : ℕ) (hcount : L < d) :
    B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        2 ≤ (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
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
    have hlabelsLt : labels.card < L := Nat.lt_of_not_ge hmany
    have hmul : labels.card * 1 <
        (Finset.univ : Finset (Fin d)).card := by
      simp only [Nat.mul_one, Finset.card_univ, Fintype.card_fin]
      exact hlabelsLt.trans hcount
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
    have hfiber : 1 <
        (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
      simpa [label, minimalSupportPrivateShiftCycleEdgeLabelFiber] using hzFiber
    exact ⟨z, hzExternal, by omega⟩

/-- A repeated cycle label at critical depth either supplies the established
crossing bound from its two target owners, or retains a specific tail-heavy
target edge together with the fixed-edge omission trichotomy. -/
theorem critical_repeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
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
    {z : Fin (n + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hkl : k ≠ l)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ j : Fin d, (j = k ∨ j = l) ∧
        j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        minimalSupportTransversalShiftTarget g hno hmin
            (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
          minimalSupportPrivateTailHeavyVertices g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
        (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
            (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
          WitnessExactOmissionTriangle g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
          WitnessThreeDistinctOmissions g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  let S := minimalSupportPrivateShiftCycleTargetPair
    g hno hmin a k l
  by_cases hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S
  · left
    apply critical_largeCross_of_two_selectedPrivateTailLight
      hq g hg hmin S hlight
    · have hcard := card_minimalSupportPrivateShiftCycleTargetPair
        g hno hmin a hcycle hkl
      change 2 ≤ S.card
      rw [hcard]
    · exact hB
  · right
    unfold MinimalSupportSelectedPrivateWitnessesTailLight at hlight
    push Not at hlight
    obtain ⟨u, huS, e, hue⟩ := hlight
    have huHeavy : u ∈ minimalSupportPrivateTailHeavyVertices g h hmin :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff g h hmin u).mpr
        ⟨e, by omega⟩
    have huPair :
        u = minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ∨
          u = minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
      simpa [S, minimalSupportPrivateShiftCycleTargetPair] using huS
    rcases huPair with huk | hul
    · subst u
      refine ⟨k, Or.inl rfl, hk, huHeavy, ?_⟩
      exact
        tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a k)
                huHeavy
    · subst u
      refine ⟨l, Or.inr rfl, hl, huHeavy, ?_⟩
      exact
        tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a l)
                huHeavy

/-- Cardinal form consumed directly after the cycle pigeonhole theorem. -/
theorem critical_largeRepeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
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
    (z : Fin (n + 1))
    (hz : 2 ≤ (minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring))
        hno hmin a d z).card)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ k l : Fin d,
        k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        ∃ j : Fin d, (j = k ∨ j = l) ∧
          j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a d z ∧
          minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
            minimalSupportPrivateTailHeavyVertices g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
          (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
            WitnessExactOmissionTriangle g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessThreeDistinctOmissions g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  have htwo : 1 < (minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring))
        hno hmin a d z).card := by omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp htwo
  rcases critical_repeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
      hq g hg hno hmin a hcycle hk hl hkl hB with hcross | hedge
  · exact Or.inl hcross
  · exact Or.inr ⟨k, l, hkl, hk, hl, hedge⟩

/-- Critical cycle endpoint preserving repeated edges.  If fewer than `d`
external labels are available, then either those labels already fill the
ambient complement, crossing is large, or two equal-labelled edges and one
of their exact tail-heavy targets survive with the fixed-edge algebra. -/
theorem critical_privateShiftCycle_capacity_or_cross_or_repeatedEdgeAlgebra
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
    (L : ℕ) (hcount : L < d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ z : Fin (n + 1), ∃ k l : Fin d,
        z ∉ B ∧ k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        ∃ j : Fin d, (j = k ∨ j = l) ∧
          j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a d z ∧
          minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
            minimalSupportPrivateTailHeavyVertices g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
          (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
            WitnessExactOmissionTriangle g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessThreeDistinctOmissions g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  have hh := half_add_half
    (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
      rw [pow_succ]
      ring)
  rcases minimalSupportPrivateShiftCycle_capacity_or_repeatedEdgeLabel
      g hg hh hno hmin a L hcount with hcapacity | hrepeated
  · exact Or.inl hcapacity
  · obtain ⟨z, hzB, hzcard⟩ := hrepeated
    rcases critical_largeRepeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
        hq g hg hno hmin a hcycle z hzcard hB with hcross | hedge
    · exact Or.inr (Or.inl hcross)
    · obtain ⟨k, l, hkl, hk, hl, halgebra⟩ := hedge
      exact Or.inr (Or.inr ⟨z, k, l, hzB, hkl, hk, hl, halgebra⟩)

end MinModulus
