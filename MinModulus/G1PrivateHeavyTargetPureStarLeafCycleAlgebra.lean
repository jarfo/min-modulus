/-
# Center algebra on a pure-star leaf cycle

Every edge of the noncrossing leaf cycle is a pure half-witness.  Its center,
the star, its source leaf, and its successor leaf are pairwise distinct, and
the witness equation is the affine midpoint relation

    2 g(center) = h + g(star) + g(successor).

After minimizing the cycle period, successor leaves are distinct.  Validity
then makes the selected centers distinct as well: equal centers would make
the affine relations identify the successor tuple entries.  This file
packages the leaf cycle with its injective center family and exact recurrence.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafCycle

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- On a least-period cycle, applying the self-map to the displayed iterates
is still injective. -/
theorem minimalFixedPointFreeCycle_apply_iterates_injective
    {α : Type*} (T : α → α) {a : α} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d) :
    Function.Injective (fun k : Fin d ↦ T (T^[k.val] a)) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hcycle.1
  have hrecover : ∀ k : Fin d,
      (T^[d - 1]) (T (T^[k.val] a)) = T^[k.val] a := by
    intro k
    have hperiod : (T^[d]) (T^[k.val] a) = T^[k.val] a := by
      calc
        (T^[d]) (T^[k.val] a) = T^[d + k.val] a :=
          (Function.iterate_add_apply T d k.val a).symm
        _ = T^[k.val + d] a := by rw [Nat.add_comm]
        _ = (T^[k.val]) (T^[d] a) :=
          Function.iterate_add_apply T k.val d a
        _ = T^[k.val] a := by rw [hcycle.2.1]
    calc
      (T^[d - 1]) (T (T^[k.val] a)) =
          (T^[(d - 1) + 1]) (T^[k.val] a) :=
        (Function.iterate_succ_apply T (d - 1) (T^[k.val] a)).symm
      _ = (T^[d]) (T^[k.val] a) := by
        rw [Nat.sub_add_cancel hdpos]
      _ = T^[k.val] a := hperiod
  intro k l hkl
  apply minimalFixedPointFreeCycle_iterates_injective T hcycle
  calc
    T^[k.val] a = (T^[d - 1]) (T (T^[k.val] a)) := (hrecover k).symm
    _ = (T^[d - 1]) (T (T^[l.val] a)) := congrArg (T^[d - 1]) hkl
    _ = T^[l.val] a := hrecover l

omit [DecidableEq G] in
/-- Exact four-coordinate geometry and affine relation on one pure-star leaf
transition. -/
theorem PureEdgeStarLeafTransitionAt.exists_center_affine
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    {r w x : Fin (m + 1)}
    (htrans : PureEdgeStarLeafTransitionAt g h hno r w x) :
    ∃ e : Fin m,
      e.succ ≠ r ∧ e.succ ≠ w ∧ e.succ ≠ x ∧
      x ≠ r ∧ x ≠ w ∧
      (2 : ℤ) • g e.succ = h + g r + g x := by
  obtain ⟨e, hxr, hxw, her, hex, hd, homit, heTwo, _hshape⟩ := htrans
  have hew : e.succ ≠ w := by
    intro hew
    have hdw := supportAvoidingWitnessAt_eq_zero g hno w
    rw [hew, hdw] at heTwo
    omega
  have homit' : ∀ a, supportAvoidingWitnessAt g hno w a = -1 ↔
      a = r ∨ a = x := by
    intro a
    simpa using homit a
  have haffine := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hd r x e.succ (Ne.symm hxr) homit' her hex heTwo
  exact ⟨e, her, hew, hex, hxr, hxw, haffine⟩

omit [DecidableEq G] in
/-- A least-period leaf cycle has an injective family of pure-edge centers,
each satisfying the exact successor affine relation and avoiding the star,
source leaf, and successor leaf. -/
theorem pureEdgeStarLeafCycle_exists_injectiveCenters
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G}
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (hT : ∀ w : ↥(witnessPureEdgeStarLeaves g h r),
      PureEdgeStarLeafTransitionAt g h hno r
        (w : Fin (m + 1)) (T w : Fin (m + 1)))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d) :
    ∃ center : Fin d → Fin (m + 1),
      Function.Injective center ∧
      ∀ j : Fin d,
        center j ≠ r ∧
        center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
        center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
        (2 : ℤ) • g (center j) =
          h + g r + g (T (T^[j.val] a) : Fin (m + 1)) := by
  classical
  let v : Fin d → ↥(witnessPureEdgeStarLeaves g h r) :=
    fun j ↦ T^[j.val] a
  have hgeom : ∀ j : Fin d, ∃ e : Fin m,
      e.succ ≠ r ∧ e.succ ≠ (v j : Fin (m + 1)) ∧
      e.succ ≠ (T (v j) : Fin (m + 1)) ∧
      (2 : ℤ) • g e.succ = h + g r + g (T (v j) : Fin (m + 1)) := by
    intro j
    obtain ⟨e, her, hew, hex, _hxr, _hxw, haffine⟩ :=
      (hT (v j)).exists_center_affine g hno
    exact ⟨e, her, hew, hex, haffine⟩
  let center : Fin d → Fin (m + 1) :=
    fun j ↦ (Classical.choose (hgeom j)).succ
  have hcenterSpec : ∀ j : Fin d,
      center j ≠ r ∧ center j ≠ (v j : Fin (m + 1)) ∧
      center j ≠ (T (v j) : Fin (m + 1)) ∧
      (2 : ℤ) • g (center j) =
        h + g r + g (T (v j) : Fin (m + 1)) := by
    intro j
    exact Classical.choose_spec (hgeom j)
  have htargetInjective : Function.Injective (fun j : Fin d ↦ T (v j)) :=
    minimalFixedPointFreeCycle_apply_iterates_injective T hcycle
  have hcenterInjective : Function.Injective center := by
    intro j l hjl
    apply htargetInjective
    apply Subtype.ext
    apply validTuple_injective g hg
    have hj := (hcenterSpec j).2.2.2
    have hl := (hcenterSpec l).2.2.2
    calc
      g (T (v j) : Fin (m + 1)) =
          (2 : ℤ) • g (center j) - h - g r := by rw [hj]; abel
      _ = (2 : ℤ) • g (center l) - h - g r := by rw [hjl]
      _ = g (T (v l) : Fin (m + 1)) := by rw [hl]; abel
  exact ⟨center, hcenterInjective, by
    intro j
    simpa [v] using hcenterSpec j⟩

/-- Global noncrossing endpoint: the finite star-leaf self-map can be reduced
to least period and equipped with an injective center family satisfying the
exact affine recurrence. -/
theorem exists_minimal_pureEdgeStarLeafCycle_with_injectiveCenters
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (q : ReducedSubsetSumCollision g h)
    (hqCanonical : q ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs q.val.1 q.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((q, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        ∃ center : Fin d → Fin (m + 1),
          d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          IsMinimalFixedPointFreeCycle T a d ∧
          Function.Injective center ∧
          ∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1)) := by
  obtain ⟨T, hTne, hT, a, D, hDtwo, hDcard, hDperiod⟩ :=
    exists_bounded_pureEdgeStarLeafCycle_of_no_three_of_no_canonicalCross
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross hL
  obtain ⟨d, hdD, hcycle⟩ :=
    exists_minimalFixedPointFreeCycle_of_period T a hTne
      (by omega : 0 < D) hDperiod
  obtain ⟨center, hcenterInjective, hcenterSpec⟩ :=
    pureEdgeStarLeafCycle_exists_injectiveCenters
      g hg hno r T hT hcycle
  exact ⟨T, a, d, center, hdD.trans hDcard, hcycle,
    hcenterInjective, hcenterSpec⟩

end MinModulus
