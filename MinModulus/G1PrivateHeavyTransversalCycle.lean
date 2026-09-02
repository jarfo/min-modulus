/-
# A cycle of private/avoiding shifts on a minimal support transversal

The previous private-heavy refinement extracted one internal shift at the
heavy witness's owner.  Minimality supplies a private half witness at every
vertex of the same transversal, while failure of common touch supplies a
witness vanishing there.  Choosing a transversal hit of each avoiding
witness defines a fixed-point-free self-map of the finite deletion set.
Consequently the entire residual carries a directed cycle, with a private
and an avoiding witness labelling every edge.
-/
import MinModulus.G1PrivateHeavyTransversalShift

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Failure of common touch supplies a witness vanishing at any prescribed
coordinate. -/
theorem exists_supportWitness_zero_at_of_noCommonTouch
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    (b : Fin m) :
    ∃ r : Fin m → ℤ, Witness g h r ∧ r b = 0 := by
  by_contra hnone
  apply hno
  refine ⟨b, ?_⟩
  intro r hr
  by_contra hrb
  exact hnone ⟨r, hr, hrb⟩

/-- A canonical half witness avoiding a prescribed vertex of a minimal
support transversal. -/
noncomputable def minimalSupportAvoidingWitness
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (b : {i : Fin m // i ∈ B}) : Fin m → ℤ :=
  Classical.choose
    (exists_supportWitness_zero_at_of_noCommonTouch g hno b)

theorem minimalSupportAvoidingWitness_isWitness
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (b : {i : Fin m // i ∈ B}) :
    Witness g h (minimalSupportAvoidingWitness g hno b) :=
  (Classical.choose_spec
    (exists_supportWitness_zero_at_of_noCommonTouch g hno b)).1

theorem minimalSupportAvoidingWitness_eq_zero
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (b : {i : Fin m // i ∈ B}) :
    minimalSupportAvoidingWitness g hno b b = 0 :=
  (Classical.choose_spec
    (exists_supportWitness_zero_at_of_noCommonTouch g hno b)).2

/-- Choose one nonzero transversal hit of the avoiding witness at `b`. -/
noncomputable def minimalSupportTransversalShiftTarget
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) : {i : Fin m // i ∈ B} :=
  ⟨Classical.choose
      (hmin.1 (minimalSupportAvoidingWitness g hno b)
        (minimalSupportAvoidingWitness_isWitness g hno b)),
    (Classical.choose_spec
      (hmin.1 (minimalSupportAvoidingWitness g hno b)
        (minimalSupportAvoidingWitness_isWitness g hno b))).1⟩

theorem minimalSupportAvoidingWitness_target_ne_zero
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    minimalSupportAvoidingWitness g hno b
        (minimalSupportTransversalShiftTarget g hno hmin b) ≠ 0 :=
  (Classical.choose_spec
    (hmin.1 (minimalSupportAvoidingWitness g hno b)
      (minimalSupportAvoidingWitness_isWitness g hno b))).2

/-- The chosen shift has no fixed point: its avoiding witness is zero at the
source and nonzero at the target. -/
theorem minimalSupportTransversalShiftTarget_ne
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    minimalSupportTransversalShiftTarget g hno hmin b ≠ b := by
  intro htarget
  have hval := congrArg Subtype.val htarget
  have hnz := minimalSupportAvoidingWitness_target_ne_zero
    g hno hmin b
  have hz := minimalSupportAvoidingWitness_eq_zero g hno b
  rw [hval] at hnz
  exact hnz hz

/-- The canonical private witness at the source vanishes at the selected
target. -/
theorem minimalSupportPrivateWitness_shiftTarget_eq_zero
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    minimalSupportPrivateWitness g h hmin b
        (minimalSupportTransversalShiftTarget g hno hmin b) = 0 := by
  apply minimalSupportPrivateWitness_eq_zero_of_ne g h hmin b
    (minimalSupportTransversalShiftTarget g hno hmin b).property
  intro hval
  exact minimalSupportTransversalShiftTarget_ne g hno hmin b
    (Subtype.ext hval)

/-- Every source vertex has a labelled internal shift: its private witness
is nonzero only at the source inside `B`, while an avoiding witness is zero at
the source and nonzero at the selected distinct target. -/
theorem minimalSupportTransversalShift_edgePackage
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    let u := minimalSupportTransversalShiftTarget g hno hmin b
    let c := minimalSupportPrivateWitness g h hmin b
    let r := minimalSupportAvoidingWitness g hno b
    u ≠ b ∧ Witness g h c ∧ c b ≠ 0 ∧ c u = 0 ∧
      Witness g h r ∧ r b = 0 ∧ r u ≠ 0 := by
  dsimp
  exact ⟨minimalSupportTransversalShiftTarget_ne g hno hmin b,
    minimalSupportPrivateWitness_isWitness g h hmin b,
    minimalSupportPrivateWitness_ne_zero g h hmin b,
    minimalSupportPrivateWitness_shiftTarget_eq_zero g hno hmin b,
    minimalSupportAvoidingWitness_isWitness g hno b,
    minimalSupportAvoidingWitness_eq_zero g hno b,
    minimalSupportAvoidingWitness_target_ne_zero g hno hmin b⟩

/-- A fixed-point-free self-map of a nonempty finite type has a directed
cycle of length between two and the size of the type. -/
theorem exists_bounded_cycle_of_fixedPointFree
    {α : Type*} [Fintype α]
    (T : α → α) (a₀ : α) (hne : ∀ a, T a ≠ a) :
    ∃ a : α, ∃ d : ℕ,
      2 ≤ d ∧ d ≤ Fintype.card α ∧ T^[d] a = a := by
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨i, j, hijne, hijEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card α + 1) ↦ T^[k.val] a₀) hcard
  have hvalne : i.val ≠ j.val := by
    intro hval
    exact hijne (Fin.ext hval)
  have horient : ∀ {i j : Fin (Fintype.card α + 1)},
      i.val < j.val → T^[i.val] a₀ = T^[j.val] a₀ →
      ∃ a : α, ∃ d : ℕ,
        2 ≤ d ∧ d ≤ Fintype.card α ∧ T^[d] a = a := by
    intro i j hij heq
    let a := T^[i.val] a₀
    let d := j.val - i.val
    have hadd : i.val + d = j.val := Nat.add_sub_of_le hij.le
    have hcycle : T^[d] a = a := by
      calc
        T^[d] a = T^[d + i.val] a₀ :=
          (Function.iterate_add_apply T d i.val a₀).symm
        _ = T^[i.val + d] a₀ := by rw [Nat.add_comm]
        _ = T^[j.val] a₀ := by rw [hadd]
        _ = a := heq.symm
    have hdpos : 0 < d := Nat.sub_pos_of_lt hij
    have hdne : d ≠ 1 := by
      intro hd
      have hfix : T a = a := by
        simpa [hd, Function.iterate_succ_apply] using hcycle
      exact hne a hfix
    have hjle : j.val ≤ Fintype.card α := by
      omega
    refine ⟨a, d, by omega, ?_, hcycle⟩
    omega
  rcases Nat.lt_or_gt_of_ne hvalne with hij | hji
  · exact horient hij hijEq
  · exact horient hji hijEq.symm

/-- Starting from a specified vertex, a fixed-point-free self-map reaches a
cycle after a bounded preperiod.  The whole first repeat occurs within the
first `card α` steps. -/
theorem exists_bounded_eventualCycle_of_fixedPointFree
    {α : Type*} [Fintype α]
    (T : α → α) (a₀ : α) (hne : ∀ a, T a ≠ a) :
    ∃ i d : ℕ,
      2 ≤ d ∧ i + d ≤ Fintype.card α ∧
        T^[i + d] a₀ = T^[i] a₀ := by
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨a, b, habne, habEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card α + 1) ↦ T^[k.val] a₀) hcard
  have hvalne : a.val ≠ b.val := by
    intro hval
    exact habne (Fin.ext hval)
  have horient : ∀ {a b : Fin (Fintype.card α + 1)},
      a.val < b.val → T^[a.val] a₀ = T^[b.val] a₀ →
      ∃ i d : ℕ,
        2 ≤ d ∧ i + d ≤ Fintype.card α ∧
          T^[i + d] a₀ = T^[i] a₀ := by
    intro a b hab heq
    let d := b.val - a.val
    have hadd : a.val + d = b.val := Nat.add_sub_of_le hab.le
    have hcycle : T^[d] (T^[a.val] a₀) = T^[a.val] a₀ := by
      calc
        T^[d] (T^[a.val] a₀) = T^[d + a.val] a₀ :=
          (Function.iterate_add_apply T d a.val a₀).symm
        _ = T^[a.val + d] a₀ := by rw [Nat.add_comm]
        _ = T^[b.val] a₀ := by rw [hadd]
        _ = T^[a.val] a₀ := heq.symm
    have hdpos : 0 < d := Nat.sub_pos_of_lt hab
    have hdne : d ≠ 1 := by
      intro hd
      have hfix : T (T^[a.val] a₀) = T^[a.val] a₀ := by
        simpa [hd, Function.iterate_succ_apply] using hcycle
      exact hne (T^[a.val] a₀) hfix
    have hble : b.val ≤ Fintype.card α := by
      omega
    refine ⟨a.val, d, by omega, ?_, ?_⟩
    · omega
    · simpa [hadd] using heq.symm
  rcases Nat.lt_or_gt_of_ne hvalne with hab | hba
  · exact horient hab habEq
  · exact horient hba habEq.symm

/-- Every nonempty minimal support transversal under no common touch carries
a bounded directed cycle of the canonical private/avoiding shifts. -/
theorem exists_minimalSupportTransversalShiftCycle
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hB : B.Nonempty) :
    ∃ b : {i : Fin m // i ∈ B}, ∃ d : ℕ,
      2 ≤ d ∧ d ≤ B.card ∧
        (minimalSupportTransversalShiftTarget g hno hmin)^[d] b = b := by
  obtain ⟨b₀, hb₀⟩ := hB
  simpa using
    (exists_bounded_cycle_of_fixedPointFree
      (minimalSupportTransversalShiftTarget g hno hmin) ⟨b₀, hb₀⟩
      (minimalSupportTransversalShiftTarget_ne g hno hmin))

/-- The avoidance/escape-enriched private-heavy residual therefore contains
a bounded cycle on its retained minimal transversal.  Every edge of this
cycle has the witness package supplied by
`minimalSupportTransversalShift_edgePackage`. -/
theorem ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_shiftCycle
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g) :
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
      2 ≤ B.card ∧
      ∃ b : {i : Fin (n + 1) // i ∈ B}, ∃ d : ℕ,
        2 ≤ d ∧ d ≤ B.card ∧
          (minimalSupportTransversalShiftTarget g hres.1 hmin)^[d] b = b := by
  obtain ⟨hno, _t, _qv, B, hmin, _ht, _hqv, _hBsub, _hrec, hBcard,
    _owner, _c, _k, _i, _hc, _hcowner, _hprivate, _hk, _hkLocation,
    _hi, _hiLocation, _hownerCoincide⟩ := hres
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨B, hmin, hBcard,
    exists_minimalSupportTransversalShiftCycle g hno hmin hB⟩

/-- More sharply, the orbit beginning at the actual heavy private owner
reaches such a cycle within `B.card` steps.  Hence the cycle is connected to
the heavy/escape-labelled part of the residual by a canonical shift path. -/
theorem
    ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_ownerPathToShiftCycle
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g) :
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
      ∃ owner : {b : Fin (n + 1) // b ∈ B},
      ∃ i d : ℕ,
        2 ≤ d ∧ i + d ≤ B.card ∧
          (minimalSupportTransversalShiftTarget g hres.1 hmin)^[i + d] owner =
            (minimalSupportTransversalShiftTarget g hres.1 hmin)^[i] owner := by
  obtain ⟨hno, _t, _qv, B, hmin, _ht, _hqv, _hBsub, _hrec, _hBcard,
    owner, _c, _k, _escape, _hc, _hcowner, _hprivate, _hk, _hkLocation,
    _hescape, _hescapeLocation, _hownerCoincide⟩ := hres
  have hcycle :=
    exists_bounded_eventualCycle_of_fixedPointFree
      (minimalSupportTransversalShiftTarget g hno hmin) owner
      (minimalSupportTransversalShiftTarget_ne g hno hmin)
  exact ⟨B, hmin, owner, by simpa using hcycle⟩

end MinModulus
