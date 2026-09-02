/-
# Minimal private/avoiding cycles on the support transversal

The canonical transversal successor is fixed-point-free, but an arbitrary
repeat need not display a simple cycle.  Minimize its positive period.  The
vertices in one period are then pairwise distinct.  Starting at the actual
heavy private owner, a bounded path reaches either a rigid two-cycle or a
vertex-simple cycle of length at least three.
-/
import MinModulus.G1PrivateHeavyTransversalCycle

namespace MinModulus

open Finset

/-- A positive period which is minimal among all positive return times. -/
def IsMinimalFixedPointFreeCycle
    {α : Type*} (T : α → α) (a : α) (d : ℕ) : Prop :=
  2 ≤ d ∧ T^[d] a = a ∧
    ∀ e : ℕ, 0 < e → T^[e] a = a → d ≤ e

/-- Any displayed positive period of a fixed-point-free self-map contains a
least positive period, no larger than the displayed one. -/
theorem exists_minimalFixedPointFreeCycle_of_period
    {α : Type*} (T : α → α) (a : α)
    (hne : ∀ x, T x ≠ x)
    {D : ℕ} (hDpos : 0 < D) (hDperiod : T^[D] a = a) :
    ∃ d : ℕ, d ≤ D ∧ IsMinimalFixedPointFreeCycle T a d := by
  classical
  let hex : ∃ e : ℕ, 0 < e ∧ T^[e] a = a :=
    ⟨D, hDpos, hDperiod⟩
  let d := Nat.find hex
  have hdspec : 0 < d ∧ T^[d] a = a := Nat.find_spec hex
  have hdne : d ≠ 1 := by
    intro hd
    have hfix : T a = a := by
      simpa [hd, Function.iterate_succ_apply] using hdspec.2
    exact hne a hfix
  have hdle : d ≤ D := Nat.find_min' hex ⟨hDpos, hDperiod⟩
  exact ⟨d, hdle, by
    refine ⟨by omega, hdspec.2, ?_⟩
    intro e he heperiod
    exact Nat.find_min' hex ⟨he, heperiod⟩⟩

/-- The vertices in one least positive period are pairwise distinct. -/
theorem minimalFixedPointFreeCycle_iterates_injective
    {α : Type*} (T : α → α) {a : α} {d : ℕ}
    (hmin : IsMinimalFixedPointFreeCycle T a d) :
    Function.Injective (fun k : Fin d ↦ T^[k.val] a) := by
  intro i j hijEq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · have hsmall := iterate_sub_is_period_of_eq_of_period T
      hmin.2.1 (Nat.le_of_lt i.isLt) hij.le hijEq
    have hleast := hmin.2.2 (j.val - i.val)
      (Nat.sub_pos_of_lt hij) hsmall
    omega
  · have hsmall := iterate_sub_is_period_of_eq_of_period T
      hmin.2.1 (Nat.le_of_lt j.isLt) hji.le hijEq.symm
    have hleast := hmin.2.2 (i.val - j.val)
      (Nat.sub_pos_of_lt hji) hsmall
    omega

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Named proposition for the private/avoiding witness labels on one
canonical transversal edge. -/
def MinimalSupportTransversalShiftEdgePackage
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) : Prop :=
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let c := minimalSupportPrivateWitness g h hmin b
  let r := minimalSupportAvoidingWitness g hno b
  u ≠ b ∧ Witness g h c ∧ c b ≠ 0 ∧ c u = 0 ∧
    Witness g h r ∧ r b = 0 ∧ r u ≠ 0

theorem minimalSupportTransversalShiftEdgePackage_holds
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    MinimalSupportTransversalShiftEdgePackage g hno hmin b :=
  minimalSupportTransversalShift_edgePackage g hno hmin b

/-- A period-two orbit is a rigid crossed-incidence rectangle: its two
distinct vertices carry both canonical private/avoiding edge packages, and
the two selected arrows point back to one another. -/
theorem minimalSupportTransversalShift_twoCyclePackage
    (g : Fin m → G) {h : G}
    (hno : ¬ ∃ e : Fin m, ∀ r : Fin m → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B})
    (hcycle :
      (minimalSupportTransversalShiftTarget g hno hmin)^[2] b = b) :
    let T := minimalSupportTransversalShiftTarget g hno hmin
    T (T b) = b ∧ T b ≠ b ∧
      MinimalSupportTransversalShiftEdgePackage g hno hmin b ∧
      MinimalSupportTransversalShiftEdgePackage g hno hmin (T b) := by
  dsimp
  have hback :
      minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) = b := by
    simpa [Function.iterate_succ_apply] using hcycle
  exact ⟨hback,
    minimalSupportTransversalShiftTarget_ne g hno hmin b,
    minimalSupportTransversalShiftEdgePackage_holds g hno hmin b,
    minimalSupportTransversalShiftEdgePackage_holds g hno hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)⟩

/-- Starting at the heavy private owner, a bounded canonical shift path
reaches a least-period, vertex-simple cycle.  Its period is explicitly split
between the rigid two-cycle and the length-at-least-three regime. -/
theorem
    ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_ownerPathToSimpleShiftCycle
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N}
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := N) (M := M) (K := K) g) :
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
      ∃ owner : {b : Fin (n + 1) // b ∈ B},
      ∃ i d : ℕ,
        2 ≤ d ∧ i + d ≤ B.card ∧
        let T := minimalSupportTransversalShiftTarget g hres.1 hmin
        T^[d] (T^[i] owner) = T^[i] owner ∧
          Function.Injective (fun k : Fin d ↦ T^[k.val] (T^[i] owner)) ∧
          (d = 2 ∨ 3 ≤ d) := by
  obtain ⟨hno, _t, _qv, B, hmin, _ht, _hqv, _hBsub, _hrec, _hBcard,
    owner, _c, _k, _escape, _hc, _hcowner, _hprivate, _hk, _hkLocation,
    _hescape, _hescapeLocation, _hownerCoincide⟩ := hres
  let T := minimalSupportTransversalShiftTarget g hno hmin
  obtain ⟨i, D, hDtwo, hiDcard, hrepeat⟩ :=
    exists_bounded_eventualCycle_of_fixedPointFree T owner
      (minimalSupportTransversalShiftTarget_ne g hno hmin)
  have hDperiod : T^[D] (T^[i] owner) = T^[i] owner := by
    calc
      T^[D] (T^[i] owner) = T^[D + i] owner :=
        (Function.iterate_add_apply T D i owner).symm
      _ = T^[i + D] owner :=
        congrArg (fun k : ℕ ↦ T^[k] owner) (Nat.add_comm D i)
      _ = T^[i] owner := hrepeat
  obtain ⟨d, hdD, hminimal⟩ :=
    exists_minimalFixedPointFreeCycle_of_period T (T^[i] owner)
      (minimalSupportTransversalShiftTarget_ne g hno hmin)
      (by omega) hDperiod
  rcases hminimal with ⟨hdtwo, hdperiod, hdleast⟩
  have hinj := minimalFixedPointFreeCycle_iterates_injective T
    ⟨hdtwo, hdperiod, hdleast⟩
  have hiDcard' : i + D ≤ B.card := by simpa using hiDcard
  exact ⟨B, hmin, owner, i, d, hdtwo, by omega, hdperiod,
    hinj, by omega⟩

end MinModulus
