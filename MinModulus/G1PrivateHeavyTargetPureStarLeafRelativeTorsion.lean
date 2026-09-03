/-
# Relative-permutation torsion on the pure-star leaf cycle

Conjugating the saturated two-permutation recurrence by the center
permutation gives one fixed-point-free relative permutation

    R = P.symm.trans S,
    2 x_i = c + x_(R i).

For `y_i = x_i-c`, this is `y_(R i)=2 y_i`.  A bounded cycle of `R` with
length `ell >= 2` therefore gives

    (2^ell - 1) • y_i = 0.

The annihilator is explicitly odd.  This is the torsion relation anticipated
by the center-incidence roadmap, now extracted in an arbitrary additive
commutative group and attached to the global noncrossing endpoint.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafPermutationAlgebra

namespace MinModulus

open Finset

/-- Iterating a doubling recurrence along a self-map produces powers of two. -/
theorem apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul
    {A : Type*} [AddCommMonoid A] {α : Type*}
    (R : α → α) (y : α → A)
    (hy : ∀ i, y (R i) = 2 • y i) :
    ∀ k i, y (R^[k] i) = (2 ^ k) • y i := by
  intro k
  induction k with
  | zero =>
      intro i
      simp
  | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply', hy, ih]
      simp [pow_succ, mul_comm, smul_smul]

/-- Closing a doubling recurrence after `ell` steps gives annihilation by
the Mersenne coefficient `2^ell-1`. -/
theorem pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
    {A : Type*} [AddCommGroup A] {α : Type*}
    (R : α → α) (y : α → A)
    (hy : ∀ i, y (R i) = 2 • y i)
    {i : α} {ell : ℕ} (hperiod : R^[ell] i = i) :
    (2 ^ ell - 1) • y i = 0 := by
  have hpow : y i = (2 ^ ell) • y i := by
    calc
      y i = y (R^[ell] i) := by rw [hperiod]
      _ = (2 ^ ell) • y i :=
        apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul R y hy ell i
  have hone : 1 ≤ 2 ^ ell := by
    have hpos : 0 < 2 ^ ell := pow_pos (by omega) ell
    omega
  have hsum : (2 ^ ell - 1) • y i + y i = y i := by
    calc
      (2 ^ ell - 1) • y i + y i = ((2 ^ ell - 1) + 1) • y i := by
        rw [add_nsmul, one_nsmul]
      _ = (2 ^ ell) • y i := by rw [Nat.sub_add_cancel hone]
      _ = y i := hpow.symm
  apply add_right_cancel (b := y i)
  simpa using hsum

/-- The relative permutation of two pointwise-distinct permutations is
fixed-point-free. -/
theorem perm_symm_trans_fixedPointFree_of_apply_ne
    {α : Type*} (P S : Equiv.Perm α)
    (hne : ∀ j, P j ≠ S j) :
    ∀ i, (P.symm.trans S) i ≠ i := by
  intro i hfix
  let j := P.symm i
  apply hne j
  have hPj : P j = i := by simp [j]
  calc
    P j = i := hPj
    _ = (P.symm.trans S) i := hfix.symm
    _ = S j := by simp [j]

/-- The exact general torsion endpoint for a two-permutation affine
recurrence.  The relative component length lies between two and `d`. -/
theorem exists_relativePermCycle_oddTorsion
    {A : Type*} [AddCommGroup A] {d : ℕ}
    (x : Fin d → A) (c : A) (P S : Equiv.Perm (Fin d))
    (hd : 2 ≤ d)
    (hne : ∀ j, P j ≠ S j)
    (hrel : ∀ j, (2 : ℤ) • x (P j) = c + x (S j)) :
    ∃ i : Fin d, ∃ ell : ℕ,
      2 ≤ ell ∧ ell ≤ d ∧
      (P.symm.trans S)^[ell] i = i ∧
      Odd (2 ^ ell - 1) ∧
      (2 ^ ell - 1) • (x i - c) = 0 := by
  let R : Equiv.Perm (Fin d) := P.symm.trans S
  have hRne : ∀ i, R i ≠ i :=
    perm_symm_trans_fixedPointFree_of_apply_ne P S hne
  obtain ⟨i, ell, hellTwo, hellCard, hperiod⟩ :=
    exists_bounded_cycle_of_fixedPointFree R ⟨0, by omega⟩ hRne
  let y : Fin d → A := fun j ↦ x j - c
  have hRrel : ∀ i, (2 : ℤ) • x i = c + x (R i) := by
    intro i
    simpa [R] using hrel (P.symm i)
  have hy : ∀ i, y (R i) = 2 • y i := by
    intro i
    have hi := hRrel i
    rw [two_zsmul] at hi
    dsimp [y]
    rw [two_nsmul]
    calc
      x (R i) - c = (c + x (R i)) - (c + c) := by abel
      _ = (x i + x i) - (c + c) := by rw [← hi]
      _ = (x i - c) + (x i - c) := by abel
  have htorsion : (2 ^ ell - 1) • (x i - c) = 0 := by
    exact pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
      R y hy hperiod
  have hellPos : 0 < ell := by omega
  have hellDecomp : ell = (ell - 1) + 1 := by omega
  have hpowEq : 2 ^ ell = 2 * 2 ^ (ell - 1) := by
    calc
      2 ^ ell = 2 ^ ((ell - 1) + 1) := by rw [← hellDecomp]
      _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ, mul_comm]
  have hodd : Odd (2 ^ ell - 1) := by
    refine ⟨2 ^ (ell - 1) - 1, ?_⟩
    rw [hpowEq]
    have hpowPos : 1 ≤ 2 ^ (ell - 1) := by
      have hpos : 0 < 2 ^ (ell - 1) := pow_pos (by omega) (ell - 1)
      omega
    omega
  exact ⟨i, ell, hellTwo, by simpa using hellCard,
    hperiod, hodd, htorsion⟩

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Saturated pure-star algebra enriched with one bounded relative component
and its explicit odd torsion relation. -/
def PureEdgeStarLeafRelativeTorsionAlgebra
    (g : Fin (m + 1) → G) (h : G) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  ∃ P S : Equiv.Perm (Fin d),
    (∀ j : Fin d,
      P j ≠ j ∧ P j ≠ S j ∧
      center j = leaf (P j) ∧
      (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
      (2 : ℤ) • g (leaf (P j)) =
        h + g r + g (leaf (S j))) ∧
    (∑ j, g (leaf j)) = d • (h + g r) ∧
    ∃ i : Fin d, ∃ ell : ℕ,
      2 ≤ ell ∧ ell ≤ d ∧
      (P.symm.trans S)^[ell] i = i ∧
      Odd (2 ^ ell - 1) ∧
      (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0

omit [DecidableEq G] in
/-- Every saturated pure-star permutation algebra contains a bounded
relative-permutation component with explicit odd torsion. -/
theorem PureEdgeStarLeafPermutationAlgebra.relativeTorsion
    (g : Fin (m + 1) → G) {h : G}
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center) :
    PureEdgeStarLeafRelativeTorsionAlgebra g h r T a d center := by
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  obtain ⟨P, S, hlocal, hsum⟩ := halg
  have htorsion := exists_relativePermCycle_oddTorsion
    (fun j ↦ g (leaf j)) (h + g r) P S hcycle.1
      (fun j ↦ (hlocal j).2.1) (fun j ↦ (hlocal j).2.2.2.2)
  exact ⟨P, S, hlocal, hsum, htorsion⟩

/-- Global pure-star outcome after relative-permutation analysis: both
nonsaturated branches pay capacity, while saturation produces odd torsion. -/
def PureEdgeStarLeafRelativeTorsionOutcome
    (g : Fin (m + 1) → G) (h : G) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    PureEdgeStarLeafRelativeTorsionAlgebra g h r T a d center

omit [DecidableEq G] in
/-- Refine the saturated branch of the global permutation outcome to its
bounded relative-cycle odd-torsion relation. -/
theorem pureEdgeStarLeafCycle_relativeTorsionOutcome_of_permutationOutcome
    (g : Fin (m + 1) → G) {h : G}
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafPermutationOutcome g h r T a d center) :
    PureEdgeStarLeafRelativeTorsionOutcome g h r T a d center := by
  rcases hout with hcap | hmixed | halg
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr (halg.relativeTorsion g r T center hcycle))

/-- Global noncrossing endpoint carrying an explicit odd-torsion relation in
the only branch that avoids both coordinate-capacity alternatives. -/
theorem exists_minimal_pureEdgeStarLeafCycle_relativeTorsionOutcome
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
          (∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1))) ∧
          PureEdgeStarLeafRelativeTorsionOutcome g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_permutationOutcome
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_relativeTorsionOutcome_of_permutationOutcome
      g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
