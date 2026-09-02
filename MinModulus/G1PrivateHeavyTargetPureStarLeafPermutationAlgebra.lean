/-
# Permutation algebra on the saturated pure-star leaf cycle

In the saturated incidence branch every coefficient-two center is a cycle
leaf.  The original cycle successor also permutes the least-period leaf
indices.  Thus the local midpoint equations compare two permutations `P`
and `S` of the same finite set:

    2 g(leaf (P j)) = c + g(leaf (S j)),
    c = h + g(star).

Here `P j` is neither `j` nor `S j`.  Summing over all indices cancels both
permutations and yields the global identity

    sum_j g(leaf j) = d • (h + g(star)).
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafCycleIncidence

namespace MinModulus

open Finset

/-- The successor on a least-period orbit induces a permutation of the
displayed orbit indices. -/
theorem minimalFixedPointFreeCycle_exists_successorIndexPerm
    {α : Type*} (T : α → α) {a : α} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d) :
    ∃ S : Equiv.Perm (Fin d),
      ∀ j : Fin d, T (T^[j.val] a) = T^[(S j).val] a := by
  let source : Fin d → α := fun j ↦ T^[j.val] a
  let target : Fin d → α := fun j ↦ T (T^[j.val] a)
  have htarget : Function.Injective target :=
    minimalFixedPointFreeCycle_apply_iterates_injective T hcycle
  have hall : ∀ j, target j ∈ Set.range source := by
    intro j
    by_cases hj : j.val + 1 < d
    · refine ⟨⟨j.val + 1, hj⟩, ?_⟩
      change T^[j.val + 1] a = T (T^[j.val] a)
      exact Function.iterate_succ_apply' T j.val a
    · have hjd : j.val + 1 = d := by omega
      refine ⟨⟨0, by omega⟩, ?_⟩
      change a = T (T^[j.val] a)
      rw [← Function.iterate_succ_apply' T j.val a,
        show j.val.succ = d by omega, hcycle.2.1]
  obtain ⟨S, hS⟩ := exists_rangeIndexPerm target source htarget hall
  exact ⟨S, hS⟩

/-- Summing a recurrence that compares two permutations removes both index
maps and leaves an exact global affine identity. -/
theorem sum_eq_card_nsmul_of_two_zsmul_perm_eq_const_add_perm
    {A : Type*} [AddCommGroup A] {d : ℕ}
    (x : Fin d → A) (c : A) (P S : Equiv.Perm (Fin d))
    (hrel : ∀ j, (2 : ℤ) • x (P j) = c + x (S j)) :
    (∑ j, x j) = d • c := by
  have hsum : (∑ j, (2 : ℤ) • x (P j)) =
      ∑ j, (c + x (S j)) := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact hrel j
  rw [← Finset.smul_sum, Equiv.sum_comp P x, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Equiv.sum_comp S x] at hsum
  rw [show (2 : ℤ) • (∑ j, x j) = (∑ j, x j) + ∑ j, x j by
    simp [two_zsmul]] at hsum
  exact add_right_cancel hsum

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Fully indexed algebra in the saturated center-incidence branch. -/
def PureEdgeStarLeafPermutationAlgebra
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
    (∑ j, g (leaf j)) = d • (h + g r)

omit [DecidableEq G] in
/-- The saturated center permutation and the induced successor permutation
satisfy a pointwise two-permutation recurrence and its summed identity. -/
theorem pureEdgeStarLeafCycle_saturatedPermutationAlgebra
    (g : Fin (m + 1) → G) {h : G}
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d))
    (hP : ∀ j : Fin d,
      P j ≠ j ∧
      (T^[(P j).val] a : Fin (m + 1)) ≠
        (T (T^[j.val] a) : Fin (m + 1)) ∧
      center j = (T^[(P j).val] a : Fin (m + 1)) ∧
      (2 : ℤ) • g (center j) =
        h + g r + g (T (T^[j.val] a) : Fin (m + 1))) :
    PureEdgeStarLeafPermutationAlgebra g h r T a d center := by
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  obtain ⟨S, hSsub⟩ :=
    minimalFixedPointFreeCycle_exists_successorIndexPerm T hcycle
  have hS : ∀ j : Fin d,
      (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) := by
    intro j
    exact congrArg Subtype.val (hSsub j)
  have hrel : ∀ j : Fin d,
      (2 : ℤ) • g (leaf (P j)) = h + g r + g (leaf (S j)) := by
    intro j
    calc
      (2 : ℤ) • g (leaf (P j)) = (2 : ℤ) • g (center j) := by
        rw [(hP j).2.2.1]
      _ = h + g r + g (T (T^[j.val] a) : Fin (m + 1)) :=
        (hP j).2.2.2
      _ = h + g r + g (leaf (S j)) := by rw [hS j]
  have hsum : (∑ j, g (leaf j)) = d • (h + g r) :=
    sum_eq_card_nsmul_of_two_zsmul_perm_eq_const_add_perm
      (fun j ↦ g (leaf j)) (h + g r) P S hrel
  change ∃ P S : Equiv.Perm (Fin d),
    (∀ j : Fin d,
      P j ≠ j ∧ P j ≠ S j ∧
      center j = leaf (P j) ∧
      (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
      (2 : ℤ) • g (leaf (P j)) =
        h + g r + g (leaf (S j))) ∧
    (∑ j, g (leaf j)) = d • (h + g r)
  refine ⟨P, S, ?_, hsum⟩
  intro j
  have hPneS : P j ≠ S j := by
    intro heq
    apply (hP j).2.1
    rw [heq]
    exact (hS j).symm
  exact ⟨(hP j).1, hPneS, (hP j).2.2.1, hS j, hrel j⟩

/-- The refined global outcome: every nonsaturated center/leaf pattern pays
capacity, while the saturated pattern carries two permutations and the
summed affine identity. -/
def PureEdgeStarLeafPermutationOutcome
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
    PureEdgeStarLeafPermutationAlgebra g h r T a d center

omit [DecidableEq G] in
/-- Refine the saturated branch of the incidence trichotomy into explicit
successor/center permutation algebra and its global sum identity. -/
theorem pureEdgeStarLeafCycle_permutationOutcome_of_centerIncidenceOutcome
    (g : Fin (m + 1) → G) {h : G}
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafCenterIncidenceOutcome g h r T a d center) :
    PureEdgeStarLeafPermutationOutcome g h r T a d center := by
  rcases hout with hcap | hmixed | hsaturated
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    obtain ⟨P, hP⟩ := hsaturated
    exact pureEdgeStarLeafCycle_saturatedPermutationAlgebra
      g r T hcycle center P hP

/-- Global noncrossing endpoint with the summed two-permutation algebra in
the only branch that avoids both available coordinate-capacity bounds. -/
theorem exists_minimal_pureEdgeStarLeafCycle_permutationOutcome
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
          PureEdgeStarLeafPermutationOutcome g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_centerIncidenceOutcome
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_permutationOutcome_of_centerIncidenceOutcome
      g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
