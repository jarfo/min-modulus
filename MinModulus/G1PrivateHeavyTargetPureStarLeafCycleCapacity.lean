/-
# Capacity or internal incidence on a pure-star leaf cycle

The least-period leaf cycle now carries two injective coordinate families:
its leaves and its coefficient-two centers.  If their images are disjoint,
the two families and the star itself occupy `2d+1` distinct ambient
coordinates.  Otherwise a center is itself a nonadjacent cycle leaf.  This
file packages that exact, lossless dichotomy and lifts it to the global
noncrossing endpoint.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafCycleAlgebra

namespace MinModulus

open Finset

/-- Two disjoint injective `d`-families, both avoiding one distinguished
point, occupy at least `2d+1` ambient coordinates. -/
theorem two_mul_add_one_le_of_disjoint_injective_ranges
    {n d : ℕ} (r : Fin n) (center leaf : Fin d → Fin n)
    (hcenter : Function.Injective center)
    (hleaf : Function.Injective leaf)
    (hdisj : Disjoint (Set.range center) (Set.range leaf))
    (hcenterStar : ∀ j, center j ≠ r)
    (hleafStar : ∀ j, leaf j ≠ r) :
    2 * d + 1 ≤ n := by
  classical
  let C : Finset (Fin n) := Finset.univ.image center
  let L : Finset (Fin n) := Finset.univ.image leaf
  have hCcard : C.card = d := by
    simpa [C] using
      Finset.card_image_of_injective (Finset.univ : Finset (Fin d)) hcenter
  have hLcard : L.card = d := by
    simpa [L] using
      Finset.card_image_of_injective (Finset.univ : Finset (Fin d)) hleaf
  have hCL : Disjoint C L := by
    rw [Finset.disjoint_left]
    intro z hzC hzL
    obtain ⟨j, _hj, hjz⟩ := Finset.mem_image.mp hzC
    obtain ⟨k, _hk, hkz⟩ := Finset.mem_image.mp hzL
    exact (Set.disjoint_left.1 hdisj)
      ⟨j, hjz⟩ ⟨k, hkz⟩
  have hUcard : (C ∪ L).card = 2 * d := by
    rw [Finset.card_union_of_disjoint hCL, hCcard, hLcard]
    omega
  have hrU : r ∉ C ∪ L := by
    intro hr
    rcases Finset.mem_union.mp hr with hrC | hrL
    · obtain ⟨j, _hj, hjr⟩ := Finset.mem_image.mp hrC
      exact hcenterStar j hjr
    · obtain ⟨j, _hj, hjr⟩ := Finset.mem_image.mp hrL
      exact hleafStar j hjr
  have hInsert : (insert r (C ∪ L)).card = (C ∪ L).card + 1 :=
    Finset.card_insert_of_notMem hrU
  have hle : (insert r (C ∪ L)).card ≤ n := by
    simpa using Finset.card_le_univ (insert r (C ∪ L))
  omega

/-- Exact set-theoretic split behind the cycle argument: disjoint images give
sharp ambient capacity, while failure of disjointness displays an incidence. -/
theorem injectiveRanges_capacity_or_intersect
    {n d : ℕ} (r : Fin n) (center leaf : Fin d → Fin n)
    (hcenter : Function.Injective center)
    (hleaf : Function.Injective leaf)
    (hcenterStar : ∀ j, center j ≠ r)
    (hleafStar : ∀ j, leaf j ≠ r) :
    2 * d + 1 ≤ n ∨ ∃ j k : Fin d, center j = leaf k := by
  classical
  by_cases hdisj : Disjoint (Set.range center) (Set.range leaf)
  · exact Or.inl (two_mul_add_one_le_of_disjoint_injective_ranges
      r center leaf hcenter hleaf hdisj hcenterStar hleafStar)
  · right
    obtain ⟨z, ⟨j, hj⟩, ⟨k, hk⟩⟩ := Set.not_disjoint_iff.mp hdisj
    exact ⟨j, k, hj.trans hk.symm⟩

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- On a least-period pure-star leaf cycle, either the centers and leaves
give `2d+1` distinct coordinates, or a center is a nonadjacent leaf.  The
internal incidence retains the affine recurrence and also avoids the
successor of its own source. -/
theorem pureEdgeStarLeafCycle_capacity_or_internalCenterIncidence
    (g : Fin (m + 1) → G) {h : G}
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hcenter : Function.Injective center)
    (hcenterSpec : ∀ j : Fin d,
      center j ≠ r ∧
      center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
      center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
      (2 : ℤ) • g (center j) =
        h + g r + g (T (T^[j.val] a) : Fin (m + 1))) :
    2 * d + 1 ≤ m + 1 ∨
      ∃ j k : Fin d,
        k ≠ j ∧
        center j = (T^[k.val] a : Fin (m + 1)) ∧
        (T^[k.val] a : Fin (m + 1)) ≠
          (T (T^[j.val] a) : Fin (m + 1)) ∧
        (2 : ℤ) • g (center j) =
          h + g r + g (T (T^[j.val] a) : Fin (m + 1)) := by
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  have hleaf : Function.Injective leaf := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    apply Subtype.ext
    exact hjk
  have hleafStar : ∀ j, leaf j ≠ r := by
    intro j
    exact (mem_witnessPureEdgeStarLeaves_iff g h r (leaf j)).1
      (T^[j.val] a).property |>.1
  rcases injectiveRanges_capacity_or_intersect
      r center leaf hcenter hleaf
      (fun j ↦ (hcenterSpec j).1) hleafStar with hcap | hinter
  · exact Or.inl hcap
  · right
    obtain ⟨j, k, hjk⟩ := hinter
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact (hcenterSpec j).2.1 hjk
    have htarget : leaf k ≠
        (T (T^[j.val] a) : Fin (m + 1)) := by
      intro hkt
      exact (hcenterSpec j).2.2.1 (hjk.trans hkt)
    exact ⟨j, k, hkj, hjk, htarget, (hcenterSpec j).2.2.2⟩

/-- Global noncrossing endpoint with the center-image dichotomy attached:
the least pure-star leaf cycle has either sharp ambient capacity or an
explicit nonadjacent internal center/leaf incidence. -/
theorem exists_minimal_pureEdgeStarLeafCycle_capacity_or_internalCenter
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
          (2 * d + 1 ≤ m + 1 ∨
            ∃ j k : Fin d,
              k ≠ j ∧
              center j = (T^[k.val] a : Fin (m + 1)) ∧
              (T^[k.val] a : Fin (m + 1)) ≠
                (T (T^[j.val] a) : Fin (m + 1)) ∧
              (2 : ℤ) • g (center j) =
                h + g r + g (T (T^[j.val] a) : Fin (m + 1))) := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_with_injectiveCenters
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross hL
  have hsplit := pureEdgeStarLeafCycle_capacity_or_internalCenterIncidence
    g r T hcycle center hcenter hcenterSpec
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hsplit⟩

end MinModulus
