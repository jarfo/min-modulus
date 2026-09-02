/-
# Aggregating center/leaf incidences on a pure-star cycle

The center/leaf overlap has three qualitatively different regimes.  Empty
overlap gives the sharp `2d+1` bound.  A proper nonempty overlap retains one
internal incidence but also one center outside the leaf image, which already
gives `d+2` distinct ambient coordinates together with all leaves and the
star.  If every center is a leaf, injectivity upgrades the incidence map to a
permutation of the cycle indices.  Its fixed points and successor hits are
excluded by the local pure-edge geometry, and every affine equation survives.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafCycleCapacity

namespace MinModulus

open Finset

/-- One point outside an injective `d`-family, together with a second point
outside both, gives `d+2` distinct ambient coordinates. -/
theorem card_add_two_le_of_injective_range_and_two_fresh
    {n d : ℕ} (r x : Fin n) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (hxStar : x ≠ r)
    (hxLeaf : x ∉ Set.range leaf)
    (hleafStar : ∀ j, leaf j ≠ r) :
    d + 2 ≤ n := by
  classical
  let L : Finset (Fin n) := Finset.univ.image leaf
  have hLcard : L.card = d := by
    simpa [L] using
      Finset.card_image_of_injective (Finset.univ : Finset (Fin d)) hleaf
  have hxL : x ∉ L := by
    intro hx
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_image.mp hx
    exact hxLeaf ⟨j, hjx⟩
  have hrL : r ∉ L := by
    intro hr
    obtain ⟨j, _hj, hjr⟩ := Finset.mem_image.mp hr
    exact hleafStar j hjr
  have hrXL : r ∉ insert x L := by
    rw [Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hxStar, hrL⟩
  have hxCard : (insert x L).card = L.card + 1 :=
    Finset.card_insert_of_notMem hxL
  have hrCard : (insert r (insert x L)).card = (insert x L).card + 1 :=
    Finset.card_insert_of_notMem hrXL
  have hle : (insert r (insert x L)).card ≤ n := by
    simpa using Finset.card_le_univ (insert r (insert x L))
  omega

/-- If every point in one injective finite family lies in a second injective
family of the same size, the unique index assignment is a permutation. -/
theorem exists_rangeIndexPerm
    {α : Type*} {d : ℕ} (center leaf : Fin d → α)
    (hcenter : Function.Injective center)
    (hall : ∀ j, center j ∈ Set.range leaf) :
    ∃ P : Equiv.Perm (Fin d), ∀ j, center j = leaf (P j) := by
  classical
  let p : Fin d → Fin d := fun j ↦ Classical.choose (hall j)
  have hpspec : ∀ j, center j = leaf (p j) := by
    intro j
    exact (Classical.choose_spec (hall j)).symm
  have hpinj : Function.Injective p := by
    intro j k hjk
    apply hcenter
    calc
      center j = leaf (p j) := hpspec j
      _ = leaf (p k) := by rw [hjk]
      _ = center k := (hpspec k).symm
  have hpbij : Function.Bijective p :=
    Finite.injective_iff_bijective.mp hpinj
  let P : Equiv.Perm (Fin d) := Equiv.ofBijective p hpbij
  refine ⟨P, ?_⟩
  intro j
  change center j = leaf (p j)
  exact hpspec j

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The lossless aggregate outcome for center/leaf incidence on one
least-period pure-star cycle. -/
def PureEdgeStarLeafCenterIncidenceOutcome
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
        center j = leaf k ∧
        center ell ∉ Set.range leaf) ∨
    ∃ P : Equiv.Perm (Fin d),
      ∀ j : Fin d,
        P j ≠ j ∧
        leaf (P j) ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
        center j = leaf (P j) ∧
        (2 : ℤ) • g (center j) =
          h + g r + g (T (T^[j.val] a) : Fin (m + 1))

omit [DecidableEq G] in
/-- Empty, proper, and saturated center/leaf overlap give respectively sharp
capacity, mixed capacity with explicit witnesses, and a fixed-point-free
incidence permutation avoiding the original cycle successor. -/
theorem pureEdgeStarLeafCycle_centerIncidenceOutcome
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
    PureEdgeStarLeafCenterIncidenceOutcome g h r T a d center := by
  classical
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
  change 2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    ∃ P : Equiv.Perm (Fin d),
      ∀ j : Fin d,
        P j ≠ j ∧
        leaf (P j) ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
        center j = leaf (P j) ∧
        (2 : ℤ) • g (center j) =
          h + g r + g (T (T^[j.val] a) : Fin (m + 1))
  by_cases hdisj : Disjoint (Set.range center) (Set.range leaf)
  · exact Or.inl (two_mul_add_one_le_of_disjoint_injective_ranges
      r center leaf hcenter hleaf hdisj
        (fun j ↦ (hcenterSpec j).1) hleafStar)
  · obtain ⟨z, ⟨j, hj⟩, ⟨k, hk⟩⟩ := Set.not_disjoint_iff.mp hdisj
    have hinter : center j = leaf k := hj.trans hk.symm
    by_cases hall : ∀ ell, center ell ∈ Set.range leaf
    · right
      right
      obtain ⟨P, hP⟩ := exists_rangeIndexPerm center leaf hcenter hall
      refine ⟨P, ?_⟩
      intro ell
      have hEq := hP ell
      have hPne : P ell ≠ ell := by
        intro hfix
        rw [hfix] at hEq
        exact (hcenterSpec ell).2.1 hEq
      have htarget : leaf (P ell) ≠
          (T (T^[ell.val] a) : Fin (m + 1)) := by
        intro heq
        exact (hcenterSpec ell).2.2.1 (hEq.trans heq)
      exact ⟨hPne, htarget, hEq, (hcenterSpec ell).2.2.2⟩
    · right
      left
      push Not at hall
      obtain ⟨ell, hell⟩ := hall
      have hcap := card_add_two_le_of_injective_range_and_two_fresh
        r (center ell) leaf hleaf (hcenterSpec ell).1 hell hleafStar
      exact ⟨hcap, j, k, ell, hinter, hell⟩

/-- Global noncrossing endpoint with the complete empty/proper/saturated
center-incidence trichotomy attached to its minimized pure-star leaf cycle. -/
theorem exists_minimal_pureEdgeStarLeafCycle_centerIncidenceOutcome
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
          PureEdgeStarLeafCenterIncidenceOutcome g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_with_injectiveCenters
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross hL
  have hout := pureEdgeStarLeafCycle_centerIncidenceOutcome
    g r T hcycle center hcenter hcenterSpec
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩

end MinModulus
