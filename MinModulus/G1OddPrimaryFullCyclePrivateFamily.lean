/-
# The private kernel-witness family owned by cycle leaves

The full-generator transversal contains all but at most one displayed cycle
leaf.  Restrict the canonical private-witness choice of a minimal transversal
to those deleted leaves.  This gives at least `d-1` pairwise distinct
witnesses whose coefficient matrix on the selected leaf set is diagonal:
the owner coefficient is nonzero and every off-diagonal selected-leaf
coefficient vanishes.

This is the concrete family to be compared with the saturated center
permutation and the earlier owner/quarter capacity bounds.
-/
import MinModulus.G1OddPrimaryFullCycleIncidence

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- A large family of private nonzero cyclic-kernel witnesses indexed by
cycle leaves in the transversal.  Its coefficient matrix on the indexed
leaves is diagonal and its rows are pairwise distinct. -/
def CycleLeafKernelPrivateWitnessFamily
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧
    (∀ j ∈ J, leaf j ∈ B) ∧
    (∀ j, scalar j • y ≠ 0) ∧
    (∀ j, Witness g (scalar j • y) (coeff j)) ∧
    (∀ j, coeff j (leaf j) ≠ 0) ∧
    (∀ j k, j ≠ k → coeff j (leaf k) = 0) ∧
    Function.Injective coeff

/-- The cycle indices whose coordinates belong to the transversal have the
same cardinality as the intersection of the transversal with the cycle
range. -/
theorem card_cycleIndicesInTransversal_eq_card_inter_cycleRange
    {B : Finset (Fin n)} {d : ℕ}
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf) :
    (Finset.univ.filter (fun j ↦ leaf j ∈ B)).card =
      (B ∩ Finset.univ.image leaf).card := by
  let J : Finset (Fin d) :=
    Finset.univ.filter (fun j ↦ leaf j ∈ B)
  have himage : J.image leaf = B ∩ Finset.univ.image leaf := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hx
      have hjB := (Finset.mem_filter.mp hjJ).2
      exact Finset.mem_inter.mpr ⟨hjB,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
    · intro hx
      have hxB := (Finset.mem_inter.mp hx).1
      obtain ⟨j, _hj, rfl⟩ :=
        Finset.mem_image.mp (Finset.mem_inter.mp hx).2
      exact Finset.mem_image.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxB⟩, rfl⟩
  calc
    (Finset.univ.filter (fun j ↦ leaf j ∈ B)).card = J.card := rfl
    _ = (J.image leaf).card :=
      (Finset.card_image_of_injective J hleaf).symm
    _ = (B ∩ Finset.univ.image leaf).card := by rw [himage]

/-- The all-but-one leaf incidence of a minimal transversal canonically
produces the large diagonal private-witness family. -/
theorem exists_cycleLeafKernelPrivateWitnessFamily
    (g : Fin n → G) (y : G) {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (hinter : d - 1 ≤ (B ∩ Finset.univ.image leaf).card) :
    ∃ J : Finset (Fin d),
      CycleLeafKernelPrivateWitnessFamily g y B leaf J := by
  let J : Finset (Fin d) :=
    Finset.univ.filter (fun j ↦ leaf j ∈ B)
  have hJmem : ∀ j ∈ J, leaf j ∈ B := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hJcard : d - 1 ≤ J.card := by
    rw [card_cycleIndicesInTransversal_eq_card_inter_cycleRange leaf hleaf]
    exact hinter
  let owner : ↥J → {i : Fin n // i ∈ B} :=
    fun j ↦ ⟨leaf j, hJmem j j.property⟩
  have howner : Function.Injective owner := by
    intro j k hjk
    have hleafEq : leaf j = leaf k := congrArg Subtype.val hjk
    exact Subtype.ext (hleaf hleafEq)
  let data : ∀ j : ↥J, CyclicKernelPrivateWitnessData g y (owner j) :=
    fun j ↦ minimalCyclicKernelPrivateWitnessData g y hmin (owner j)
  refine ⟨J, (fun j ↦ (data j).scalar),
    (fun j ↦ (data j).coeff), hJcard, hJmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (data j).target_ne_zero
  · intro j
    exact (data j).isWitness
  · intro j
    exact (data j).owner_ne_zero
  · intro j k hjk
    apply (data j).zero_other (leaf k) (hJmem k k.property)
    intro hleafEq
    exact hjk (Subtype.ext (hleaf hleafEq.symm))
  · exact (minimalCyclicKernelPrivateWitness_coeff_injective
      g y hmin).comp howner

/-- Full-cycle incidence descent enriched by its large diagonal family of
leaf-owned private kernel witnesses. -/
def OddPrimaryFullCycleLeafPrivateChargeDescent
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin (m + 1)))
    (d : ℕ) (leaf : Fin d → Fin (m + 1)) : Prop :=
  OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
    ∃ J : Finset (Fin d),
      CycleLeafKernelPrivateWitnessFamily g y B leaf J

/-- Attach the canonical leaf-owned private family to a full-cycle incidence
descent. -/
theorem fullCycleLeafPrivateChargeDescent_of_incidence
    {t q d : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdescent : OddPrimaryFullCycleIncidenceChargeDescent g y B d
      (fun j ↦ (T^[j.val] a : Fin (m + 1)))) :
    OddPrimaryFullCycleLeafPrivateChargeDescent g y B d
      (fun j ↦ (T^[j.val] a : Fin (m + 1))) := by
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  have hleaf : Function.Injective leaf := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hjk
  obtain ⟨J, hfamily⟩ :=
    exists_cycleLeafKernelPrivateWitnessFamily
      g y hdescent.1.1 leaf hleaf hdescent.2.2
  exact ⟨hdescent, J, by simpa [leaf] using hfamily⟩

/-- Global endpoint retaining the all-but-one incidence and the resulting
large diagonal family of leaf-owned private witnesses. -/
def PureEdgeStarLeafOddPrimaryFullCyclePrivateFamilyOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
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
    (PureEdgeStarLeafOddPrimaryFullCycleIncidenceOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        (∀ j : Fin d,
          g (leaf j) - (h + g r) ∈ AddSubgroup.zmultiples y) ∧
        OddPrimaryFullCycleLeafPrivateChargeDescent g y B d leaf)

/-- Refine the global incidence endpoint by constructing the canonical
leaf-owned private-witness family. -/
theorem pureEdgeStarLeafCycle_privateFamilyOutcome_of_incidenceOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleIncidenceOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCyclePrivateFamilyOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨_hcharge, y, B, hmem, hdescent⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    exact ⟨hout', y, B, hmem,
      fullCycleLeafPrivateChargeDescent_of_incidence
        g r T hcycle hdescent⟩

/-- Global critical even-stratum endpoint carrying at least `d-1` distinct
leaf-owned private kernel witnesses with diagonal leaf restriction. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePrivateFamilyOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (qroot : ReducedSubsetSumCollision g h)
    (hqCanonical : qroot ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((qroot, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', qroot) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
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
          PureEdgeStarLeafOddPrimaryFullCyclePrivateFamilyOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleIncidenceOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_privateFamilyOutcome_of_incidenceOutcome
      g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
