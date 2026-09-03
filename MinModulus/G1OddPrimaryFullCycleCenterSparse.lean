/-
# Sparse center support of the leaf-owned kernel witnesses

In the saturated branch the center family is a permutation of the cycle
leaves.  Since the full-generator transversal contains all but at most one
leaf, it also contains all but at most one center.  A private witness owned
by a deleted leaf vanishes on every other deleted coordinate.  Its
restriction to the center range is consequently supported at no more than
two center indices: the center corresponding to its owner leaf, and the
possible center corresponding to the sole undeleted leaf.

This transfers the diagonal leaf-private family into the affine center
geometry where the next algebraic comparison takes place.
-/
import MinModulus.G1OddPrimaryFullCyclePrivateFamily

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- A large canonical private-witness family whose restriction to a
permuted copy of the leaf coordinates has support at most two in every row.
-/
def CycleCenterSparseKernelPrivateWitnessFamily
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧
    (∀ j : Fin d, j ∈ J ↔ leaf j ∈ B) ∧
    (∀ j, scalar j • y ≠ 0) ∧
    (∀ j, Witness g (scalar j • y) (coeff j)) ∧
    (∀ j, coeff j (leaf j) ≠ 0) ∧
    (∀ j k, j ≠ k → coeff j (leaf k) = 0) ∧
    (∀ (j : ↥J) x, x ∈ B →
      x ≠ leaf (j : Fin d) → coeff j x = 0) ∧
    Function.Injective coeff ∧
    (∀ k : Fin d, center k = leaf (P k)) ∧
    (Finset.univ.filter (fun k ↦ center k ∉ B)).card ≤ 1 ∧
    ∀ j : ↥J,
      coeff j (center (P.symm j)) ≠ 0 ∧
      (Finset.univ.filter (fun k ↦ coeff j (center k) ≠ 0)).card ≤ 2 ∧
      ∀ k : Fin d, coeff j (center k) ≠ 0 →
        k = P.symm j ∨ center k ∉ B

/-- Construct the center-sparse family from a minimal transversal, its
all-but-one leaf incidence, and the saturated center permutation. -/
theorem exists_cycleCenterSparseKernelPrivateWitnessFamily
    (g : Fin n → G) (y : G) {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    {d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (hinter : d - 1 ≤ (B ∩ Finset.univ.image leaf).card)
    (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (hcenter : ∀ k : Fin d, center k = leaf (P k)) :
    ∃ J : Finset (Fin d),
      CycleCenterSparseKernelPrivateWitnessFamily
        g y B leaf center P J := by
  let J : Finset (Fin d) :=
    Finset.univ.filter (fun j ↦ leaf j ∈ B)
  have hJiff : ∀ j : Fin d, j ∈ J ↔ leaf j ∈ B := by
    intro j
    simp [J]
  have hJcard : d - 1 ≤ J.card := by
    rw [card_cycleIndicesInTransversal_eq_card_inter_cycleRange leaf hleaf]
    exact hinter
  let owner : ↥J → {i : Fin n // i ∈ B} :=
    fun j ↦ ⟨leaf j, (hJiff j).mp j.property⟩
  have howner : Function.Injective owner := by
    intro j k hjk
    have hleafEq : leaf j = leaf k := congrArg Subtype.val hjk
    exact Subtype.ext (hleaf hleafEq)
  let data : ∀ j : ↥J, CyclicKernelPrivateWitnessData g y (owner j) :=
    fun j ↦ minimalCyclicKernelPrivateWitnessData g y hmin (owner j)
  let E : Finset (Fin d) :=
    Finset.univ.filter (fun k ↦ center k ∉ B)
  have hJcompl : (Finset.univ \ J).card ≤ 1 := by
    have hpartition := Finset.card_sdiff_add_card_inter
      (Finset.univ : Finset (Fin d)) J
    have hJle : J.card ≤ d := by simpa using Finset.card_le_univ J
    simp only [Finset.inter_eq_right.mpr (Finset.subset_univ J),
      Finset.card_univ, Fintype.card_fin] at hpartition
    omega
  have hEcard : E.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    have hkNotB : center k ∉ B := (Finset.mem_filter.mp hk).2
    have hlNotB : center l ∉ B := (Finset.mem_filter.mp hl).2
    have hPkNotJ : P k ∉ J := by
      intro hPkJ
      apply hkNotB
      rw [hcenter k]
      exact (hJiff (P k)).mp hPkJ
    have hPlNotJ : P l ∉ J := by
      intro hPlJ
      apply hlNotB
      rw [hcenter l]
      exact (hJiff (P l)).mp hPlJ
    apply P.injective
    exact (Finset.card_le_one.mp hJcompl)
      (P k) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hPkNotJ⟩)
      (P l) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hPlNotJ⟩)
  have hlocation : ∀ (j : ↥J) (k : Fin d),
      (data j).coeff (center k) ≠ 0 →
        k = P.symm j ∨ center k ∉ B := by
    intro j k hcoeff
    by_cases hkOwner : k = P.symm (j : Fin d)
    · exact Or.inl hkOwner
    · right
      intro hkB
      apply hcoeff
      apply (data j).zero_other (center k) hkB
      intro hcenterOwner
      apply hkOwner
      have hPk : P k = (j : Fin d) := by
        apply hleaf
        rw [← hcenter k]
        exact hcenterOwner
      calc
        k = P.symm (P k) := (P.symm_apply_apply k).symm
        _ = P.symm (j : Fin d) := congrArg P.symm hPk
  have hsupport : ∀ j : ↥J,
      (Finset.univ.filter
        (fun k ↦ (data j).coeff (center k) ≠ 0)).card ≤ 2 := by
    intro j
    let K : Finset (Fin d) := Finset.univ.filter
      (fun k ↦ (data j).coeff (center k) ≠ 0)
    have hsubset : K ⊆ ({P.symm (j : Fin d)} : Finset (Fin d)) ∪ E := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      rcases hlocation j k hknz with hkOwner | hkOutside
      · exact Finset.mem_union_left E (by simp [hkOwner])
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkOutside⟩)
    have hcard := Finset.card_le_card hsubset
    have hunion := Finset.card_union_le
      ({P.symm (j : Fin d)} : Finset (Fin d)) E
    have hsingleton :
        ({P.symm (j : Fin d)} : Finset (Fin d)).card = 1 := by
      simp
    change K.card ≤ 2
    omega
  refine ⟨J, (fun j ↦ (data j).scalar),
    (fun j ↦ (data j).coeff), hJcard, hJiff, ?_, ?_, ?_, ?_, ?_,
    ?_, hcenter, by simpa [E] using hEcard, ?_⟩
  · intro j
    exact (data j).target_ne_zero
  · intro j
    exact (data j).isWitness
  · intro j
    exact (data j).owner_ne_zero
  · intro j k hjk
    apply (data j).zero_other (leaf k) ((hJiff k).mp k.property)
    intro hleafEq
    exact hjk (Subtype.ext (hleaf hleafEq.symm))
  · intro j x hxB hxOwner
    exact (data j).zero_other x hxB hxOwner
  · exact (minimalCyclicKernelPrivateWitness_coeff_injective
      g y hmin).comp howner
  · intro j
    constructor
    · rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply]
      exact (data j).owner_ne_zero
    · exact ⟨hsupport j, hlocation j⟩

/-- Global saturated endpoint with the full odd-primary descent and the
center-sparse private-witness family attached to the original cycle-layer
package. -/
def PureEdgeStarLeafOddPrimaryFullCycleCenterSparseOutcome
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
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          (∀ j : Fin d,
            g (leaf j) - (h + g r) ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J)

/-- Starting from the aligned cycle-layer endpoint, construct the full-cycle
generator, its minimal descent, all-but-one leaf incidence, and the sparse
center restriction of the private family in one lossless saturated branch.
-/
theorem pureEdgeStarLeafCycle_centerSparseOutcome_of_cycleLayerChargeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleCenterSparseOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨hrelative, _hlayer, _i, _ell, _p, _B, _hellTwo, _hellD,
        _hodd, _htorsion, _hlayers, _hcert, _hordD, _hlog⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    have hleaf : Function.Injective leaf := by
      intro j k hjk
      apply minimalFixedPointFreeCycle_iterates_injective T hcycle
      exact Subtype.ext hjk
    have hperm := hrelative.permutationAlgebra g r T center
    obtain ⟨P, S, hlocal, hsum⟩ := hperm
    have hperm' : PureEdgeStarLeafPermutationAlgebra
        g h r T a d center := ⟨P, S, hlocal, hsum⟩
    have hcenter : ∀ k : Fin d, center k = leaf (P k) := by
      intro k
      exact (hlocal k).2.2.1
    obtain ⟨y, hmem, hlower, hrq⟩ :=
      hperm'.exists_fullCycleOddKernelGenerator
        g hg r T hcycle center
    obtain ⟨B, hcharge⟩ :=
      exists_fullCycleMinimalTransversalChargeDescent
        ht hcycle.1 g hg hcritical hlower hrq
    have hincidence : OddPrimaryFullCycleIncidenceChargeDescent
        g y B d leaf := by
      simpa [leaf] using
        fullCycleIncidenceChargeDescent_of_chargeDescent
          g hg r T hcycle hmem hcharge
    obtain ⟨J, hsparse⟩ :=
      exists_cycleCenterSparseKernelPrivateWitnessFamily
        g y hincidence.1.1 leaf hleaf hincidence.2.2 center P hcenter
    refine ⟨hout', y, B, P, J, ?_, hincidence, hsparse⟩
    simpa [leaf] using hmem

/-- Global critical even-stratum endpoint with at least `d-1` distinct
leaf-owned kernel witnesses, each supported at no more than two positions on
the saturated center range. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleCenterSparseOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleCenterSparseOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCycleLayerChargeOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_centerSparseOutcome_of_cycleLayerChargeOutcome
      ht g hg hcritical r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
