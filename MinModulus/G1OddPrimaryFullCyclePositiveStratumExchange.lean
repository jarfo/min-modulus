/-
# Uniform positive-stratum exchange

The complete quotient normal form exposes a deleted owner of full quotient
order in every non-full retained-difference arm, including the formerly
degenerate first stratum.  Exchange that owner with one retained coordinate
and minimize the resulting cyclic-kernel transversal.

A strict minimization enters the already separated three-retained C2 branch.
Otherwise the literal exchanged set remains minimal, has two retained
coordinates with quotient difference of order `2^t`, and inherits the exact
two-lift row normal form.  Thus no positive stratum needs a separate exchange
argument.
-/
import MinModulus.G1OddPrimaryFullCyclePositiveStratumQuotientPhase
import MinModulus.G1OddPrimaryFullCycleTransversalExchange
import MinModulus.G1OddPrimaryFullCyclePrimitiveUnitRows

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A weight-`-1` owner primitive relative to `z` is equally primitive
relative to `x`: its row says that the retained difference is twice the
owner displacement, so the second displacement is its negative. -/
theorem TwoRetainedFiveWeightPresentation.primitive_otherRetained_of_weight_eq_neg_one
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (b : ↥B) (hweight : p.weight b = -1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hquotientRelation :
      (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (b : Fin n) - g p.z) +
        p.weight b • (g p.x - g p.z))).mpr
    exact p.row_mem b
  have hdeltaDouble : deltaQ = (2 : ℕ) • betaQ := by
    rw [hweight] at hquotientRelation
    change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
    have hrelation' : betaQ + betaQ - deltaQ = 0 := by
      simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
        hquotientRelation
    calc
      deltaQ = (betaQ + betaQ - deltaQ) + deltaQ := by
        rw [hrelation', zero_add]
      _ = betaQ + betaQ := by abel
      _ = (2 : ℕ) • betaQ := (two_nsmul betaQ).symm
  have hdecomp :
      g (b : Fin n) - g p.x =
        (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
    abel
  have hquotient : pi (g (b : Fin n) - g p.x) = -betaQ := by
    rw [hdecomp, map_sub]
    change betaQ - deltaQ = -betaQ
    rw [hdeltaDouble]
    module
  change addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t
  rw [hquotient, addOrderOf_neg]
  simpa only [betaQ, pi, H, Q] using hprimitive

/-- Exchanging an owner outside a one-missing-leaf range for that missing
leaf puts the entire range into the exchanged deletion set. -/
theorem cycleRange_subset_insert_erase_missing
    {d : ℕ} (leaf : Fin d → Fin n) (p : Fin d)
    {B : Finset (Fin n)} {b x : Fin n}
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hmissing : leaf p = x) (hbOutside : b ∉ Set.range leaf) :
    ∀ i, leaf i ∈ insert x (B.erase b) := by
  classical
  intro i
  by_cases hip : i = p
  · subst i
    rw [hmissing]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, (hleafB i).2 hip⟩
    intro hleafb
    exact hbOutside ⟨i, hleafb⟩

/-- Exchanging one deleted cycle leaf for a point outside the cycle leaves
exactly that leaf undeleted. -/
theorem cycleRange_mem_insert_erase_leaf_iff
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    {B : Finset (Fin n)} (hleafB : ∀ i, leaf i ∈ B)
    (r : Fin d) {x : Fin n} (hxOutside : x ∉ Set.range leaf) :
    ∀ i, leaf i ∈ insert x (B.erase (leaf r)) ↔ i ≠ r := by
  classical
  intro i
  constructor
  · intro hi hir
    subst i
    simp only [Finset.mem_insert, Finset.mem_erase] at hi
    rcases hi with hxr | hir
    · exact hxOutside ⟨r, hxr⟩
    · exact hir.1 rfl
  · intro hir
    apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, hleafB i⟩
    intro hleafEq
    exact hir (hleafInj hleafEq)

/-- Literal exchanges of distinct injective cycle leaves give distinct
deletion sets when the inserted point was not deleted originally. -/
theorem insert_erase_cycleLeaf_injective
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    {B : Finset (Fin n)} (hleafB : ∀ i, leaf i ∈ B)
    {x : Fin n} (hxB : x ∉ B) :
    Function.Injective (fun r ↦ insert x (B.erase (leaf r))) := by
  classical
  intro r s hrs
  change insert x (B.erase (leaf r)) = insert x (B.erase (leaf s)) at hrs
  apply hleafInj
  by_contra hleafNe
  have hmemRight : leaf r ∈ insert x (B.erase (leaf s)) := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨hleafNe, hleafB r⟩
  have hmemLeft : leaf r ∈ insert x (B.erase (leaf r)) := by
    rw [hrs]
    exact hmemRight
  simp only [Finset.mem_insert, Finset.mem_erase] at hmemLeft
  rcases hmemLeft with hleafX | hfalse
  · exact hxB (hleafX ▸ hleafB r)
  · exact hfalse.1 rfl

/-- A cycle whose translated displacements span the cyclic kernel has one
quotient coset: all leaf displacements from any fixed base have the same
image modulo that kernel. -/
theorem cycle_quotient_displacement_eq_of_span
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y a base : G)
    {d : ℕ} (leaf : Fin d → Fin n)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    let H := AddSubgroup.zmultiples y
    let pi : G →+ G ⧸ H := QuotientAddGroup.mk' H
    ∀ i j,
      pi (g (leaf i) - base) = pi (g (leaf j) - base) := by
  let H : AddSubgroup G := AddSubgroup.zmultiples y
  let pi : G →+ G ⧸ H := QuotientAddGroup.mk' H
  change ∀ i j,
    pi (g (leaf i) - base) = pi (g (leaf j) - base)
  intro i j
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (QuotientAddGroup.eq_zero_iff
    ((g (leaf i) - base) - (g (leaf j) - base))).mpr
  have hi : g (leaf i) - a ∈ H := by
    change g (leaf i) - a ∈ AddSubgroup.zmultiples y
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hj : g (leaf j) - a ∈ H := by
    change g (leaf j) - a ∈ AddSubgroup.zmultiples y
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨j, rfl⟩
  have hij := H.sub_mem hi hj
  have heq :
      (g (leaf i) - base) - (g (leaf j) - base) =
        (g (leaf i) - a) - (g (leaf j) - a) := by
    abel
  rw [heq]
  exact hij

/-- Reverse the retained orientation of one five-weight presentation.  The
normalized weight transforms by `w ↦ -2-w`, leaving the underlying affine
row unchanged. -/
def TwoRetainedFiveWeightPresentation.reverse
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B) :
    TwoRetainedFiveWeightPresentation g y B where
  x := p.z
  z := p.x
  weight := fun b ↦ -2 - p.weight b
  x_not_mem := p.z_not_mem
  z_not_mem := p.x_not_mem
  x_ne_z := p.x_ne_z.symm
  complement_eq := by simpa only [pair_comm] using p.complement_eq
  weight_mem := by
    intro b
    have hb := p.weight_mem b
    simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
      Finset.mem_singleton] at hb ⊢
    rcases hb with hb | hb | hb | hb | hb <;> omega
  row_mem := by
    intro b
    have hb := p.row_mem b
    convert hb using 1
    module

/-- Extract a five-weight presentation in either prescribed ordering of the
two retained coordinates. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fiveWeightPresentation_with_orientation
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = x ∧ p.z = z := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hxComplement : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
  have hzComplement : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  rw [p.complement_eq] at hxComplement hzComplement
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxComplement hzComplement
  rcases hxComplement with hxpX | hxpZ
  · have hzpZ : z = p.z := hzComplement.resolve_left (by
      intro hzpX
      exact hxz (hxpX.trans hzpX.symm))
    exact ⟨p, hxpX.symm, hzpZ.symm⟩
  · have hzpX : z = p.x := hzComplement.resolve_right (by
      intro hzpZ
      exact hxz (hxpZ.trans hzpZ.symm))
    refine ⟨p.reverse g y B, ?_, ?_⟩
    · exact hxpZ.symm
    · exact hzpX.symm

/-- The full-order two-retained state after positive-stratum exchange. -/
def PrimitiveTwoRetainedPositiveStratumRows
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)

/-- A full-order positive-stratum state with its exact row presentation kept
as explicit data.  This carrier prevents later cycle arguments from choosing
a second, potentially oppositely oriented presentation. -/
def PrimitiveTwoRetainedPositiveStratumPresentation
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    addOrderOf deltaQ = 2 ^ t ∧
      ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
        (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
          pi (g (b : Fin n) - g p.z) =
            (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)

/-- The existential state is exactly the existence of one explicit
presentation carrier. -/
theorem primitiveTwoRetainedPositiveStratumRows_iff_exists_presentation
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) :
    PrimitiveTwoRetainedPositiveStratumRows g y B ↔
      ∃ p : TwoRetainedFiveWeightPresentation g y B,
        PrimitiveTwoRetainedPositiveStratumPresentation g y B p := by
  constructor
  · rintro ⟨hmin, hretained, hrows, p, hp⟩
    exact ⟨p, hmin, hretained, hrows, hp⟩
  · rintro ⟨p, hmin, hretained, hrows, hp⟩
    exact ⟨hmin, hretained, hrows, p, hp⟩

/-- Reorient a full-order state by any prescribed ordering of its two
retained coordinates while preserving the intrinsic quotient order. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.exists_fullOrderPresentation_with_orientation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = x ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t := by
  classical
  rcases hstate with ⟨_hmin, _hretained, hrows, p₀, hp₀full⟩
  obtain ⟨p, hpx, hpz⟩ :=
    hrows.fiveWeightPresentation_with_orientation
      g y B x z hxB hzB hxz
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  have hp₀Order : addOrderOf (pi (g p₀.x - g p₀.z)) = 2 ^ t := by
    simpa only [pi, H, Q] using hp₀full.1
  have hxCase : x = p₀.x ∨ x = p₀.z := by
    have hxMem : x ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
    rw [p₀.complement_eq] at hxMem
    simpa using hxMem
  have hzCase : z = p₀.x ∨ z = p₀.z := by
    have hzMem : z ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
    rw [p₀.complement_eq] at hzMem
    simpa using hzMem
  have hxzOrder : addOrderOf (pi (g x - g z)) = 2 ^ t := by
    rcases hxCase with hxpX | hxpZ
    · have hzpZ : z = p₀.z := hzCase.resolve_left (by
        intro hzpX
        exact hxz (hxpX.trans hzpX.symm))
      simpa only [hxpX, hzpZ] using hp₀Order
    · have hzpX : z = p₀.x := hzCase.resolve_right (by
        intro hzpZ
        exact hxz (hxpZ.trans hzpZ.symm))
      have hneg : g x - g z = -(g p₀.x - g p₀.z) := by
        rw [hxpZ, hzpX]
        abel
      rw [hneg, map_neg, addOrderOf_neg]
      exact hp₀Order
  refine ⟨p, hpx, hpz, ?_⟩
  rw [hpx, hpz]
  simpa only [pi, H, Q] using hxzOrder

/-- A canonical private presentation removes the half-period ambiguity from
every positive-stratum full-order row.  Its owner coefficient is a unit, and
the raw witness equation selects the first quotient lift. -/
theorem TwoRetainedCanonicalPrivatePresentation.fullOrder_unitRowNormalForm
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hfull :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 2 ^ t) :
    ∀ b : ↥B,
      (p.coeff b (b : Fin n) = -1 ∨ p.coeff b (b : Fin n) = 1) ∧
      ∃ k : ℤ, k ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
        p.weight b = 2 * k ∧
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        let H := AddSubgroup.zmultiples y
        let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
          QuotientAddGroup.mk' H
        pi (g (b : Fin n) - g p.z) =
          -(k • pi (g p.x - g p.z)) := by
  classical
  intro b
  let pFive := p.toFiveWeightPresentation g y B
  have hfullFive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g pFive.x - g pFive.z)) = 2 ^ t := by
    simpa only [pFive,
      TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
      using hfull
  have hnotWeight : p.weight b ≠ -1 := by
    have hnot := pFive.weight_ne_neg_one_of_fullOrder
      ht g y B hyq hfullOdd hfullFive b
    simpa only [pFive,
      TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
      using hnot
  have hnotHeavy : p.coeff b (b : Fin n) ≠ 2 := by
    intro hheavy
    exact hnotWeight ((p.weight_eq_neg_one_iff b).2 hheavy)
  have hownerUnit :
      p.coeff b (b : Fin n) = -1 ∨ p.coeff b (b : Fin n) = 1 := by
    have hlevels := p.owner_mem b
    simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
      Finset.mem_singleton] at hlevels
    rcases hlevels with hminus | hone | htwo
    · exact Or.inl hminus
    · exact Or.inr hone
    · exact (hnotHeavy htwo).elim
  refine ⟨hownerUnit, ?_⟩
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases hownerUnit with hminus | hone
  · let k : ℤ := -(p.coeff b p.x)
    have hweight : p.weight b = 2 * k := by
      rw [p.weight_eq b, hminus]
      simp only [twoRetainedOwnerNormalization, if_pos, k]
      ring
    have hkMem : k ∈ ({-2, -1, 0, 1} : Finset ℤ) := by
      have hw := p.weight_mem b
      simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
        Finset.mem_singleton] at hw
      rw [hweight] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcorrected :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) =
          -(p.scalar b • y) := by
      rw [hshape.2.2, hshape.1, hminus]
      dsimp only [k]
      module
    have hcorrectedMem :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y := by
      rw [hcorrected]
      exact AddSubgroup.neg_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _)
    refine ⟨k, hkMem, hweight, hcorrectedMem, ?_⟩
    let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    have hzero : pi
        (g (b : Fin n) - g p.z + k • (g p.x - g p.z)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcorrectedMem
    change pi (g (b : Fin n) - g p.z) =
      -(k • pi (g p.x - g p.z))
    rw [map_add, map_zsmul] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  · let k : ℤ := p.coeff b p.x
    have hweight : p.weight b = 2 * k := by
      rw [p.weight_eq b, hone]
      norm_num [twoRetainedOwnerNormalization, k]
    have hkMem : k ∈ ({-2, -1, 0, 1} : Finset ℤ) := by
      have hw := p.weight_mem b
      simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
        Finset.mem_singleton] at hw
      rw [hweight] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcorrected :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) =
          p.scalar b • y := by
      rw [hshape.2.2, hshape.1, hone]
      dsimp only [k]
      module
    have hcorrectedMem :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y := by
      rw [hcorrected]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
    refine ⟨k, hkMem, hweight, hcorrectedMem, ?_⟩
    let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    have hzero : pi
        (g (b : Fin n) - g p.z + k • (g p.x - g p.z)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcorrectedMem
    change pi (g (b : Fin n) - g p.z) =
      -(k • pi (g p.x - g p.z))
    rw [map_add, map_zsmul] at hzero
    exact eq_neg_of_add_eq_zero_left hzero

/-- Reconstruct canonical private witnesses in the exact orientation of a
positive-stratum carrier.  The reconstructed five-weight presentation remains
a full-order carrier and every canonical row uses its unique first lift. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exists_alignedCanonicalUnitRows
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1) :
    ∃ pc : TwoRetainedCanonicalPrivatePresentation g y B,
      pc.x = p.x ∧ pc.z = p.z ∧
        PrimitiveTwoRetainedPositiveStratumPresentation
          g y B (pc.toFiveWeightPresentation g y B) ∧
        ∀ b : ↥B,
          (pc.coeff b (b : Fin n) = -1 ∨
            pc.coeff b (b : Fin n) = 1) ∧
          ∃ k : ℤ, k ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
            pc.weight b = 2 * k ∧
            g (b : Fin n) - g pc.z + k • (g pc.x - g pc.z) ∈
              AddSubgroup.zmultiples y ∧
            let H := AddSubgroup.zmultiples y
            let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
              QuotientAddGroup.mk' H
            pi (g (b : Fin n) - g pc.z) =
              -(k • pi (g pc.x - g pc.z)) := by
  classical
  obtain ⟨pc, hpcx, hpcz⟩ :=
    exists_twoRetainedCanonicalPrivatePresentation
      g y hpres.1 hpres.2.1 p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z
        p.complement_eq
  have hfull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g pc.x - g pc.z)) = 2 ^ t := by
    simpa only [hpcx, hpcz] using hpres.2.2.2.1
  have hunit := pc.fullOrder_unitRowNormalForm
    ht g y B hyq hfullOdd hfull
  let pcFive := pc.toFiveWeightPresentation g y B
  have hcarrier :
      PrimitiveTwoRetainedPositiveStratumPresentation g y B pcFive := by
    refine ⟨hpres.1, hpres.2.1, hpres.2.2.1, hfull, ?_⟩
    intro b
    obtain ⟨_howner, k, _hk, hweight, _hcorrected, hquotient⟩ := hunit b
    exact ⟨k, hweight, Or.inl hquotient⟩
  exact ⟨pc, hpcx, hpcz, hcarrier, hunit⟩

/-- An odd integer multiple of an element of order `2^t` has the same order.
This is the parity fact that makes the positive-stratum exchange orientation
uniform. -/
theorem addOrderOf_odd_zsmul_eq_twoPower
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (delta : Q) (hdelta : addOrderOf delta = 2 ^ t)
    (c : ℤ) (hc : Odd c) :
    addOrderOf (c • delta) = 2 ^ t := by
  rcases Int.eq_nat_or_neg c with ⟨k, rfl | rfl⟩
  · have hkOdd : Odd k := by exact_mod_cast hc
    have hcoprime : (2 ^ t).Coprime k :=
      hkOdd.coprime_two_left.pow_left t
    rw [natCast_zsmul, addOrderOf_nsmul, hdelta,
      hcoprime.gcd_eq_one, Nat.div_one]
  · have hkOdd : Odd k := by simpa using hc
    have hcoprime : (2 ^ t).Coprime k :=
      hkOdd.coprime_two_left.pow_left t
    rw [neg_zsmul, addOrderOf_neg, natCast_zsmul, addOrderOf_nsmul,
      hdelta, hcoprime.gcd_eq_one, Nat.div_one]

/-- If `beta` is any integer multiple of a primitive `2^t`-element, then
`beta` or `beta-delta` is primitive: their integer coefficients are
consecutive, hence one is odd. -/
theorem addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (delta beta : Q) (hdelta : addOrderOf delta = 2 ^ t)
    (c : ℤ) (hbeta : beta = c • delta) :
    addOrderOf beta = 2 ^ t ∨ addOrderOf (beta - delta) = 2 ^ t := by
  rcases Int.even_or_odd c with hc | hc
  · right
    have hcSub : Odd (c - 1) := hc.sub_odd odd_one
    have hsub : beta - delta = (c - 1) • delta := by
      rw [hbeta]
      module
    rw [hsub]
    exact addOrderOf_odd_zsmul_eq_twoPower delta hdelta (c - 1) hcSub
  · left
    rw [hbeta]
    exact addOrderOf_odd_zsmul_eq_twoPower delta hdelta c hc

/-- Every deleted owner in an exact full-order presentation is primitive
relative to at least one of the two retained coordinates.  The exact row
normal form puts its quotient displacement in `Z*delta`; switching the
retained base point subtracts one copy of `delta`. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.owner_primitive_at_one_retained
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t ∨
      addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t := by
  rcases hpres with ⟨_hmin, _hretained, _hrows, hfull⟩
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using hfull.1
  obtain ⟨k, _hweight, hbeta | hbeta⟩ := hfull.2 b
  · have hmultiple : betaQ = (-k) • deltaQ := by
      simpa only [betaQ, deltaQ, pi, H, Q, neg_zsmul] using hbeta
    have hprimitive :=
      addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
        deltaQ betaQ hdelta (-k) hmultiple
    have hbaseChange :
        pi (g (b : Fin n) - g p.x) = betaQ - deltaQ := by
      have hvalue :
          g (b : Fin n) - g p.x =
            (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
        abel
      rw [hvalue, map_sub]
    simpa only [betaQ, deltaQ, pi, H, Q, hbaseChange] using hprimitive
  · have hmultiple :
        betaQ = ((2 ^ (t - 1) : ℕ) : ℤ) • deltaQ - k • deltaQ := by
      simpa only [betaQ, deltaQ, pi, H, Q, natCast_zsmul] using hbeta
    have hmultiple' :
        betaQ = (((2 ^ (t - 1) : ℕ) : ℤ) - k) • deltaQ := by
      rw [hmultiple]
      module
    have hprimitive :=
      addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
        deltaQ betaQ hdelta (((2 ^ (t - 1) : ℕ) : ℤ) - k) hmultiple'
    have hbaseChange :
        pi (g (b : Fin n) - g p.x) = betaQ - deltaQ := by
      have hvalue :
          g (b : Fin n) - g p.x =
            (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
        abel
      rw [hvalue, map_sub]
    simpa only [betaQ, deltaQ, pi, H, Q, hbaseChange] using hprimitive

/-- At the fifth stratum, an owner primitive relative to the first retained
coordinate can only have normalized weight `-4` or `0`. -/
private theorem fifthStratum_xPrimitive_ownerWeight
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.x)) = 32) :
    p.weight b = -4 ∨ p.weight b = 0 := by
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  let gammaQ : Q := pi (g (b : Fin n) - g p.x)
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    have hraw := hpres.2.2.2.1
    change addOrderOf (pi (g p.x - g p.z)) = 2 ^ 5 at hraw
    norm_num at hraw
    exact hraw
  have hgammaOrder : addOrderOf gammaQ = 32 := by
    simpa only [gammaQ, pi, H, Q] using hprimitive
  have hgamma : gammaQ = betaQ - deltaQ := by
    have hvalue :
        g (b : Fin n) - g p.x =
          (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
      abel
    change pi (g (b : Fin n) - g p.x) =
      pi (g (b : Fin n) - g p.z) - pi (g p.x - g p.z)
    rw [hvalue, map_sub]
  have hdeltaZero : (32 : ℕ) • deltaQ = 0 := by
    simpa only [hdeltaOrder] using addOrderOf_nsmul_eq_zero deltaQ
  obtain ⟨k, hk, hbeta⟩ := hpres.2.2.2.2 b
  change betaQ = -(k • deltaQ) ∨
    betaQ = (2 ^ (5 - 1) : ℕ) • deltaQ - k • deltaQ at hbeta
  have hweightMem := p.weight_mem b
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hweightMem
  rcases hweightMem with hw | hw | hw | hw | hw
  · exact Or.inl hw
  · have hk' : k = -1 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · have hgammaZero : (16 : ℕ) • gammaQ = 0 := by
        rw [hgamma, hbeta]
        module
      have hdvd : 32 ∣ 16 := by
        rw [← hgammaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hgammaZero
      omega
    · have hgammaZero : (16 : ℕ) • gammaQ = 0 := by
        norm_num at hbeta
        calc
          (16 : ℕ) • gammaQ = 8 • ((32 : ℕ) • deltaQ) := by
            rw [hgamma, hbeta]
            module
          _ = 0 := by rw [hdeltaZero]; simp
      have hdvd : 32 ∣ 16 := by
        rw [← hgammaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hgammaZero
      omega
  · omega
  · exact Or.inr hw
  · have hk' : k = 1 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · have hgammaZero : (16 : ℕ) • gammaQ = 0 := by
        calc
          (16 : ℕ) • gammaQ = -((32 : ℕ) • deltaQ) := by
            rw [hgamma, hbeta]
            module
          _ = 0 := by rw [hdeltaZero, neg_zero]
      have hdvd : 32 ∣ 16 := by
        rw [← hgammaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hgammaZero
      omega
    · have hgammaZero : (16 : ℕ) • gammaQ = 0 := by
        norm_num at hbeta
        calc
          (16 : ℕ) • gammaQ = 7 • ((32 : ℕ) • deltaQ) := by
            rw [hgamma, hbeta]
            module
          _ = 0 := by rw [hdeltaZero]; simp
      have hdvd : 32 ∣ 16 := by
        rw [← hgammaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hgammaZero
      omega

/-- Exact quotient positions of a fifth-stratum owner primitive relative to
the first retained coordinate.  The four positions are the two lifts of each
of the only two surviving normalized weights. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_xPrimitive_ownerPosition
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.x)) = 32) :
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    let deltaQ := pi (g p.x - g p.z)
    let betaQ := pi (g (b : Fin n) - g p.z)
    (p.weight b = -4 ∧
        (betaQ = (2 : ℕ) • deltaQ ∨ betaQ = (18 : ℕ) • deltaQ)) ∨
      (p.weight b = 0 ∧
        (betaQ = 0 ∨ betaQ = (16 : ℕ) • deltaQ)) := by
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  change
    (p.weight b = -4 ∧
        (betaQ = (2 : ℕ) • deltaQ ∨ betaQ = (18 : ℕ) • deltaQ)) ∨
      (p.weight b = 0 ∧
        (betaQ = 0 ∨ betaQ = (16 : ℕ) • deltaQ))
  have hweight := fifthStratum_xPrimitive_ownerWeight
    g y B p hpres b hprimitive
  obtain ⟨k, hk, hbeta⟩ := hpres.2.2.2.2 b
  change betaQ = -(k • deltaQ) ∨
    betaQ = (2 ^ (5 - 1) : ℕ) • deltaQ - k • deltaQ at hbeta
  rcases hweight with hweight | hweight
  · left
    refine ⟨hweight, ?_⟩
    have hk' : k = -2 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · left
      rw [hbeta]
      module
    · right
      norm_num at hbeta
      rw [hbeta]
      module
  · right
    refine ⟨hweight, ?_⟩
    have hk' : k = 0 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · left
      rw [hbeta]
      module
    · right
      norm_num at hbeta
      rw [hbeta]

/-- At the fifth stratum, an owner primitive relative to the second retained
coordinate can only have normalized weight `-2` or `2`. -/
private theorem fifthStratum_zPrimitive_ownerWeight
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z)) = 32) :
    p.weight b = -2 ∨ p.weight b = 2 := by
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hbetaOrder : addOrderOf betaQ = 32 := by
    simpa only [betaQ, pi, H, Q] using hprimitive
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    have hraw := hpres.2.2.2.1
    change addOrderOf (pi (g p.x - g p.z)) = 2 ^ 5 at hraw
    norm_num at hraw
    exact hraw
  have hdeltaZero : (32 : ℕ) • deltaQ = 0 := by
    simpa only [hdeltaOrder] using addOrderOf_nsmul_eq_zero deltaQ
  obtain ⟨k, hk, hbeta⟩ := hpres.2.2.2.2 b
  change betaQ = -(k • deltaQ) ∨
    betaQ = (2 ^ (5 - 1) : ℕ) • deltaQ - k • deltaQ at hbeta
  have hweightMem := p.weight_mem b
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hweightMem
  rcases hweightMem with hw | hw | hw | hw | hw
  · have hk' : k = -2 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · have hbetaZero : (16 : ℕ) • betaQ = 0 := by
        calc
          (16 : ℕ) • betaQ = (32 : ℕ) • deltaQ := by
            rw [hbeta]
            module
          _ = 0 := hdeltaZero
      have hdvd : 32 ∣ 16 := by
        rw [← hbetaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hbetaZero
      omega
    · have hbetaZero : (16 : ℕ) • betaQ = 0 := by
        norm_num at hbeta
        calc
          (16 : ℕ) • betaQ = 9 • ((32 : ℕ) • deltaQ) := by
            rw [hbeta]
            module
          _ = 0 := by rw [hdeltaZero]; simp
      have hdvd : 32 ∣ 16 := by
        rw [← hbetaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hbetaZero
      omega
  · exact Or.inl hw
  · omega
  · have hk' : k = 0 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · have hbetaZero : (16 : ℕ) • betaQ = 0 := by
        rw [hbeta]
        simp
      have hdvd : 32 ∣ 16 := by
        rw [← hbetaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hbetaZero
      omega
    · have hbetaZero : (16 : ℕ) • betaQ = 0 := by
        norm_num at hbeta
        calc
          (16 : ℕ) • betaQ = 8 • ((32 : ℕ) • deltaQ) := by
            rw [hbeta]
            module
          _ = 0 := by rw [hdeltaZero]; simp
      have hdvd : 32 ∣ 16 := by
        rw [← hbetaOrder]
        exact addOrderOf_dvd_of_nsmul_eq_zero hbetaZero
      omega
  · exact Or.inr hw

/-- Exact quotient positions of a fifth-stratum owner primitive relative to
the second retained coordinate. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_zPrimitive_ownerPosition
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z)) = 32) :
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    let deltaQ := pi (g p.x - g p.z)
    let betaQ := pi (g (b : Fin n) - g p.z)
    (p.weight b = -2 ∧
        (betaQ = deltaQ ∨ betaQ = (17 : ℕ) • deltaQ)) ∨
      (p.weight b = 2 ∧
        (betaQ = -deltaQ ∨ betaQ = (15 : ℕ) • deltaQ)) := by
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  change
    (p.weight b = -2 ∧
        (betaQ = deltaQ ∨ betaQ = (17 : ℕ) • deltaQ)) ∨
      (p.weight b = 2 ∧
        (betaQ = -deltaQ ∨ betaQ = (15 : ℕ) • deltaQ))
  have hweight := fifthStratum_zPrimitive_ownerWeight
    g y B p hpres b hprimitive
  obtain ⟨k, hk, hbeta⟩ := hpres.2.2.2.2 b
  change betaQ = -(k • deltaQ) ∨
    betaQ = (2 ^ (5 - 1) : ℕ) • deltaQ - k • deltaQ at hbeta
  rcases hweight with hweight | hweight
  · left
    refine ⟨hweight, ?_⟩
    have hk' : k = -1 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · left
      rw [hbeta]
      module
    · right
      norm_num at hbeta
      rw [hbeta]
      module
  · right
    refine ⟨hweight, ?_⟩
    have hk' : k = 1 := by omega
    subst k
    rcases hbeta with hbeta | hbeta
    · left
      rw [hbeta]
      module
    · right
      norm_num at hbeta
      rw [hbeta]
      module

/-- In the only live three- and four-cycle Mersenne cases, fifth-stratum
criticality locks the ambient dimension to five more than the cycle length.
This is a cardinality consequence of validity and the strict endpoint, not a
tuple census. -/
theorem criticalFifthStratum_mersenne_threeOrFour_dimension_eq_add_five
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    (hd : d = 3 ∨ d = 4) (hq : q = 2 ^ d - 1) :
    n = d + 5 := by
  have hqSmall : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 15 := by
    rcases hd with rfl | rfl <;> norm_num at hq ⊢ <;> omega
  have hpairs := criticalFifthStratum_smallOddFactor_finitePairs
    g hg hcritical hqSmall
  rcases hpairs with ⟨hn, hq'⟩ | ⟨hn, hq'⟩ |
      ⟨hn, hq'⟩ | ⟨hn, hq'⟩
  all_goals rcases hd with rfl | rfl <;> norm_num at hq ⊢ <;> omega

/-- A two-retained transversal containing exactly all but one member of an
injective `d`-coordinate family has exactly four owners outside that family
when the ambient dimension is `d+5`. -/
theorem card_offCycleOwners_eq_four_of_oneRetained_dimension
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (B : Finset (Fin n)) (p : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hn : n = d + 5) (hretained : n - B.card = 2) :
    (B \ (Finset.univ.image leaf)).card = 4 := by
  let L : Finset (Fin n) := Finset.univ.image leaf
  have hLinter : (B ∩ L).card = d - 1 := by
    rw [← card_cycleIndicesInTransversal_eq_card_inter_cycleRange
      leaf hleafInj]
    have hfilter :
        Finset.univ.filter (fun i ↦ leaf i ∈ B) =
          (Finset.univ : Finset (Fin d)).erase p := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      rw [hleafB]
      tauto
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ, Fintype.card_fin]
  have hBcardLe : B.card ≤ n := by
    simpa using Finset.card_le_univ B
  have hBcard : B.card = d + 3 := by omega
  have hdecomp := Finset.card_sdiff_add_card_inter B L
  rw [hLinter, hBcard] at hdecomp
  have hdpos : 0 < d := by
    exact Nat.pos_of_ne_zero (by
      intro hd0
      subst d
      exact Fin.elim0 p)
  simpa only [L] using (show (B \ L).card = 4 by omega)

/-- The four quotient coefficients for owners primitive toward the first
retained coordinate. -/
def fifthStratumXOwnerQuotientCoefficients : Finset ℕ := {2, 18, 0, 16}

/-- The four quotient coefficients for owners primitive toward the second
retained coordinate.  Coefficient `31` represents `-1` modulo order `32`. -/
def fifthStratumZOwnerQuotientCoefficients : Finset ℕ := {1, 17, 31, 15}

/-- The realized first-retained primitive-owner positions generated by an
order-`32` retained difference. -/
noncomputable def fifthStratumXOwnerQuotientPositions
    {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
    (delta : Q) : Finset Q :=
  fifthStratumXOwnerQuotientCoefficients.image (fun k ↦ k • delta)

/-- The realized second-retained primitive-owner positions generated by an
order-`32` retained difference. -/
noncomputable def fifthStratumZOwnerQuotientPositions
    {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
    (delta : Q) : Finset Q :=
  fifthStratumZOwnerQuotientCoefficients.image (fun k ↦ k • delta)

private theorem eq_of_nsmul_eq_nsmul_of_lt_addOrderOf
    {Q : Type*} [AddCommGroup Q] {delta : Q} {a b : ℕ}
    (ha : a < addOrderOf delta) (hb : b < addOrderOf delta)
    (hab : a • delta = b • delta) : a = b := by
  exact ((nsmul_eq_nsmul_iff_modEq).mp hab).eq_of_lt_of_lt ha hb

/-- The four candidate first-retained owner positions are genuinely distinct
when the retained difference has order `32`. -/
theorem card_fifthStratumXOwnerQuotientPositions_of_order32
    {Q : Type*} [AddCommGroup Q] [Finite Q] [DecidableEq Q]
    (delta : Q) (hdelta : addOrderOf delta = 32) :
    (fifthStratumXOwnerQuotientPositions delta).card = 4 := by
  classical
  have hcoeffCard : fifthStratumXOwnerQuotientCoefficients.card = 4 := by
    norm_num [fifthStratumXOwnerQuotientCoefficients]
  have hinj : Set.InjOn (fun k : ℕ ↦ k • delta)
      fifthStratumXOwnerQuotientCoefficients := by
    intro a ha b hb hab
    apply eq_of_nsmul_eq_nsmul_of_lt_addOrderOf (delta := delta)
    · rw [hdelta]
      change a ∈ fifthStratumXOwnerQuotientCoefficients at ha
      simp [fifthStratumXOwnerQuotientCoefficients] at ha
      omega
    · rw [hdelta]
      change b ∈ fifthStratumXOwnerQuotientCoefficients at hb
      simp [fifthStratumXOwnerQuotientCoefficients] at hb
      omega
    · exact hab
  rw [fifthStratumXOwnerQuotientPositions,
    Finset.card_image_iff.mpr hinj, hcoeffCard]

/-- The four candidate second-retained owner positions are genuinely distinct
when the retained difference has order `32`. -/
theorem card_fifthStratumZOwnerQuotientPositions_of_order32
    {Q : Type*} [AddCommGroup Q] [Finite Q] [DecidableEq Q]
    (delta : Q) (hdelta : addOrderOf delta = 32) :
    (fifthStratumZOwnerQuotientPositions delta).card = 4 := by
  classical
  have hcoeffCard : fifthStratumZOwnerQuotientCoefficients.card = 4 := by
    norm_num [fifthStratumZOwnerQuotientCoefficients]
  have hinj : Set.InjOn (fun k : ℕ ↦ k • delta)
      fifthStratumZOwnerQuotientCoefficients := by
    intro a ha b hb hab
    apply eq_of_nsmul_eq_nsmul_of_lt_addOrderOf (delta := delta)
    · rw [hdelta]
      change a ∈ fifthStratumZOwnerQuotientCoefficients at ha
      simp [fifthStratumZOwnerQuotientCoefficients] at ha
      omega
    · rw [hdelta]
      change b ∈ fifthStratumZOwnerQuotientCoefficients at hb
      simp [fifthStratumZOwnerQuotientCoefficients] at hb
      omega
    · exact hab
  rw [fifthStratumZOwnerQuotientPositions,
    Finset.card_image_iff.mpr hinj, hcoeffCard]

private theorem fifthStratum_xPrimitive_ownerPosition_mem
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.x)) = 32) :
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    pi (g (b : Fin n) - g p.z) ∈
      fifthStratumXOwnerQuotientPositions
        (pi (g p.x - g p.z)) := by
  classical
  have hpos := hpres.fifthStratum_xPrimitive_ownerPosition
    g y B p b hprimitive
  rcases hpos with ⟨_, hpos | hpos⟩ | ⟨_, hpos | hpos⟩
  all_goals simp [fifthStratumXOwnerQuotientPositions,
    fifthStratumXOwnerQuotientCoefficients, hpos]

private theorem fifthStratum_zPrimitive_ownerPosition_mem
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z)) = 32) :
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    pi (g (b : Fin n) - g p.z) ∈
      fifthStratumZOwnerQuotientPositions
        (pi (g p.x - g p.z)) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    have hraw := hpres.2.2.2.1
    change addOrderOf (pi (g p.x - g p.z)) = 2 ^ 5 at hraw
    norm_num at hraw
    exact hraw
  have hdeltaZero : (32 : ℕ) • deltaQ = 0 := by
    simpa only [hdeltaOrder] using addOrderOf_nsmul_eq_zero deltaQ
  have hneg : -deltaQ = (31 : ℕ) • deltaQ := by
    calc
      -deltaQ = -deltaQ + (32 : ℕ) • deltaQ := by
        rw [hdeltaZero, add_zero]
      _ = (31 : ℕ) • deltaQ := by module
  have hpos := hpres.fifthStratum_zPrimitive_ownerPosition
    g y B p b hprimitive
  change pi (g (b : Fin n) - g p.z) ∈
    fifthStratumZOwnerQuotientPositions deltaQ
  change
    (p.weight b = -2 ∧
        (pi (g (b : Fin n) - g p.z) = deltaQ ∨
          pi (g (b : Fin n) - g p.z) = (17 : ℕ) • deltaQ)) ∨
      (p.weight b = 2 ∧
        (pi (g (b : Fin n) - g p.z) = -deltaQ ∨
          pi (g (b : Fin n) - g p.z) = (15 : ℕ) • deltaQ)) at hpos
  rcases hpos with ⟨_, hpos | hpos⟩ | ⟨_, hpos | hpos⟩
  all_goals simp [fifthStratumZOwnerQuotientPositions,
    fifthStratumZOwnerQuotientCoefficients, hpos, hneg]

/-- An equal-cardinality finite family mapping into a finite target either
has a collision or occupies the whole target. -/
theorem finiteMap_collision_or_fullImage_of_equal_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β)
    (hcard : S.card = T.card) (hsubset : S.image f ⊆ T) :
    (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a = f b) ∨
      S.image f = T := by
  by_cases hinj : Set.InjOn f S
  · right
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_image_iff.mpr hinj, hcard]
  · left
    simp only [Set.InjOn] at hinj
    push Not at hinj
    obtain ⟨a, ha, b, hb, hfab, hab⟩ := hinj
    exact ⟨a, ha, b, hb, hab, hfab⟩

/-- Four off-cycle owners primitive toward the first retained coordinate
either collide in quotient position or occupy all four HAK positions. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_xPrimitive_offCycle_collision_or_fullOccupancy
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (leaf : Fin d → Fin n)
    (hcard : (B \ (Finset.univ.image leaf)).card = 4)
    (hall : ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.x)) = 32) :
    let S := B \ (Finset.univ.image leaf)
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    let deltaQ := pi (g p.x - g p.z)
    (∃ b ∈ S, ∃ c ∈ S, b ≠ c ∧
        pi (g b - g p.z) = pi (g c - g p.z)) ∨
      S.image (fun b ↦ pi (g b - g p.z)) =
        fifthStratumXOwnerQuotientPositions deltaQ := by
  classical
  let S := B \ (Finset.univ.image leaf)
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let f : Fin n → Q := fun b ↦ pi (g b - g p.z)
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    have hraw := hpres.2.2.2.1
    change addOrderOf (pi (g p.x - g p.z)) = 2 ^ 5 at hraw
    norm_num at hraw
    exact hraw
  have htargetCard :
      (fifthStratumXOwnerQuotientPositions deltaQ).card = 4 :=
    card_fifthStratumXOwnerQuotientPositions_of_order32
      deltaQ hdeltaOrder
  have hsubset : S.image f ⊆
      fifthStratumXOwnerQuotientPositions deltaQ := by
    rw [Finset.image_subset_iff]
    intro b hbS
    have hbB : b ∈ B := (Finset.mem_sdiff.mp hbS).1
    have hbOutside : b ∉ Set.range leaf := by
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      exact (Finset.mem_sdiff.mp hbS).2
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    exact fifthStratum_xPrimitive_ownerPosition_mem
      g y B p hpres ⟨b, hbB⟩ (hall ⟨b, hbB⟩ hbOutside)
  have hcardEq : S.card =
      (fifthStratumXOwnerQuotientPositions deltaQ).card := by
    rw [htargetCard]
    exact hcard
  exact finiteMap_collision_or_fullImage_of_equal_card
    S (fifthStratumXOwnerQuotientPositions deltaQ) f hcardEq hsubset

/-- Four off-cycle owners primitive toward the second retained coordinate
either collide in quotient position or occupy all four HAK positions. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_zPrimitive_offCycle_collision_or_fullOccupancy
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (leaf : Fin d → Fin n)
    (hcard : (B \ (Finset.univ.image leaf)).card = 4)
    (hall : ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z)) = 32) :
    let S := B \ (Finset.univ.image leaf)
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    let deltaQ := pi (g p.x - g p.z)
    (∃ b ∈ S, ∃ c ∈ S, b ≠ c ∧
        pi (g b - g p.z) = pi (g c - g p.z)) ∨
      S.image (fun b ↦ pi (g b - g p.z)) =
        fifthStratumZOwnerQuotientPositions deltaQ := by
  classical
  let S := B \ (Finset.univ.image leaf)
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let f : Fin n → Q := fun b ↦ pi (g b - g p.z)
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    have hraw := hpres.2.2.2.1
    change addOrderOf (pi (g p.x - g p.z)) = 2 ^ 5 at hraw
    norm_num at hraw
    exact hraw
  have htargetCard :
      (fifthStratumZOwnerQuotientPositions deltaQ).card = 4 :=
    card_fifthStratumZOwnerQuotientPositions_of_order32
      deltaQ hdeltaOrder
  have hsubset : S.image f ⊆
      fifthStratumZOwnerQuotientPositions deltaQ := by
    rw [Finset.image_subset_iff]
    intro b hbS
    have hbB : b ∈ B := (Finset.mem_sdiff.mp hbS).1
    have hbOutside : b ∉ Set.range leaf := by
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      exact (Finset.mem_sdiff.mp hbS).2
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    exact fifthStratum_zPrimitive_ownerPosition_mem
      g y B p hpres ⟨b, hbB⟩ (hall ⟨b, hbB⟩ hbOutside)
  have hcardEq : S.card =
      (fifthStratumZOwnerQuotientPositions deltaQ).card := by
    rw [htargetCard]
    exact hcard
  exact finiteMap_collision_or_fullImage_of_equal_card
    S (fifthStratumZOwnerQuotientPositions deltaQ) f hcardEq hsubset

/-- Four source points mapping into a set of at most two values necessarily
contain a collision. -/
theorem finiteMap_collision_of_card_four_image_subset_pair
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (u v : β)
    (hcard : S.card = 4) (hsubset : S.image f ⊆ {u, v}) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a = f b := by
  by_contra hcollision
  push Not at hcollision
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    by_contra hne
    exact hcollision a ha b hb hne hab
  have himageCard : (S.image f).card = 4 := by
    rw [Finset.card_image_iff.mpr hinj, hcard]
  have hle := Finset.card_le_card hsubset
  have hpairCard : ({u, v} : Finset β).card ≤ 2 := by
    calc
      ({u, v} : Finset β).card ≤ ({v} : Finset β).card + 1 :=
        Finset.card_insert_le u {v}
      _ = 2 := by simp
  omega

/-- Canonical private rows collapse the four HAK positions in the
first-retained primitive orientation to the two first-lift positions.
Consequently four off-cycle owners must collide in the quotient; the HAM
full-occupancy arm cannot occur. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_xPrimitive_offCycle_collision_of_canonicalRows
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (leaf : Fin d → Fin n)
    (hcard : (B \ (Finset.univ.image leaf)).card = 4)
    (hall : ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.x)) = 32) :
    let S := B \ (Finset.univ.image leaf)
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    ∃ b ∈ S, ∃ c ∈ S, b ≠ c ∧
      pi (g b - g p.z) = pi (g c - g p.z) := by
  classical
  obtain ⟨pc, hpcx, hpcz, hpc, hunit⟩ :=
    hpres.exists_alignedCanonicalUnitRows (by norm_num)
      g y B p hyq hfullOdd
  let pcFive := pc.toFiveWeightPresentation g y B
  let S := B \ (Finset.univ.image leaf)
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g pc.x - g pc.z)
  let f : Fin n → Q := fun b ↦ pi (g b - g pc.z)
  have hsubset : S.image f ⊆ {(2 : ℕ) • deltaQ, 0} := by
    rw [Finset.image_subset_iff]
    intro b hbS
    have hbB : b ∈ B := (Finset.mem_sdiff.mp hbS).1
    have hbOutside : b ∉ Set.range leaf := by
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      exact (Finset.mem_sdiff.mp hbS).2
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    have hprimitive :
        addOrderOf (pi (g b - g pc.x)) = 32 := by
      have hraw := hall ⟨b, hbB⟩ hbOutside
      simpa only [pi, H, Q, hpcx] using hraw
    have hprimitiveFive :
        addOrderOf (pi (g b - g pcFive.x)) = 32 := by
      simpa only [pcFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hprimitive
    have hpos := hpc.fifthStratum_xPrimitive_ownerPosition
      g y B pcFive ⟨b, hbB⟩ hprimitiveFive
    have hpos' : pc.weight ⟨b, hbB⟩ = -4 ∨
        pc.weight ⟨b, hbB⟩ = 0 := by
      simpa only [pcFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hpos.imp (fun h ↦ h.1) (fun h ↦ h.1)
    obtain ⟨_howner, k, _hk, hweight, _hcorrected, hquotient⟩ :=
      hunit ⟨b, hbB⟩
    change f b = -(k • deltaQ) at hquotient
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hpos' with hweightNeg | hweightZero
    · left
      have hk : k = -2 := by omega
      rw [hquotient, hk]
      module
    · right
      have hk : k = 0 := by omega
      rw [hquotient, hk]
      simp
  have hcollision :=
    finiteMap_collision_of_card_four_image_subset_pair
      S f ((2 : ℕ) • deltaQ) 0 hcard hsubset
  simpa only [S, f, pi, H, Q, hpcz] using hcollision

/-- Canonical private rows collapse the four HAK positions in the
second-retained primitive orientation to the two first-lift positions.
Consequently four off-cycle owners must collide in the quotient; the HAM
full-occupancy arm cannot occur. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.fifthStratum_zPrimitive_offCycle_collision_of_canonicalRows
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (leaf : Fin d → Fin n)
    (hcard : (B \ (Finset.univ.image leaf)).card = 4)
    (hall : ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z)) = 32) :
    let S := B \ (Finset.univ.image leaf)
    let pi := QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
    ∃ b ∈ S, ∃ c ∈ S, b ≠ c ∧
      pi (g b - g p.z) = pi (g c - g p.z) := by
  classical
  obtain ⟨pc, hpcx, hpcz, hpc, hunit⟩ :=
    hpres.exists_alignedCanonicalUnitRows (by norm_num)
      g y B p hyq hfullOdd
  let pcFive := pc.toFiveWeightPresentation g y B
  let S := B \ (Finset.univ.image leaf)
  let H : AddSubgroup (ZMod (2 ^ 5 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 5 * q) ⧸ H
  let pi : ZMod (2 ^ 5 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g pc.x - g pc.z)
  let f : Fin n → Q := fun b ↦ pi (g b - g pc.z)
  have hsubset : S.image f ⊆ {deltaQ, -deltaQ} := by
    rw [Finset.image_subset_iff]
    intro b hbS
    have hbB : b ∈ B := (Finset.mem_sdiff.mp hbS).1
    have hbOutside : b ∉ Set.range leaf := by
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      exact (Finset.mem_sdiff.mp hbS).2
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    have hprimitive :
        addOrderOf (pi (g b - g pc.z)) = 32 := by
      have hraw := hall ⟨b, hbB⟩ hbOutside
      simpa only [pi, H, Q, hpcz] using hraw
    have hprimitiveFive :
        addOrderOf (pi (g b - g pcFive.z)) = 32 := by
      simpa only [pcFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hprimitive
    have hpos := hpc.fifthStratum_zPrimitive_ownerPosition
      g y B pcFive ⟨b, hbB⟩ hprimitiveFive
    have hpos' : pc.weight ⟨b, hbB⟩ = -2 ∨
        pc.weight ⟨b, hbB⟩ = 2 := by
      simpa only [pcFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hpos.imp (fun h ↦ h.1) (fun h ↦ h.1)
    obtain ⟨_howner, k, _hk, hweight, _hcorrected, hquotient⟩ :=
      hunit ⟨b, hbB⟩
    change f b = -(k • deltaQ) at hquotient
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hpos' with hweightNeg | hweightPos
    · left
      have hk : k = -1 := by omega
      rw [hquotient, hk]
      module
    · right
      have hk : k = 1 := by omega
      rw [hquotient, hk]
      simp
  have hcollision :=
    finiteMap_collision_of_card_four_image_subset_pair
      S f deltaQ (-deltaQ) hcard hsubset
  simpa only [S, f, pi, H, Q, hpcz] using hcollision

/-- Full quotient order makes the five-weight labels of a fully deleted
doubling cycle constant in the *given* row presentation.  This is the
presentation-preserving version of the generic cycle split: the alternative
nonzero coefficient has absolute value at most `18`, while full order forces
its absolute value to be divisible by `2^t`. -/
theorem TwoRetainedFiveWeightPresentation.fullDeleted_weight_constant_of_fullOrder
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hfull :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 2 ^ t)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∀ i j,
      p.weight ⟨leaf i, hleafB i⟩ = p.weight ⟨leaf j, hleafB j⟩ := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ t * q) := g p.x - g p.z
  let deltaQ : Q := pi delta
  have hdeltaOrder : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, delta, pi, H, Q] using hfull
  have htransition : ∀ i,
      (p.weight ⟨leaf (R i), hleafB (R i)⟩ -
          2 * p.weight ⟨leaf i, hleafB i⟩) • delta +
        (2 : ℤ) • (g p.z - a) ∈ H := by
    intro i
    have hsub := H.sub_mem (p.row_mem ⟨leaf (R i), hleafB (R i)⟩)
      (H.zsmul_mem (p.row_mem ⟨leaf i, hleafB i⟩) 2)
    have hvalue :
        g (leaf (R i)) = (2 : ℤ) • g (leaf i) - a := by
      calc
        g (leaf (R i)) = (g (leaf (R i)) - a) + a := by abel
        _ = (2 : ℤ) • (g (leaf i) - a) + a := by rw [hdouble i]
        _ = (2 : ℤ) • g (leaf i) - a := by module
    convert hsub using 1
    dsimp only [H, delta]
    rw [hvalue]
    module
  have hpair : ∀ i j,
      ((p.weight ⟨leaf (R i), hleafB (R i)⟩ -
          2 * p.weight ⟨leaf i, hleafB i⟩) -
        (p.weight ⟨leaf (R j), hleafB (R j)⟩ -
          2 * p.weight ⟨leaf j, hleafB j⟩)) • delta ∈ H := by
    intro i j
    have hsub := H.sub_mem (htransition i) (htransition j)
    convert hsub using 1
    module
  let cycleWeight : Fin d → ℤ := fun i ↦
    p.weight ⟨leaf i, hleafB i⟩
  let i₀ : Fin d := ⟨0, hd⟩
  have hcycleWeight : ∀ i,
      cycleWeight i ∈ twoRetainedNormalizedWeightLevels := by
    intro i
    exact p.weight_mem ⟨leaf i, hleafB i⟩
  have hcyclePair : ∀ i j,
      ((cycleWeight (R i) - 2 * cycleWeight i) -
        (cycleWeight (R j) - 2 * cycleWeight j)) • delta ∈ H := by
    intro i j
    simpa only [cycleWeight] using hpair i j
  rcases fiveWeightTransition_smallKernelMultiple_or_weight_constant
      i₀ R cycleWeight hcycleWeight delta y hcyclePair with
    ⟨e, he, helow, hehigh, heMem⟩ | hconstant
  · have heQuotient : e • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff (e • delta)).mpr
      simpa only [H] using heMem
    have hnatQuotient : e.natAbs • deltaQ = 0 := by
      rw [← natCast_zsmul]
      rcases Int.natAbs_eq e with hePos | heNeg
      · rw [hePos] at heQuotient
        exact heQuotient
      · rw [heNeg, neg_smul] at heQuotient
        exact neg_eq_zero.mp heQuotient
    have horderDvd : 2 ^ t ∣ e.natAbs := by
      rw [← hdeltaOrder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hnatQuotient
    have horderLe : 2 ^ t ≤ e.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · simpa only [cycleWeight] using hconstant

/-- In a presentation oriented with the unique retained cycle leaf first,
full quotient order forces every deleted cycle-leaf row to have pure weight
`-2`.  Only the common cycle coset and the order gap `4 < 2^t` are used. -/
theorem TwoRetainedFiveWeightPresentation.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hfull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t)
    (hpow : 4 < 2 ^ t)
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (hpx : leaf r = p.x)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2 := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using hfull
  intro i hi
  have hbeta : pi (g (leaf i) - g p.z) = deltaQ := by
    calc
      pi (g (leaf i) - g p.z) = pi (g (leaf r) - g p.z) :=
        cycle_quotient_displacement_eq_of_span
          g y a (g p.z) leaf hspan i r
      _ = deltaQ := by rw [hpx]
  have hquotientRelation :
      (2 : ℤ) • pi (g (leaf i) - g p.z) +
        p.weight ⟨leaf i, hi⟩ • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (leaf i) - g p.z) +
        p.weight ⟨leaf i, hi⟩ • (g p.x - g p.z))).mpr
    exact p.row_mem ⟨leaf i, hi⟩
  rw [hbeta] at hquotientRelation
  let e : ℤ := p.weight ⟨leaf i, hi⟩ + 2
  have heZero : e • deltaQ = 0 := by
    dsimp only [e]
    rw [add_zsmul]
    rw [add_comm]
    exact hquotientRelation
  by_contra hweight
  have he : e ≠ 0 := by
    intro he
    apply hweight
    dsimp only [e] at he
    omega
  have hnatZero : e.natAbs • deltaQ = 0 := by
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq e with hePos | heNeg
    · rw [hePos] at heZero
      exact heZero
    · rw [heNeg, neg_smul] at heZero
      exact neg_eq_zero.mp heZero
  have horderDvd : 2 ^ t ∣ e.natAbs := by
    rw [← hdelta]
    exact addOrderOf_dvd_of_nsmul_eq_zero hnatZero
  have horderLe : 2 ^ t ≤ e.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
  have hweightMem := p.weight_mem ⟨leaf i, hi⟩
  have habsLe : e.natAbs ≤ 4 := by
    simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
      Finset.mem_singleton] at hweightMem
    rcases Int.natAbs_eq e with hePos | heNeg
    · have : (e.natAbs : ℤ) ≤ 4 := by
        dsimp only [e]
        rcases hweightMem with hw | hw | hw | hw | hw <;> omega
      exact_mod_cast this
    · have : (e.natAbs : ℤ) ≤ 4 := by
        dsimp only [e]
        rcases hweightMem with hw | hw | hw | hw | hw <;> omega
      exact_mod_cast this
  omega

/-- A punctured-cycle full-order state in the common comparison orientation:
the missing leaf is retained first, a fixed off-cycle endpoint is retained
second, and every surviving cycle leaf has pure normalized weight `-2`. -/
def PrimitiveOneRetainedCyclePurePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) {d : ℕ} (leaf : Fin d → Fin n)
    (r : Fin d) (z : Fin n) : Prop :=
  PrimitiveTwoRetainedPositiveStratumRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = leaf r ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2

/-- Put one punctured-cycle full-order state into the common pure comparison
orientation. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 4 < 2 ^ t)
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (z : Fin n) (hzB : z ∉ B) (hrz : leaf r ≠ z) :
    PrimitiveOneRetainedCyclePurePresentation g y B leaf r z := by
  have hrB : leaf r ∉ B := by
    rw [hleafB r]
    simp
  obtain ⟨p, hpx, hpz, hfull⟩ :=
    hstate.exists_fullOrderPresentation_with_orientation
      g y B (leaf r) z hrB hzB hrz
  refine ⟨hstate, p, hpx, hpz, hfull, ?_⟩
  exact p.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
    g y B hfull hpow leaf a r hpx.symm hspan

/-- Canonical private-row data for every member of a simultaneous punctured
cycle family.  Besides the aligned presentations, the carrier keeps the
literal deletion sets, cycle incidence, both relevant full-order differences,
and the common inserted owner in every transversal. -/
structure PrimitivePuncturedCyclePrivateMatrix
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    {d : ℕ} (set : Fin d → Finset (Fin n)) (leaf : Fin d → Fin n)
    (inserted fixed : Fin n) where
  state : ∀ r, PrimitiveTwoRetainedPositiveStratumRows g y (set r)
  presentation : ∀ r,
    TwoRetainedCanonicalPrivatePresentation g y (set r)
  leaf_injective : Function.Injective leaf
  common_mem : ∀ r, inserted ∈ set r
  leaf_mem_iff : ∀ r i, leaf i ∈ set r ↔ i ≠ r
  missing_first : ∀ r, (presentation r).x = leaf r
  fixed_second : ∀ r, (presentation r).z = fixed
  retained_full_order : ∀ r,
    addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g (presentation r).x - g (presentation r).z)) = 2 ^ t
  common_full_order :
    addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g inserted - g fixed)) = 2 ^ t
  surviving_weight : ∀ r i (hi : leaf i ∈ set r),
    (presentation r).weight ⟨leaf i, hi⟩ = -2
  set_injective : Function.Injective set

/-- Reconstruct the canonical private witnesses in the same pure orientation
as one punctured state. -/
theorem PrimitiveOneRetainedCyclePurePresentation.exists_canonicalPrivatePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (z : Fin n)
    (hpure : PrimitiveOneRetainedCyclePurePresentation g y B leaf r z)
    (hpow : 4 < 2 ^ t)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      p.x = leaf r ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2 := by
  classical
  rcases hpure with ⟨hstate, p₀, hp₀x, hp₀z, hp₀full, _hp₀weight⟩
  have hrB : leaf r ∉ B := by
    simpa only [← hp₀x] using p₀.x_not_mem
  have hzB : z ∉ B := by
    simpa only [← hp₀z] using p₀.z_not_mem
  have hrz : leaf r ≠ z := by
    intro hrz
    apply p₀.x_ne_z
    rw [hp₀x, hp₀z, hrz]
  have hcomplement : Finset.univ \ B = {leaf r, z} := by
    simpa only [hp₀x, hp₀z] using p₀.complement_eq
  obtain ⟨p, hpx, hpz⟩ :=
    exists_twoRetainedCanonicalPrivatePresentation
      g y hstate.1 hstate.2.1 (leaf r) z hrB hzB hrz hcomplement
  have hfull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t := by
    simpa only [hpx, hpz, hp₀x, hp₀z] using hp₀full
  let pFive := p.toFiveWeightPresentation g y B
  have hweight :=
    pFive.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
      g y B hfull hpow leaf a r hpx.symm hspan
  refine ⟨p, hpx, hpz, hfull, ?_⟩
  intro i hi
  simpa only [pFive,
    TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation] using
      hweight i hi

/-- Assemble canonical private presentations pointwise from an aligned pure
punctured family. -/
theorem exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    {d : ℕ} (set : Fin d → Finset (Fin n)) (leaf : Fin d → Fin n)
    (inserted fixed : Fin n) (a : ZMod (2 ^ t * q))
    (hfamily : ∀ r,
      PrimitiveOneRetainedCyclePurePresentation g y (set r) leaf r fixed)
    (hleafInj : Function.Injective leaf)
    (hcommonMem : ∀ r, inserted ∈ set r)
    (hleafMem : ∀ r i, leaf i ∈ set r ↔ i ≠ r)
    (hsetsInj : Function.Injective set)
    (hcommonFull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g inserted - g fixed)) = 2 ^ t)
    (hpow : 4 < 2 ^ t)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    Nonempty
      (PrimitivePuncturedCyclePrivateMatrix
        g y set leaf inserted fixed) := by
  classical
  have hcanonical : ∀ r, ∃ p :
      TwoRetainedCanonicalPrivatePresentation g y (set r),
      p.x = leaf r ∧ p.z = fixed ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ set r), p.weight ⟨leaf i, hi⟩ = -2 := by
    intro r
    exact (hfamily r).exists_canonicalPrivatePresentation
      g y (set r) leaf a r fixed hpow hspan
  choose presentation hpresentation using hcanonical
  exact ⟨{
    state := fun r ↦ (hfamily r).1
    presentation := presentation
    leaf_injective := hleafInj
    common_mem := hcommonMem
    leaf_mem_iff := hleafMem
    missing_first := fun r ↦ (hpresentation r).1
    fixed_second := fun r ↦ (hpresentation r).2.1
    retained_full_order := fun r ↦ (hpresentation r).2.2.1
    common_full_order := hcommonFull
    surviving_weight := fun r ↦ (hpresentation r).2.2.2
    set_injective := hsetsInj }⟩

/-- The common inserted coordinate viewed as an owner in one punctured
transversal. -/
def PrimitivePuncturedCyclePrivateMatrix.commonOwner
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ↥(set r) :=
  ⟨inserted, M.common_mem r⟩

/-- The selected scalar of the common inserted owner's private row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonScalar
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ℤ :=
  (M.presentation r).scalar (M.commonOwner r)

/-- The selected coefficient vector of the common inserted owner's private
row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonCoeff
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : Fin n → ℤ :=
  (M.presentation r).coeff (M.commonOwner r)

/-- Every row selected at the common inserted owner retains its nonzero
kernel target, witness equation, nonzero owner diagonal, bounded owner level,
and privacy on the corresponding literal punctured transversal. -/
theorem PrimitivePuncturedCyclePrivateMatrix.common_private_row
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonScalar r • y ≠ 0 ∧
      Witness g (M.commonScalar r • y) (M.commonCoeff r) ∧
      M.commonCoeff r inserted ≠ 0 ∧
      M.commonCoeff r inserted ∈ twoRetainedExternalCoefficientLevels ∧
      ∀ b ∈ set r, b ≠ inserted → M.commonCoeff r b = 0 := by
  exact ⟨(M.presentation r).target_ne_zero (M.commonOwner r),
    (M.presentation r).isWitness (M.commonOwner r),
    (M.presentation r).owner_ne_zero (M.commonOwner r),
    (M.presentation r).owner_mem (M.commonOwner r),
    (M.presentation r).zero_other (M.commonOwner r)⟩

/-- Every common-owner row has exact three-coordinate support and one of
seven integer profiles.  Writing its coefficients on
`(inserted, missing leaf, fixed)` as `(mu, lambda, gamma)`, the possibilities
are

* `mu = -1`, `-1 ≤ lambda ≤ 2`;
* `mu = 1`, `-1 ≤ lambda ≤ 0`;
* `mu = 2`, `lambda = -1`;

and always `mu + lambda + gamma = 0`. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCoeff_threeSupport_sevenProfiles
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    (∀ i, i ≠ inserted → i ≠ leaf r → i ≠ fixed →
      M.commonCoeff r i = 0) ∧
    M.commonCoeff r inserted + M.commonCoeff r (leaf r) +
        M.commonCoeff r fixed = 0 ∧
    ((M.commonCoeff r inserted = -1 ∧
        -1 ≤ M.commonCoeff r (leaf r) ∧
        M.commonCoeff r (leaf r) ≤ 2) ∨
      (M.commonCoeff r inserted = 1 ∧
        -1 ≤ M.commonCoeff r (leaf r) ∧
        M.commonCoeff r (leaf r) ≤ 0) ∨
      (M.commonCoeff r inserted = 2 ∧
        M.commonCoeff r (leaf r) = -1)) ∧
    M.commonCoeff r inserted • g inserted +
        M.commonCoeff r (leaf r) • g (leaf r) +
        M.commonCoeff r fixed • g fixed = M.commonScalar r • y := by
  classical
  let c : Fin n → ℤ := M.commonCoeff r
  have hleafNeInserted : leaf r ≠ inserted := by
    intro hli
    have hmem : leaf r ∈ set r := by
      simpa only [hli] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 hmem) rfl
  have hinsertedNeFixed : inserted ≠ fixed := by
    intro hif
    apply (M.presentation r).z_not_mem
    rw [M.fixed_second r, ← hif]
    exact M.common_mem r
  have hleafNeFixed : leaf r ≠ fixed := by
    intro hlf
    apply (M.presentation r).x_ne_z
    rw [M.missing_first r, M.fixed_second r, hlf]
  have hinsertedNotTail : inserted ∉ ({leaf r, fixed} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hleafNeInserted, hinsertedNeFixed⟩
  have hleafNotFixed : leaf r ∉ ({fixed} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hleafNeFixed
  have hzero : ∀ i, i ≠ inserted → i ≠ leaf r → i ≠ fixed → c i = 0 := by
    intro i hiInserted hiLeaf hiFixed
    by_cases hiSet : i ∈ set r
    · exact (M.presentation r).zero_other
        (M.commonOwner r) i hiSet hiInserted
    · have hiComplement : i ∈ Finset.univ \ set r :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiSet⟩
      rw [(M.presentation r).complement_eq] at hiComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiComplement
      rcases hiComplement with hix | hiz
      · exact False.elim (hiLeaf (hix.trans (M.missing_first r)))
      · exact False.elim (hiFixed (hiz.trans (M.fixed_second r)))
  have hrestrict :
      ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i =
        ∑ i, c i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      apply hzero i
      · intro hii
        exact hi (by simp [hii])
      · intro hil
        exact hi (by simp [hil])
      · intro hif
        exact hi (by simp [hif]))
  have hsumRight : c inserted + (c (leaf r) + c fixed) = 0 := by
    calc
      c inserted + (c (leaf r) + c fixed) =
          ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i := by
            rw [Finset.sum_insert hinsertedNotTail,
              Finset.sum_insert hleafNotFixed]
            simp
      _ = ∑ i, c i := hrestrict
      _ = 0 := (M.presentation r).isWitness (M.commonOwner r) |>.2.2.1
  have hsum : c inserted + c (leaf r) + c fixed = 0 := by
    simpa only [add_assoc] using hsumRight
  have hvalueRestrict :
      ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i • g i =
        ∑ i, c i • g i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      rw [hzero i (by
        intro hii
        exact hi (by simp [hii])) (by
        intro hil
        exact hi (by simp [hil])) (by
        intro hif
        exact hi (by simp [hif])), zero_zsmul])
  have hvalueRight : c inserted • g inserted +
      (c (leaf r) • g (leaf r) + c fixed • g fixed) =
        M.commonScalar r • y := by
    calc
      c inserted • g inserted +
          (c (leaf r) • g (leaf r) + c fixed • g fixed) =
          ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)),
            c i • g i := by
              rw [Finset.sum_insert hinsertedNotTail,
                Finset.sum_insert hleafNotFixed]
              simp
      _ = ∑ i, c i • g i := hvalueRestrict
      _ = M.commonScalar r • y :=
        (M.presentation r).isWitness (M.commonOwner r) |>.2.2.2
  have hvalue : c inserted • g inserted + c (leaf r) • g (leaf r) +
      c fixed • g fixed = M.commonScalar r • y := by
    simpa only [add_assoc] using hvalueRight
  have hownerMem : c inserted ∈ twoRetainedExternalCoefficientLevels := by
    simpa only [c] using (M.common_private_row r).2.2.2.1
  have hmissingLower : -1 ≤ c (leaf r) := by
    simpa only [c,
      PrimitivePuncturedCyclePrivateMatrix.commonCoeff] using
      ((M.presentation r).isWitness (M.commonOwner r)).2.1 (leaf r)
  have hfixedLower : -1 ≤ c fixed := by
    simpa only [c,
      PrimitivePuncturedCyclePrivateMatrix.commonCoeff] using
      ((M.presentation r).isWitness (M.commonOwner r)).2.1 fixed
  have hprofiles :
      (c inserted = -1 ∧ -1 ≤ c (leaf r) ∧ c (leaf r) ≤ 2) ∨
      (c inserted = 1 ∧ -1 ≤ c (leaf r) ∧ c (leaf r) ≤ 0) ∨
      (c inserted = 2 ∧ c (leaf r) = -1) := by
    simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
      Finset.mem_singleton] at hownerMem
    rcases hownerMem with hminus | hone | htwo
    · exact Or.inl ⟨hminus, hmissingLower, by omega⟩
    · exact Or.inr (Or.inl ⟨hone, hmissingLower, by omega⟩)
    · exact Or.inr (Or.inr ⟨htwo, by omega⟩)
  exact ⟨by simpa only [c] using hzero,
    by simpa only [c] using hsum,
    by simpa only [c] using hprofiles,
    by simpa only [c] using hvalue⟩

/-- The seven possible `(common owner, missing leaf)` coefficient pairs.  The
fixed-endpoint coefficient is their negative sum. -/
def puncturedCyclePrivateProfiles : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (-1, 2),
    (1, -1), (1, 0), (2, -1)}

theorem card_puncturedCyclePrivateProfiles :
    puncturedCyclePrivateProfiles.card = 7 := by
  norm_num [puncturedCyclePrivateProfiles]

/-- The finite profile of one common-owner private row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonProfile
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ℤ × ℤ :=
  (M.commonCoeff r inserted, M.commonCoeff r (leaf r))

theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_mem
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonProfile r ∈ puncturedCyclePrivateProfiles := by
  have hprofile := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.1
  simp only [puncturedCyclePrivateProfiles,
    PrimitivePuncturedCyclePrivateMatrix.commonProfile,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rcases hprofile with hminus | hone | htwo <;> omega

/-- Seven-profile pigeonhole for the cross-puncture private matrix. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_capacity_or_largeFiber
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (K : ℕ) :
    d ≤ 7 * K ∨
      ∃ profile ∈ puncturedCyclePrivateProfiles,
        K < (Finset.univ.filter
          (fun r : Fin d ↦ M.commonProfile r = profile)).card := by
  have hcapacity := finiteMap_capacity_or_largeFiber
    puncturedCyclePrivateProfiles M.commonProfile M.commonProfile_mem K
  simpa only [Fintype.card_fin, card_puncturedCyclePrivateProfiles] using
    hcapacity

/-- The actual nonzero odd-kernel target of the common-owner row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonTarget
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ZMod (2 ^ t * q) :=
  M.commonScalar r • y

/-- Two elements of the same positive power-of-two order cannot be related by
doubling. -/
theorem ne_two_nsmul_of_addOrderOf_eq_same_twoPower
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (ht : 1 ≤ t) (delta beta : Q)
    (hdelta : addOrderOf delta = 2 ^ t)
    (hbeta : addOrderOf beta = 2 ^ t) :
    delta ≠ (2 : ℕ) • beta := by
  intro heq
  have hpowEq : 2 ^ (t - 1) * 2 = 2 ^ t := by
    calc
      2 ^ (t - 1) * 2 = 2 ^ ((t - 1) + 1) := (pow_succ 2 (t - 1)).symm
      _ = 2 ^ t := by congr 1; omega
  have hzero : (2 ^ (t - 1)) • delta = 0 := by
    rw [heq, ← mul_nsmul beta 2 (2 ^ (t - 1)), Nat.mul_comm, hpowEq]
    simpa only [hbeta] using addOrderOf_nsmul_eq_zero beta
  have hdvd : 2 ^ t ∣ 2 ^ (t - 1) := by
    rw [← hdelta]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzero
  have hle : 2 ^ t ≤ 2 ^ (t - 1) :=
    Nat.le_of_dvd (by positivity) hdvd
  have hlt : 2 ^ (t - 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- The raw three-supported witness gives a two-generator relation in the
quotient: `mu * delta + lambda * beta = 0`. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_quotientRelation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonCoeff r inserted •
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g inserted - g fixed) +
      M.commonCoeff r (leaf r) •
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (leaf r) - g fixed) = 0 := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  have hsum := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hvalue := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.2
  have hfixedCoeff :
      M.commonCoeff r fixed =
        -(M.commonCoeff r inserted + M.commonCoeff r (leaf r)) := by
    omega
  have htargetMem : M.commonTarget r ∈ H := by
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
  have hmem :
      M.commonCoeff r inserted • (g inserted - g fixed) +
        M.commonCoeff r (leaf r) • (g (leaf r) - g fixed) ∈ H := by
    change M.commonScalar r • y ∈ H at htargetMem
    rw [← hvalue] at htargetMem
    rw [hfixedCoeff] at htargetMem
    convert htargetMem using 1
    module
  apply (QuotientAddGroup.eq_zero_iff
    (M.commonCoeff r inserted • (g inserted - g fixed) +
      M.commonCoeff r (leaf r) • (g (leaf r) - g fixed))).2
  exact hmem

/-- Only three of the seven sparse profiles are compatible with full order
for both the common inserted difference and the missing-leaf difference. -/
def puncturedCycleFullOrderPrivateProfiles : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 1), (1, -1)}

theorem card_puncturedCycleFullOrderPrivateProfiles :
    puncturedCycleFullOrderPrivateProfiles.card = 3 := by
  norm_num [puncturedCycleFullOrderPrivateProfiles]

theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_mem_fullOrderProfiles
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (ht : 1 ≤ t) (r : Fin d) :
    M.commonProfile r ∈ puncturedCycleFullOrderPrivateProfiles := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  let betaQ : Q := pi (g (leaf r) - g fixed)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using M.common_full_order
  have hbeta : addOrderOf betaQ = 2 ^ t := by
    have horder := M.retained_full_order r
    simpa only [deltaQ, betaQ, pi, H, Q, M.missing_first r,
      M.fixed_second r] using horder
  have hrelation : M.commonCoeff r inserted • deltaQ +
      M.commonCoeff r (leaf r) • betaQ = 0 := by
    simpa only [deltaQ, betaQ, pi, H, Q] using
      M.commonProfile_quotientRelation r
  have hprofile := M.commonProfile_mem r
  simp only [puncturedCyclePrivateProfiles,
    PrimitivePuncturedCyclePrivateMatrix.commonProfile,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hprofile
  rcases hprofile with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inl h₁
  · have hzero : deltaQ = 0 := by
      rw [h₂.1, h₂.2] at hrelation
      simpa only [neg_one_zsmul, zero_zsmul, add_zero, neg_eq_zero] using
        hrelation
    rw [hzero] at hdelta
    norm_num at hdelta
    have : 1 < 2 ^ t := one_lt_pow₀ (by omega) (by omega)
    omega
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inr (Or.inl h₃)
  · have heq : deltaQ = (2 : ℕ) • betaQ := by
      rw [h₄.1, h₄.2] at hrelation
      have hsub : (2 : ℤ) • betaQ - deltaQ = 0 := by
        simpa only [neg_one_zsmul, sub_eq_add_neg, add_comm] using hrelation
      have heqZ : deltaQ = (2 : ℤ) • betaQ :=
        (sub_eq_zero.mp hsub).symm
      simpa only [two_nsmul, two_zsmul] using heqZ
    exact (ne_two_nsmul_of_addOrderOf_eq_same_twoPower
      ht deltaQ betaQ hdelta hbeta heq).elim
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inr (Or.inr h₅)
  · have hzero : deltaQ = 0 := by
      rw [h₆.1, h₆.2] at hrelation
      simpa only [one_zsmul, zero_zsmul, add_zero] using hrelation
    rw [hzero] at hdelta
    norm_num at hdelta
    have : 1 < 2 ^ t := one_lt_pow₀ (by omega) (by omega)
    omega
  · have heq : betaQ = (2 : ℕ) • deltaQ := by
      rw [h₇.1, h₇.2] at hrelation
      have hsub : (2 : ℤ) • deltaQ - betaQ = 0 := by
        simpa only [neg_one_zsmul, sub_eq_add_neg] using hrelation
      have heqZ : betaQ = (2 : ℤ) • deltaQ :=
        (sub_eq_zero.mp hsub).symm
      simpa only [two_nsmul, two_zsmul] using heqZ
    exact (ne_two_nsmul_of_addOrderOf_eq_same_twoPower
      ht betaQ deltaQ hbeta hdelta heq).elim

/-- Once the cycle leaves share one quotient coset, the negative profile
cannot coexist with either positive profile.  Thus the entire punctured
private matrix has one global quotient orientation. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_globalOrientation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hpow : 2 < 2 ^ t)
    (a : ZMod (2 ^ t * q))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∀ r, M.commonProfile r = (-1, -1)) ∨
      ∀ r, M.commonProfile r = (-1, 1) ∨
        M.commonProfile r = (1, -1) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  let betaQ : Fin d → Q := fun r ↦ pi (g (leaf r) - g fixed)
  have hdeltaOrder : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using M.common_full_order
  have hcoset : ∀ r s, betaQ r = betaQ s := by
    intro r s
    simpa only [betaQ, pi, H, Q] using
      cycle_quotient_displacement_eq_of_span
        g y a (g fixed) leaf hspan r s
  have hrelation : ∀ r,
      M.commonCoeff r inserted • deltaQ +
        M.commonCoeff r (leaf r) • betaQ r = 0 := by
    intro r
    simpa only [deltaQ, betaQ, pi, H, Q] using
      M.commonProfile_quotientRelation r
  have ht : 1 ≤ t := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro htZero
    subst t
    norm_num at hpow
  have hprofiles : ∀ r,
      M.commonProfile r = (-1, -1) ∨
        M.commonProfile r = (-1, 1) ∨
          M.commonProfile r = (1, -1) := by
    intro r
    have hr := M.commonProfile_mem_fullOrderProfiles ht r
    simpa only [puncturedCycleFullOrderPrivateProfiles,
      Finset.mem_insert, Finset.mem_singleton] using hr
  have hnegative : ∀ {r}, M.commonProfile r = (-1, -1) →
      betaQ r = -deltaQ := by
    intro r hr
    have hmu := congrArg Prod.fst hr
    have hlambda := congrArg Prod.snd hr
    change M.commonCoeff r inserted = -1 at hmu
    change M.commonCoeff r (leaf r) = -1 at hlambda
    have hrel := hrelation r
    rw [hmu, hlambda] at hrel
    simp only [neg_one_zsmul] at hrel
    calc
      betaQ r = - -betaQ r := (neg_neg (betaQ r)).symm
      _ = -deltaQ := neg_eq_of_add_eq_zero_left hrel
  have hpositive : ∀ {r},
      M.commonProfile r = (-1, 1) ∨ M.commonProfile r = (1, -1) →
        betaQ r = deltaQ := by
    intro r hr
    rcases hr with hr | hr
    · have hmu := congrArg Prod.fst hr
      have hlambda := congrArg Prod.snd hr
      change M.commonCoeff r inserted = -1 at hmu
      change M.commonCoeff r (leaf r) = 1 at hlambda
      have hrel := hrelation r
      rw [hmu, hlambda] at hrel
      simp only [neg_one_zsmul, one_zsmul] at hrel
      exact (neg_add_eq_zero.mp hrel).symm
    · have hmu := congrArg Prod.fst hr
      have hlambda := congrArg Prod.snd hr
      change M.commonCoeff r inserted = 1 at hmu
      change M.commonCoeff r (leaf r) = -1 at hlambda
      have hrel := hrelation r
      rw [hmu, hlambda] at hrel
      simp only [one_zsmul, neg_one_zsmul] at hrel
      exact (add_neg_eq_zero.mp hrel).symm
  have hnotSelfNeg : deltaQ ≠ -deltaQ := by
    intro hself
    have htwoZero : (2 : ℕ) • deltaQ = 0 := by
      rw [two_nsmul]
      calc
        deltaQ + deltaQ = deltaQ + -deltaQ :=
          congrArg (fun z ↦ deltaQ + z) hself
        _ = 0 := add_neg_cancel deltaQ
    have hdvd : 2 ^ t ∣ 2 := by
      rw [← hdeltaOrder]
      exact addOrderOf_dvd_of_nsmul_eq_zero htwoZero
    have hle : 2 ^ t ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  by_cases hallNegative : ∀ r, M.commonProfile r = (-1, -1)
  · exact Or.inl hallNegative
  · right
    push Not at hallNegative
    obtain ⟨r, hrNotNegative⟩ := hallNegative
    have hrCases := hprofiles r
    have hrPositive :
        M.commonProfile r = (-1, 1) ∨
          M.commonProfile r = (1, -1) := by
      rcases hrCases with hrNegative | hrPositive
      · exact (hrNotNegative hrNegative).elim
      · exact hrPositive
    intro s
    have hsCases := hprofiles s
    rcases hsCases with hsNegative | hsPositive
    · exfalso
      apply hnotSelfNeg
      calc
        deltaQ = betaQ r := (hpositive hrPositive).symm
        _ = betaQ s := hcoset r s
        _ = -deltaQ := hnegative hsNegative
    · exact hsPositive

/-- Either positive profile places the missing leaf in the same quotient
coset as the common inserted coordinate. -/
theorem PrimitivePuncturedCyclePrivateMatrix.leaf_sub_inserted_mem_of_positiveProfile
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d)
    (hpositive : M.commonProfile r = (-1, 1) ∨
      M.commonProfile r = (1, -1)) :
    g (leaf r) - g inserted ∈ AddSubgroup.zmultiples y := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  let betaQ : Q := pi (g (leaf r) - g fixed)
  have hrelation : M.commonCoeff r inserted • deltaQ +
      M.commonCoeff r (leaf r) • betaQ = 0 := by
    simpa only [deltaQ, betaQ, pi, H, Q] using
      M.commonProfile_quotientRelation r
  have hbetaEq : betaQ = deltaQ := by
    rcases hpositive with hpositive | hpositive
    · have hmu := congrArg Prod.fst hpositive
      have hlambda := congrArg Prod.snd hpositive
      change M.commonCoeff r inserted = -1 at hmu
      change M.commonCoeff r (leaf r) = 1 at hlambda
      rw [hmu, hlambda] at hrelation
      simp only [neg_one_zsmul, one_zsmul] at hrelation
      exact (neg_add_eq_zero.mp hrelation).symm
    · have hmu := congrArg Prod.fst hpositive
      have hlambda := congrArg Prod.snd hpositive
      change M.commonCoeff r inserted = 1 at hmu
      change M.commonCoeff r (leaf r) = -1 at hlambda
      rw [hmu, hlambda] at hrelation
      simp only [one_zsmul, neg_one_zsmul] at hrelation
      exact (add_neg_eq_zero.mp hrelation).symm
  apply (QuotientAddGroup.eq_zero_iff (g (leaf r) - g inserted)).1
  change pi (g (leaf r) - g inserted) = 0
  have hdecomp :
      g (leaf r) - g inserted =
        (g (leaf r) - g fixed) - (g inserted - g fixed) := by
    abel
  rw [hdecomp, map_sub]
  exact sub_eq_zero.mpr hbetaEq

/-- The positive global orientation is impossible at an exact Mersenne
kernel.  It would put the common inserted coordinate together with all `d`
injective cycle leaves in one kernel coset, forcing `2^d ≤ 2^d - 1`. -/
theorem PrimitivePuncturedCyclePrivateMatrix.not_all_positiveProfiles_of_mersenne
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hg : ValidTuple g)
    (horder : addOrderOf y = 2 ^ d - 1)
    (hpositive : ∀ r, M.commonProfile r = (-1, 1) ∨
      M.commonProfile r = (1, -1)) : False := by
  classical
  let L : Finset (Fin n) := Finset.univ.image leaf
  let S : Finset (Fin n) := insert inserted L
  have hinsertedNotL : inserted ∉ L := by
    intro hinserted
    rcases Finset.mem_image.mp hinserted with ⟨r, _hr, hr⟩
    have hleafMem : leaf r ∈ set r := by
      rw [hr]
      exact M.common_mem r
    exact ((M.leaf_mem_iff r r).1 hleafMem) rfl
  have hSnonempty : S.Nonempty := by
    exact ⟨inserted, Finset.mem_insert_self _ _⟩
  have hleafInserted : ∀ r,
      g (leaf r) - g inserted ∈ AddSubgroup.zmultiples y := by
    intro r
    exact M.leaf_sub_inserted_mem_of_positiveProfile r (hpositive r)
  have hScoset : ∀ b ∈ S, ∀ c ∈ S,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hb c hc
    rcases Finset.mem_insert.mp hb with rfl | hb
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · simp
      · rcases Finset.mem_image.mp hc with ⟨j, _hj, rfl⟩
        have hj := hleafInserted j
        have hneg := (AddSubgroup.zmultiples y).neg_mem hj
        convert hneg using 1
        abel
    · rcases Finset.mem_image.mp hb with ⟨i, _hi, rfl⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hleafInserted i
      · rcases Finset.mem_image.mp hc with ⟨j, _hj, rfl⟩
        have hij := (AddSubgroup.zmultiples y).sub_mem
          (hleafInserted i) (hleafInserted j)
        convert hij using 1
        abel
  have hLcard : L.card = d := by
    simp only [L, Finset.card_image_of_injective _ M.leaf_injective,
      Finset.card_univ, Fintype.card_fin]
  have hScard : S.card = d + 1 := by
    change (insert inserted L).card = d + 1
    rw [Finset.card_insert_of_notMem hinsertedNotL, hLcard]
  have hlower := two_pow_pred_le_addOrderOf_of_valid_kernelCoset
    g hg y S hSnonempty hScoset
  rw [horder, hScard] at hlower
  simp only [Nat.add_sub_cancel] at hlower
  have hpowPositive : 0 < 2 ^ d := pow_pos (by decide) d
  omega

/-- At an exact Mersenne kernel the global orientation is forced to be the
single negative profile. -/
theorem PrimitivePuncturedCyclePrivateMatrix.all_negativeProfile_of_mersenne
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hg : ValidTuple g)
    (hpow : 2 < 2 ^ t) (a : ZMod (2 ^ t * q))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (horder : addOrderOf y = 2 ^ d - 1) :
    ∀ r, M.commonProfile r = (-1, -1) := by
  rcases M.commonProfile_globalOrientation hpow a hspan with
    hnegative | hpositive
  · exact hnegative
  · exact (M.not_all_positiveProfiles_of_mersenne
      hg horder hpositive).elim

/-- A negative profiled row is literally the pure edge centered at the fixed
endpoint and joining the common inserted coordinate to the missing leaf. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCoeff_eq_pureEdgeCoeffs_of_negativeProfile
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d)
    (hnegative : M.commonProfile r = (-1, -1)) :
    M.commonCoeff r = pureEdgeCoeffs fixed inserted (leaf r) := by
  have hmu : M.commonCoeff r inserted = -1 :=
    congrArg Prod.fst hnegative
  have hlambda : M.commonCoeff r (leaf r) = -1 :=
    congrArg Prod.snd hnegative
  have hsum := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hfixedCoeff : M.commonCoeff r fixed = 2 := by omega
  have hsupport := (M.commonCoeff_threeSupport_sevenProfiles r).1
  have hleafNeInserted : leaf r ≠ inserted := by
    intro hli
    have hmem : leaf r ∈ set r := by
      simpa only [hli] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 hmem) rfl
  have hinsertedNeFixed : inserted ≠ fixed := by
    intro hif
    apply (M.presentation r).z_not_mem
    rw [M.fixed_second r, ← hif]
    exact M.common_mem r
  have hleafNeFixed : leaf r ≠ fixed := by
    intro hlf
    apply (M.presentation r).x_ne_z
    rw [M.missing_first r, M.fixed_second r, hlf]
  funext i
  by_cases hiFixed : i = fixed
  · subst i
    simp [pureEdgeCoeffs, hfixedCoeff, Ne.symm hinsertedNeFixed,
      Ne.symm hleafNeFixed]
  by_cases hiInserted : i = inserted
  · subst i
    simp [pureEdgeCoeffs, hmu, hinsertedNeFixed,
      Ne.symm hleafNeInserted]
  by_cases hiLeaf : i = leaf r
  · subst i
    simp [pureEdgeCoeffs, hlambda, hleafNeFixed, hleafNeInserted]
  rw [hsupport i hiInserted hiLeaf hiFixed]
  simp [pureEdgeCoeffs, hiFixed, hiInserted, hiLeaf]

/-- The all-negative target plus its leaf displacement is independent of the
puncture.  This is the constant-center recurrence left by HAD. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (a : ZMod (2 ^ t * q)) (r : Fin d)
    (hnegative : M.commonProfile r = (-1, -1)) :
    M.commonTarget r + (g (leaf r) - a) =
      (2 : ℤ) • g fixed - g inserted - a := by
  have hmu : M.commonCoeff r inserted = -1 :=
    congrArg Prod.fst hnegative
  have hlambda : M.commonCoeff r (leaf r) = -1 :=
    congrArg Prod.snd hnegative
  have hsum := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hfixedCoeff : M.commonCoeff r fixed = 2 := by omega
  have hvalue := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.2
  change M.commonScalar r • y + (g (leaf r) - a) =
    (2 : ℤ) • g fixed - g inserted - a
  rw [← hvalue, hmu, hlambda, hfixedCoeff]
  simp only [neg_one_zsmul]
  module

/-- Three distinct all-negative rows cannot realize the common center as one
signed three-leaf displacement.  Their coefficient combination `uᵢ+uⱼ-uₖ`
would otherwise be a legal nonzero witness at zero. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCenter_ne_signedThreeLeaf_of_negativeProfiles
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hg : ValidTuple g)
    (a : ZMod (2 ^ t * q))
    (hnegative : ∀ r, M.commonProfile r = (-1, -1))
    {i j k : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (2 : ℤ) • g fixed - g inserted - a ≠
      (g (leaf i) - a) + (g (leaf j) - a) - (g (leaf k) - a) := by
  intro hcenter
  let c : Fin n → ℤ :=
    M.commonCoeff i + M.commonCoeff j - M.commonCoeff k
  apply (validTuple_iff_no_zero_witness g).mp hg c
  have hshapeI := M.commonCoeff_eq_pureEdgeCoeffs_of_negativeProfile
    i (hnegative i)
  have hshapeJ := M.commonCoeff_eq_pureEdgeCoeffs_of_negativeProfile
    j (hnegative j)
  have hshapeK := M.commonCoeff_eq_pureEdgeCoeffs_of_negativeProfile
    k (hnegative k)
  have hleafIJ : leaf i ≠ leaf j := fun h ↦ hij (M.leaf_injective h)
  have hleafIK : leaf i ≠ leaf k := fun h ↦ hik (M.leaf_injective h)
  have hleafJK : leaf j ≠ leaf k := fun h ↦ hjk (M.leaf_injective h)
  have hinsertedNeFixed : inserted ≠ fixed := by
    intro hif
    apply (M.presentation i).z_not_mem
    rw [M.fixed_second i, ← hif]
    exact M.common_mem i
  have hleafNeInserted : ∀ r, leaf r ≠ inserted := by
    intro r hli
    have hmem : leaf r ∈ set r := by
      simpa only [hli] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 hmem) rfl
  have hleafNeFixed : ∀ r, leaf r ≠ fixed := by
    intro r hlf
    apply (M.presentation r).x_ne_z
    rw [M.missing_first r, M.fixed_second r, hlf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have hcfixed := congrFun hc fixed
    simp only [c, Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
      hshapeI, hshapeJ, hshapeK, pureEdgeCoeffs] at hcfixed
    simp [Ne.symm hinsertedNeFixed, Ne.symm (hleafNeFixed i),
      Ne.symm (hleafNeFixed j), Ne.symm (hleafNeFixed k)] at hcfixed
  · intro x
    simp only [c, hshapeI, hshapeJ, hshapeK, pureEdgeCoeffs,
      Pi.sub_apply, Pi.add_apply]
    have hfi := Ne.symm (hleafNeFixed i)
    have hfj := Ne.symm (hleafNeFixed j)
    have hfk := Ne.symm (hleafNeFixed k)
    have hii := Ne.symm (hleafNeInserted i)
    have hij' := Ne.symm (hleafNeInserted j)
    have hik' := Ne.symm (hleafNeInserted k)
    split_ifs <;> omega
  · simp only [c, Pi.sub_apply, Pi.add_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      (M.common_private_row i).2.1.2.2.1,
      (M.common_private_row j).2.1.2.2.1,
      (M.common_private_row k).2.1.2.2.1]
    ring
  · simp only [c, Pi.sub_apply, Pi.add_apply, add_smul, sub_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      (M.common_private_row i).2.1.2.2.2,
      (M.common_private_row j).2.1.2.2.2,
      (M.common_private_row k).2.1.2.2.2]
    have hiTarget :=
      M.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
        a i (hnegative i)
    have hjTarget :=
      M.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
        a j (hnegative j)
    have hkTarget :=
      M.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
        a k (hnegative k)
    change M.commonTarget i + M.commonTarget j - M.commonTarget k = 0
    rw [show M.commonTarget i =
        ((2 : ℤ) • g fixed - g inserted - a) - (g (leaf i) - a) by
          apply eq_sub_of_add_eq
          exact hiTarget,
      show M.commonTarget j =
        ((2 : ℤ) • g fixed - g inserted - a) - (g (leaf j) - a) by
          apply eq_sub_of_add_eq
          exact hjTarget,
      show M.commonTarget k =
        ((2 : ℤ) • g fixed - g inserted - a) - (g (leaf k) - a) by
          apply eq_sub_of_add_eq
          exact hkTarget,
      hcenter]
    module

/-- In cyclic order seven or fifteen, every nonzero element other than one of
the displayed doubling-orbit points is a signed sum of three distinct orbit
points.  This is the finite arithmetic input needed by the general row
combination obstruction above. -/
theorem exists_signedThreePowers_of_order_seven_or_fifteen
    {G : Type*} [AddCommGroup G] (v C : G) {d : ℕ}
    (hd : d = 3 ∨ d = 4) (hv : addOrderOf v = 2 ^ d - 1)
    (hCmem : C ∈ AddSubgroup.zmultiples v) (hC0 : C ≠ 0)
    (hCpower : ∀ r : Fin d, C ≠ (2 ^ r.val) • v) :
    ∃ i j k : Fin d, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      C = (2 ^ i.val) • v + (2 ^ j.val) • v - (2 ^ k.val) • v := by
  rcases hd with rfl | rfl
  · have hv' : addOrderOf v = 7 := by norm_num at hv ⊢; exact hv
    obtain ⟨s, hs0, hslt, rfl⟩ :=
      exists_positive_nsmul_eq_of_mem_zmultiples
        (v := v) (t := C) (q := 7) (by norm_num) hv' hCmem hC0
    have hvzero : (7 : ℕ) • v = 0 := by
      simpa only [hv'] using addOrderOf_nsmul_eq_zero v
    interval_cases s
    · exfalso
      exact (hCpower ⟨0, by norm_num⟩) (by norm_num)
    · exfalso
      exact (hCpower ⟨1, by norm_num⟩) (by norm_num)
    · refine ⟨⟨0, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨1, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · exfalso
      exact (hCpower ⟨2, by norm_num⟩) (by norm_num)
    · refine ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨0, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩,
        ⟨2, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      change 6 • v = 1 • v + 2 • v - 4 • v
      calc
        6 • v = 7 • v - v := by
          rw [show 7 = 6 + 1 by norm_num, add_nsmul, one_nsmul]
          abel
        _ = 0 - v := by rw [hvzero]
        _ = 1 • v + 2 • v - 4 • v := by module
  · have hv' : addOrderOf v = 15 := by norm_num at hv ⊢; exact hv
    obtain ⟨s, hs0, hslt, rfl⟩ :=
      exists_positive_nsmul_eq_of_mem_zmultiples
        (v := v) (t := C) (q := 15) (by norm_num) hv' hCmem hC0
    have hvzero : (15 : ℕ) • v = 0 := by
      simpa only [hv'] using addOrderOf_nsmul_eq_zero v
    interval_cases s
    · exfalso
      exact (hCpower ⟨0, by norm_num⟩) (by norm_num)
    · exfalso
      exact (hCpower ⟨1, by norm_num⟩) (by norm_num)
    · refine ⟨⟨0, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨1, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · exfalso
      exact (hCpower ⟨2, by norm_num⟩) (by norm_num)
    · refine ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨0, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨1, by norm_num⟩, ⟨3, by norm_num⟩,
        ⟨2, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨0, by norm_num⟩, ⟨3, by norm_num⟩,
        ⟨1, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · exfalso
      exact (hCpower ⟨3, by norm_num⟩) (by norm_num)
    · refine ⟨⟨1, by norm_num⟩, ⟨3, by norm_num⟩,
        ⟨0, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨2, by norm_num⟩, ⟨3, by norm_num⟩,
        ⟨1, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨2, by norm_num⟩, ⟨3, by norm_num⟩,
        ⟨0, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      norm_num
      module
    · refine ⟨⟨0, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨3, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      change 12 • v = 1 • v + 4 • v - 8 • v
      calc
        12 • v = 15 • v - 3 • v := by
          rw [show 15 = 12 + 3 by norm_num, add_nsmul]
          abel
        _ = 0 - 3 • v := by rw [hvzero]
        _ = 1 • v + 4 • v - 8 • v := by module
    · refine ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩,
        ⟨3, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      change 13 • v = 2 • v + 4 • v - 8 • v
      calc
        13 • v = 15 • v - 2 • v := by
          rw [show 15 = 13 + 2 by norm_num, add_nsmul]
          abel
        _ = 0 - 2 • v := by rw [hvzero]
        _ = 2 • v + 4 • v - 8 • v := by module
    · refine ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩,
        ⟨2, by norm_num⟩, by decide, by decide, by decide, ?_⟩
      change 14 • v = 1 • v + 2 • v - 4 • v
      calc
        14 • v = 15 • v - v := by
          rw [show 15 = 14 + 1 by norm_num, add_nsmul, one_nsmul]
          abel
        _ = 0 - v := by rw [hvzero]
        _ = 1 • v + 2 • v - 4 • v := by module

/-- On a three- or four-leaf full Mersenne cycle, the all-negative recurrence
forces its common center to vanish.  The proof combines the preceding cyclic
cover with the ambient-validity obstruction, so the finite arithmetic is
used only to discharge a general structural pattern. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCenter_eq_zero_of_negativeProfiles_threeOrFour
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (a : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (horder : addOrderOf y = 2 ^ d - 1)
    (hnegative : ∀ r, M.commonProfile r = (-1, -1))
    (hd : d = 3 ∨ d = 4) :
    (2 : ℤ) • g fixed - g inserted - a = 0 := by
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  let disp : Fin d → ZMod (2 ^ t * q) := fun r ↦ g (leaf r) - a
  have hdoubleN : ∀ i, disp (R i) = (2 : ℕ) • disp i := by
    intro i
    simpa only [disp, two_nsmul, two_zsmul] using hdouble i
  let root : Fin d := ⟨0, hdpos⟩
  let e : Fin d ≃ Fin d := fullCycleOrbitEquiv R hcycle hRne root
  let v : ZMod (2 ^ t * q) := disp root
  let C : ZMod (2 ^ t * q) :=
    (2 : ℤ) • g fixed - g inserted - a
  have hdispE : ∀ r : Fin d, disp (e r) = (2 ^ r.val) • v := by
    intro r
    exact fullCycleOrbitEquiv_doubling_eq_pow_two
      R hcycle hRne root disp hdoubleN r
  have hgroups : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y := by
    exact zmultiples_eq_of_isCycle_doubling_span
      R hcycle hRne disp hdoubleN y hspan root
  have hv : addOrderOf v = 2 ^ d - 1 := by
    calc
      addOrderOf v = addOrderOf y :=
        addOrderOf_eq_of_isCycle_doubling_span
          R hcycle hRne disp hdoubleN y hspan root
      _ = 2 ^ d - 1 := horder
  have hCmemY : C ∈ AddSubgroup.zmultiples y := by
    have htarget : M.commonTarget root ∈ AddSubgroup.zmultiples y :=
      (AddSubgroup.zmultiples y).zsmul_mem
        (AddSubgroup.mem_zmultiples y) (M.commonScalar root)
    have hdisp : disp root ∈ AddSubgroup.zmultiples y := by
      rw [← hspan]
      exact AddSubgroup.subset_closure ⟨root, rfl⟩
    have hadd := (AddSubgroup.zmultiples y).add_mem htarget hdisp
    have hrec :=
      M.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
        a root (hnegative root)
    change M.commonTarget root + disp root = C at hrec
    rwa [hrec] at hadd
  have hCmem : C ∈ AddSubgroup.zmultiples v := by
    rw [hgroups]
    exact hCmemY
  have hCpower : ∀ r : Fin d, C ≠ (2 ^ r.val) • v := by
    intro r hpow
    apply (M.common_private_row (e r)).1
    have hrec :=
      M.commonTarget_add_leaf_sub_base_eq_of_negativeProfile
        a (e r) (hnegative (e r))
    change M.commonTarget (e r) + disp (e r) = C at hrec
    calc
      M.commonTarget (e r) =
          (M.commonTarget (e r) + disp (e r)) - disp (e r) := by abel
      _ = C - disp (e r) := by rw [hrec]
      _ = 0 := by rw [hpow, hdispE]; abel
  change C = 0
  by_contra hC0
  obtain ⟨i, j, k, hij, hik, hjk, hsigned⟩ :=
    exists_signedThreePowers_of_order_seven_or_fifteen
      v C hd hv hCmem hC0 hCpower
  apply M.commonCenter_ne_signedThreeLeaf_of_negativeProfiles
    hg a hnegative (e.injective.ne hij) (e.injective.ne hik)
      (e.injective.ne hjk)
  change C = disp (e i) + disp (e j) - disp (e k)
  rw [hdispE, hdispE, hdispE]
  exact hsigned

/-- A displayed pure-edge value with three distinct coordinates is a legal
witness.  This small constructor lets structural endpoints expose their
coefficient vector without rebuilding the floor and sum checks. -/
theorem pureEdgeCoeffs_witness_of_value
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (h : G) (x a b : Fin n)
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hval : (2 : ℤ) • g x - g a - g b = h) :
    Witness g h (pureEdgeCoeffs x a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hx := congrFun hzero x
    simp [pureEdgeCoeffs, hxa, hxb] at hx
  · intro i
    simp only [pureEdgeCoeffs]
    split_ifs <;> omega
  · simp [pureEdgeCoeffs, Finset.sum_sub_distrib]
  · simpa [pureEdgeCoeffs, sub_smul, Finset.sum_sub_distrib] using hval

/-- A three- or four-leaf cycle always has a directed edge whose two leaf
coordinates avoid any prescribed ambient coordinate.  If the prescribed
coordinate is itself a leaf, only that leaf and its predecessor are
forbidden; two indices cannot cover a cycle of size at least three. -/
theorem exists_leaf_cycle_edge_avoiding_coordinate_threeOrFour
    {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (anchor : Fin n) :
    ∃ i : Fin d, leaf i ≠ anchor ∧ leaf (R i) ≠ anchor := by
  classical
  by_cases hanchor : ∃ j, leaf j = anchor
  · obtain ⟨j, hj⟩ := hanchor
    by_contra hnone
    have hall : (Finset.univ : Finset (Fin d)) ⊆ {j, R.symm j} := by
      intro i _hi
      by_cases hi : leaf i = anchor
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (hleafInj (hi.trans hj.symm))
      · have hRi : leaf (R i) = anchor := by
          by_contra hRi
          exact hnone ⟨i, hi, hRi⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        apply R.injective
        simpa using hleafInj (hRi.trans hj.symm)
    have hcard := Finset.card_le_card hall
    have hpair : ({j, R.symm j} : Finset (Fin d)).card ≤ 2 :=
      Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    rcases hd with rfl | rfl <;> omega
  · have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
    let i : Fin d := ⟨0, hdpos⟩
    exact ⟨i, fun hi ↦ hanchor ⟨i, hi⟩,
      fun hRi ↦ hanchor ⟨R i, hRi⟩⟩

/-- A full relative-doubling cycle of length three or four whose affine base
is `h + g anchor` already contains a literal pure-edge witness at `h`.
Choose an edge avoiding the anchor and rewrite its doubling identity as
`2*g(source) - g(target) - g(anchor) = h`. -/
theorem fullDoublingCycle_pureEdgeWitness_of_threeOrFour
    {d : ℕ} {G : Type*} [AddCommGroup G]
    (hd : d = 3 ∨ d = 4)
    (g : Fin n → G) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (a h : G) (anchor : Fin n) (hbase : a = h + g anchor)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, Witness g h (pureEdgeCoeffs x z anchor) := by
  obtain ⟨i, hiAnchor, hRiAnchor⟩ :=
    exists_leaf_cycle_edge_avoiding_coordinate_threeOrFour
      hd leaf hleafInj R anchor
  have hiRi : leaf i ≠ leaf (R i) := by
    intro heq
    exact hRne i (hleafInj heq).symm
  have hvalue :
      (2 : ℤ) • g (leaf i) - g (leaf (R i)) - g anchor = h := by
    have hdbl := hdouble i
    have hcenter :
        (2 : ℤ) • g (leaf i) - g (leaf (R i)) - a = 0 := by
      calc
        (2 : ℤ) • g (leaf i) - g (leaf (R i)) - a =
            (2 : ℤ) • (g (leaf i) - a) -
              (g (leaf (R i)) - a) := by module
        _ = 0 := by rw [← hdbl]; simp
    calc
      (2 : ℤ) • g (leaf i) - g (leaf (R i)) - g anchor =
          ((2 : ℤ) • g (leaf i) - g (leaf (R i)) - a) + h := by
            rw [hbase, two_zsmul]
            abel
      _ = 0 + h := by rw [hcenter]
      _ = h := zero_add h
  exact ⟨leaf i, leaf (R i),
    pureEdgeCoeffs_witness_of_value g h (leaf i) (leaf (R i)) anchor
      hiRi hiAnchor hRiAnchor hvalue⟩

/-- A zero pure-edge center cannot use the affine anchor as either retained
endpoint when their quotient difference has order greater than four.  In
either collision the retained difference becomes four-torsion in the ambient
group, hence also in the quotient, contradicting its full two-power order. -/
theorem fullOrder_pureEdgeCenter_endpoints_ne_anchor
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q))
    {h a : ZMod (2 ^ t * q)} (hh : h + h = 0)
    (inserted fixed anchor : Fin n)
    (horder : addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g inserted - g fixed)) = 2 ^ t)
    (hpow : 4 < 2 ^ t) (hbase : a = h + g anchor)
    (hcenter : (2 : ℤ) • g fixed - g inserted - a = 0) :
    inserted ≠ anchor ∧ fixed ≠ anchor := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  have horder' : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using horder
  have hnotFourTorsion : ¬ (4 : ℕ) • deltaQ = 0 := by
    intro hzero
    have hdvd : addOrderOf deltaQ ∣ 4 :=
      addOrderOf_dvd_of_nsmul_eq_zero hzero
    rw [horder'] at hdvd
    have hle : 2 ^ t ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  constructor
  · intro hinserted
    have hfourAmbient :
        (4 : ℕ) • (g inserted - g fixed) = 0 := by
      rw [hbase, ← hinserted] at hcenter
      have htwoDiff :
          (2 : ℤ) • (g fixed - g inserted) = h := by
        calc
          (2 : ℤ) • (g fixed - g inserted) =
              ((2 : ℤ) • g fixed - g inserted -
                (h + g inserted)) + h := by module
          _ = 0 + h := by rw [hcenter]
          _ = h := zero_add h
      have htwoH : (2 : ℤ) • h = 0 := by
        simpa only [two_zsmul] using hh
      have hfourAmbientZ :
          (4 : ℤ) • (g inserted - g fixed) = 0 := by
        calc
          (4 : ℤ) • (g inserted - g fixed) =
              -((2 : ℤ) • ((2 : ℤ) • (g fixed - g inserted))) := by
                module
          _ = -((2 : ℤ) • h) := by rw [htwoDiff]
          _ = 0 := by rw [htwoH]; simp
      exact_mod_cast hfourAmbientZ
    apply hnotFourTorsion
    change (4 : ℕ) • pi (g inserted - g fixed) = 0
    rw [← map_nsmul, hfourAmbient, map_zero]
  · intro hfixed
    have hfourAmbient :
        (4 : ℕ) • (g inserted - g fixed) = 0 := by
      rw [hbase, ← hfixed] at hcenter
      have hdiff : g fixed - g inserted = h := by
        calc
          g fixed - g inserted =
              ((2 : ℤ) • g fixed - g inserted -
                (h + g fixed)) + h := by module
          _ = 0 + h := by rw [hcenter]
          _ = h := zero_add h
      have htwoH : (2 : ℤ) • h = 0 := by
        simpa only [two_zsmul] using hh
      have hfourAmbientZ :
          (4 : ℤ) • (g inserted - g fixed) = 0 := by
        calc
          (4 : ℤ) • (g inserted - g fixed) =
              -((2 : ℤ) • ((2 : ℤ) • (g fixed - g inserted))) := by
                module
          _ = -((2 : ℤ) • ((2 : ℤ) • h)) := by rw [hdiff]
          _ = 0 := by rw [htwoH]; simp
      exact_mod_cast hfourAmbientZ
    apply hnotFourTorsion
    change (4 : ℕ) • pi (g inserted - g fixed) = 0
    rw [← map_nsmul, hfourAmbient, map_zero]

/-- Restore the original affine base `h + g(anchor)` after the order-seven or
order-fifteen center obstruction.  The resulting identity is the literal
pure-edge witness at the half target `h`, an accepted upstream G1 currency. -/
theorem PrimitivePuncturedCyclePrivateMatrix.pureEdgeWitness_of_mersenne_threeOrFour
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (a : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 2 < 2 ^ t) (horder : addOrderOf y = 2 ^ d - 1)
    (hd : d = 3 ∨ d = 4)
    (h : ZMod (2 ^ t * q)) (anchor : Fin n)
    (hbase : a = h + g anchor)
    (hfixedAnchor : fixed ≠ anchor)
    (hinsertedAnchor : inserted ≠ anchor) :
    Witness g h (pureEdgeCoeffs fixed inserted anchor) := by
  have hnegative :=
    M.all_negativeProfile_of_mersenne hg hpow a hspan horder
  have hcenter :=
    M.commonCenter_eq_zero_of_negativeProfiles_threeOrFour
      hg R hcycle hRne a hdouble hspan horder hnegative hd
  have hinsertedNeFixed : inserted ≠ fixed := by
    have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
    let r : Fin d := ⟨0, hdpos⟩
    intro hif
    apply (M.presentation r).z_not_mem
    rw [M.fixed_second r, ← hif]
    exact M.common_mem r
  have hvalue :
      (2 : ℤ) • g fixed - g inserted - g anchor = h := by
    rw [hbase] at hcenter
    calc
      (2 : ℤ) • g fixed - g inserted - g anchor =
          ((2 : ℤ) • g fixed - g inserted - (h + g anchor)) + h := by
            abel
      _ = 0 + h := by rw [hcenter]
      _ = h := zero_add h
  exact pureEdgeCoeffs_witness_of_value
    g h fixed inserted anchor hinsertedNeFixed.symm
      hfixedAnchor hinsertedAnchor hvalue

/-- Rows in one exact profile differ only through their missing-leaf term. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonTarget_sub_eq_zsmul_leaf_sub_of_profile_eq
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) {r s : Fin d}
    (hprofile : M.commonProfile r = M.commonProfile s) :
    M.commonTarget s - M.commonTarget r =
      M.commonCoeff r (leaf r) • (g (leaf s) - g (leaf r)) := by
  have hmu : M.commonCoeff r inserted = M.commonCoeff s inserted := by
    exact congrArg Prod.fst hprofile
  have hlambda :
      M.commonCoeff r (leaf r) = M.commonCoeff s (leaf s) := by
    exact congrArg Prod.snd hprofile
  have hsumR := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hsumS := (M.commonCoeff_threeSupport_sevenProfiles s).2.1
  have hfixed : M.commonCoeff r fixed = M.commonCoeff s fixed := by
    omega
  have hvalueR := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.2
  have hvalueS := (M.commonCoeff_threeSupport_sevenProfiles s).2.2.2
  calc
    M.commonTarget s - M.commonTarget r =
        (M.commonCoeff s inserted • g inserted +
          M.commonCoeff s (leaf s) • g (leaf s) +
          M.commonCoeff s fixed • g fixed) -
        (M.commonCoeff r inserted • g inserted +
          M.commonCoeff r (leaf r) • g (leaf r) +
          M.commonCoeff r fixed • g fixed) := by
            rw [hvalueS, hvalueR]
            rfl
    _ = M.commonCoeff r (leaf r) •
        (g (leaf s) - g (leaf r)) := by
      rw [← hmu, ← hlambda, ← hfixed]
      module

/-- On an edge that stays inside one profile, the private target difference
is the missing-leaf coefficient times the original doubling displacement. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonTarget_cycleEdge_sub_eq
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (r : Fin d) (hprofile : M.commonProfile (R r) = M.commonProfile r) :
    M.commonTarget (R r) - M.commonTarget r =
      M.commonCoeff r (leaf r) • (g (leaf r) - a) := by
  have htarget :=
    M.commonTarget_sub_eq_zsmul_leaf_sub_of_profile_eq hprofile.symm
  have hleafDiff : g (leaf (R r)) - g (leaf r) = g (leaf r) - a := by
    have hr := hdouble r
    calc
      g (leaf (R r)) - g (leaf r) =
          (g (leaf (R r)) - a) - (g (leaf r) - a) := by abel
      _ = (2 : ℤ) • (g (leaf r) - a) - (g (leaf r) - a) := by
        rw [hr]
      _ = g (leaf r) - a := by module
  rw [hleafDiff] at htarget
  exact htarget

/-- Either of the two zero-missing-coefficient profiles occurs at most once.
Indeed its exact three-supported coefficient vector is determined entirely by
the profile, so HY's cross-puncture injectivity identifies the punctures. -/
theorem PrimitivePuncturedCyclePrivateMatrix.eq_of_commonProfile_eq_of_missingCoeff_eq_zero
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (hcoeffInjective : Function.Injective M.commonCoeff)
    {r s : Fin d} (hmissing : M.commonCoeff r (leaf r) = 0)
    (hprofile : M.commonProfile r = M.commonProfile s) : r = s := by
  apply hcoeffInjective
  have hmu : M.commonCoeff r inserted = M.commonCoeff s inserted :=
    congrArg Prod.fst hprofile
  have hlambda :
      M.commonCoeff r (leaf r) = M.commonCoeff s (leaf s) :=
    congrArg Prod.snd hprofile
  have hmissingS : M.commonCoeff s (leaf s) = 0 := by
    rw [← hlambda, hmissing]
  have hsumR := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hsumS := (M.commonCoeff_threeSupport_sevenProfiles s).2.1
  have hfixed : M.commonCoeff r fixed = M.commonCoeff s fixed := by omega
  have hsupportR := (M.commonCoeff_threeSupport_sevenProfiles r).1
  have hsupportS := (M.commonCoeff_threeSupport_sevenProfiles s).1
  funext i
  by_cases hiInserted : i = inserted
  · subst i
    exact hmu
  by_cases hiFixed : i = fixed
  · subst i
    exact hfixed
  have hzeroR : M.commonCoeff r i = 0 := by
    by_cases hiLeaf : i = leaf r
    · subst i
      exact hmissing
    · exact hsupportR i hiInserted hiLeaf hiFixed
  have hzeroS : M.commonCoeff s i = 0 := by
    by_cases hiLeaf : i = leaf s
    · subst i
      exact hmissingS
    · exact hsupportS i hiInserted hiLeaf hiFixed
  rw [hzeroR, hzeroS]

theorem PrimitivePuncturedCyclePrivateMatrix.zeroMissing_profileFiber_card_le_one
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (hcoeffInjective : Function.Injective M.commonCoeff)
    (profile : ℤ × ℤ) (hzero : profile.2 = 0) :
    (Finset.univ.filter
      (fun r : Fin d ↦ M.commonProfile r = profile)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro r hr s hs
  have hrProfile := (Finset.mem_filter.mp hr).2
  have hsProfile := (Finset.mem_filter.mp hs).2
  have hrMissing : M.commonCoeff r (leaf r) = 0 := by
    calc
      M.commonCoeff r (leaf r) = (M.commonProfile r).2 := rfl
      _ = profile.2 := congrArg Prod.snd hrProfile
      _ = 0 := hzero
  exact M.eq_of_commonProfile_eq_of_missingCoeff_eq_zero hcoeffInjective
    hrMissing (hrProfile.trans hsProfile.symm)

/-- Private coefficient rows attached to distinct punctures are distinct.
If two rows agreed, privacy in the other puncture would make the missing-leaf
coefficient zero.  The normalized row would then kill twice the common
inserted-to-fixed difference, contradicting its full `2^t` quotient order. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCoeff_injective
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hpow : 2 < 2 ^ t) :
    Function.Injective M.commonCoeff := by
  intro r s hrs
  by_contra hrsNe
  have hrMemS : leaf r ∈ set s :=
    (M.leaf_mem_iff s r).2 hrsNe
  have hrNeInserted : leaf r ≠ inserted := by
    intro hri
    have : leaf r ∈ set r := by simpa only [hri] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 this) rfl
  have hzeroS : M.commonCoeff s (leaf r) = 0 :=
    (M.presentation s).zero_other (M.commonOwner s)
      (leaf r) hrMemS hrNeInserted
  have hzeroR : M.commonCoeff r (leaf r) = 0 := by
    rw [hrs]
    exact hzeroS
  have hweightR :
      (M.presentation r).weight (M.commonOwner r) = 0 := by
    rw [(M.presentation r).weight_eq, M.missing_first r]
    change twoRetainedOwnerNormalization
      (M.commonCoeff r inserted) * M.commonCoeff r (leaf r) = 0
    rw [hzeroR, mul_zero]
  let pFive :=
    (M.presentation r).toFiveWeightPresentation g y (set r)
  have hrow := pFive.row_mem (M.commonOwner r)
  have hmem :
      (2 : ℤ) • (g inserted - g fixed) ∈ AddSubgroup.zmultiples y := by
    change (2 : ℤ) • (g inserted - g (M.presentation r).z) +
      (M.presentation r).weight (M.commonOwner r) •
        (g (M.presentation r).x - g (M.presentation r).z) ∈
          AddSubgroup.zmultiples y at hrow
    rw [M.fixed_second r, hweightR, zero_zsmul, add_zero] at hrow
    exact hrow
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  have hzeroZ : (2 : ℤ) • deltaQ = 0 := by
    rw [← map_zsmul]
    exact (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g inserted - g fixed))).2 hmem
  have hzeroN : (2 : ℕ) • deltaQ = 0 := by
    simpa only [two_nsmul, two_zsmul] using hzeroZ
  have horder : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using M.common_full_order
  have hdvd : 2 ^ t ∣ 2 := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzeroN
  have hle : 2 ^ t ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The constant cycle and the exact quotient-row normal form use one and the
same presentation.  In particular, no orientation or existential witness is
lost before the positive-stratum descent step. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_exactPresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      PrimitiveTwoRetainedPositiveStratumPresentation g y B p ∧
      ∀ i j,
        p.weight ⟨leaf i, hleafB i⟩ =
          p.weight ⟨leaf j, hleafB j⟩ := by
  rcases hstate with ⟨hmin, hretained, hrows, p, hpfull⟩
  refine ⟨p, ⟨hmin, hretained, hrows, hpfull⟩, ?_⟩
  exact p.fullDeleted_weight_constant_of_fullOrder
    g y B hpfull.1 hpow hd leaf R a hleafB hdouble

/-- In a full-order positive-stratum state, a fully deleted doubling cycle
has constant five-weight label as soon as the quotient order exceeds the
universal coefficient bound `18` from `fullDeletedCycle_split`. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_weight_constant_of_eighteen_lt_twoPower
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∀ i j,
        weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩ := by
  classical
  rcases hstate with ⟨_hmin, _hretained, hrows, p, hpfull⟩
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  have hpOrder : addOrderOf (pi (g p.x - g p.z)) = 2 ^ t := by
    simpa only [pi, H, Q] using hpfull.1
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hsmall | hconstant⟩ :=
    hrows.fullDeletedCycle_split g y B hd leaf R a hleafB hdouble
  · have hxCase : x = p.x ∨ x = p.z := by
      have hxMem : x ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
      rw [p.complement_eq] at hxMem
      simpa using hxMem
    have hzCase : z = p.x ∨ z = p.z := by
      have hzMem : z ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
      rw [p.complement_eq] at hzMem
      simpa using hzMem
    have hxzOrder : addOrderOf (pi (g x - g z)) = 2 ^ t := by
      rcases hxCase with hxpX | hxpZ
      · have hzpZ : z = p.z := hzCase.resolve_left (by
          intro hzpX
          exact hxz (hxpX.trans hzpX.symm))
        simpa only [hxpX, hzpZ] using hpOrder
      · have hzpX : z = p.x := hzCase.resolve_right (by
          intro hzpZ
          exact hxz (hxpZ.trans hzpZ.symm))
        have hneg : g x - g z = -(g p.x - g p.z) := by
          rw [hxpZ, hzpX]
          abel
        rw [hneg, map_neg, addOrderOf_neg]
        exact hpOrder
    obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
    have heQuotient : e • pi (g x - g z) = 0 := by
      rw [← map_zsmul]
      exact (QuotientAddGroup.eq_zero_iff (e • (g x - g z))).2 heMem
    have hnatQuotient : e.natAbs • pi (g x - g z) = 0 := by
      rw [← natCast_zsmul]
      rcases Int.natAbs_eq e with hePos | heNeg
      · rw [hePos] at heQuotient
        exact heQuotient
      · rw [heNeg, neg_smul] at heQuotient
        exact neg_eq_zero.mp heQuotient
    have horderDvd : 2 ^ t ∣ e.natAbs := by
      rw [← hxzOrder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hnatQuotient
    have horderLe : 2 ^ t ≤ e.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hconstant⟩

/-- Fifth-stratum specialization of full-order fully-deleted-cycle
constancy. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_weight_constant_of_fifthStratum
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ 5 * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∀ i j,
        weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩ := by
  exact hstate.fullDeletedCycle_weight_constant_of_eighteen_lt_twoPower
    g y B (by norm_num) hd leaf R a hleafB hdouble

/-- Minimize one literal positive-stratum primitive-owner exchange.  A strict
shrink enters C2; equality retains the literal exchanged deletion set as a
full-order two-retained state. -/
theorem exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g b - g z)) = 2 ^ t)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedPositiveStratumRows g y
        (insert x (B.erase b)) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have htwo : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hquotientNe : pi (g b - g z) ≠ 0 := by
    intro hzero
    have horder : addOrderOf (pi (g b - g z)) = 2 ^ t := by
      simpa only [pi, H] using hprimitive
    rw [hzero] at horder
    norm_num at horder
    omega
  have hdiff : g b - g z ∉ AddSubgroup.zmultiples y := by
    intro hmem
    exact hquotientNe ((QuotientAddGroup.eq_zero_iff (g b - g z)).2 hmem)
  let Bexchange : Finset (Fin n) := insert x (B.erase b)
  have hBexchange : CyclicKernelSupportTransversal g y Bexchange := by
    simpa only [Bexchange] using
      cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
        g y hmin.1 hb hxB hzB hxz hcomplement hdiff
  obtain ⟨B₀, hB₀sub, hB₀min⟩ :=
    exists_minimalCyclicKernelSupportTransversal_subset g y hBexchange
  have hBexchangeCard : Bexchange.card = B.card := by
    simpa only [Bexchange] using card_erase_insert_retained_eq hb hxB
  have hB₀card : B₀.card ≤ B.card := by
    calc
      B₀.card ≤ Bexchange.card := Finset.card_le_card hB₀sub
      _ = B.card := hBexchangeCard
  by_cases hstrict : B₀.card < B.card
  · left
    refine ⟨B₀, hB₀min, ?_⟩
    have hBcard : B.card ≤ n := by
      simpa using Finset.card_le_univ B
    omega
  · right
    have hcardEq : B₀.card = B.card := by omega
    have hB₀eq : B₀ = Bexchange := by
      apply Finset.eq_of_subset_of_card_le hB₀sub
      rw [hBexchangeCard, hcardEq]
    have hretained₀ : n - B₀.card = 2 := by omega
    have hrows₀ := twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
      g hg hh hne hunique hno y hB₀min hretained₀
    have hfive₀ := hrows₀.fiveWeightRows g y B₀
    obtain ⟨p₀⟩ := hfive₀.fiveWeightPresentation g y B₀
    have hcomplement₀ : Finset.univ \ B₀ = {b, z} := by
      rw [hB₀eq]
      simpa only [Bexchange] using
        complement_erase_insert_retained hb hxB hzB hxz hcomplement
    have hp₀x : p₀.x = b ∨ p₀.x = z := by
      have hxMem : p₀.x ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.x_not_mem⟩
      rw [hcomplement₀] at hxMem
      simpa using hxMem
    have hp₀z : p₀.z = b ∨ p₀.z = z := by
      have hzMem : p₀.z ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.z_not_mem⟩
      rw [hcomplement₀] at hzMem
      simpa using hzMem
    have hp₀primitive : addOrderOf (pi (g p₀.x - g p₀.z)) = 2 ^ t := by
      rcases hp₀x with hxb | hxz'
      · have hzz : p₀.z = z := hp₀z.resolve_left (by
          intro hzb
          exact p₀.x_ne_z (hxb.trans hzb.symm))
        simpa only [hxb, hzz, pi, H] using hprimitive
      · have hzb : p₀.z = b := hp₀z.resolve_right (by
          intro hzz
          exact p₀.x_ne_z (hxz'.trans hzz.symm))
        have hneg : g p₀.x - g p₀.z = -(g b - g z) := by
          rw [hxz', hzb]
          abel
        rw [hneg, map_neg, addOrderOf_neg]
        simpa only [pi, H] using hprimitive
    have hnormal := p₀.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
      ht g hg hunique hne y hyq hfullOdd B₀ hfive₀ hminimal
    have hhalfLt : 2 ^ (t - 1) < 2 ^ t :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hsolved :
        ∀ b₀ : ↥B₀, ∃ k : ℤ, p₀.weight b₀ = 2 * k ∧
          (pi (g (b₀ : Fin n) - g p₀.z) =
              -(k • pi (g p₀.x - g p₀.z)) ∨
            pi (g (b₀ : Fin n) - g p₀.z) =
              (2 ^ (t - 1) : ℕ) • pi (g p₀.x - g p₀.z) -
                k • pi (g p₀.x - g p₀.z)) := by
      rcases hnormal with hfirst | hhalf | hfull
      · have hpowOne : 2 ^ t = 1 := by
          exact hp₀primitive.symm.trans hfirst.2.1
        omega
      · have hpowHalf : 2 ^ t = 2 ^ (t - 1) := by
          exact hp₀primitive.symm.trans hhalf.1
        omega
      · simpa only [pi, H] using hfull.2
    have hstate₀ : PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
      refine ⟨hB₀min, hretained₀, hfive₀, p₀, ?_⟩
      simpa only [pi, H] using And.intro hp₀primitive hsolved
    rw [hB₀eq] at hstate₀
    simpa only [Bexchange] using hstate₀

/-- Exchange any named deleted owner in an explicit full-order presentation.
One of the two retained orientations is primitive, so minimization either
enters C2 or preserves one of the two literal exchanged deletion sets as a
new full-order exact-two state. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_owner_to_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    (b : ↥B) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.x (B.erase (b : Fin n))) ∨
        PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.z (B.erase (b : Fin n))) := by
  classical
  have horientation := hpres.owner_primitive_at_one_retained g y B p b
  rcases hpres with ⟨hmin, hretained, hrows, _hfull⟩
  rcases horientation with hprimitiveZ | hprimitiveX
  · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained b.property
          p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq hprimitiveZ
            hminimal with
      hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr (Or.inl hexact)
  · have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
      simpa only [pair_comm] using p.complement_eq
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained b.property
          p.z_not_mem p.x_not_mem p.x_ne_z.symm hcomplementReverse
            hprimitiveX hminimal with
      hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr (Or.inr hexact)

/-- On a fully deleted cycle, exchanging any chosen leaf either enters C2 or
produces a literal one-retained-leaf cycle state.  This is the uniform
full-to-punctured transition needed for the remaining positive-stratum
descent. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_fullDeleted_cycleLeaf_to_oneRetained_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (hleafB : ∀ i, leaf i ∈ B) (r : Fin d) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.x (B.erase (leaf r))) ∧
        ∀ i, leaf i ∈ insert p.x (B.erase (leaf r)) ↔ i ≠ r) ∨
      (PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.z (B.erase (leaf r))) ∧
        ∀ i, leaf i ∈ insert p.z (B.erase (leaf r)) ↔ i ≠ r) := by
  classical
  have hrB : leaf r ∈ B := hleafB r
  let b : ↥B := ⟨leaf r, hrB⟩
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  rcases hpres.exchange_owner_to_fullOrder_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal b with
    hthree | hx | hz
  · exact Or.inl hthree
  · exact Or.inr (Or.inl ⟨by simpa only [b] using hx,
      cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside⟩)
  · exact Or.inr (Or.inr ⟨by simpa only [b] using hz,
      cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside⟩)

/-- The odd-kernel cycle coset makes the primitive exchange orientation
uniform over all fully deleted leaves.  Therefore either one leaf exchange
enters C2, or every leaf simultaneously supplies a literal full-order
exact-two transversal using the same retained endpoint. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ((∀ r,
          PrimitiveTwoRetainedPositiveStratumRows g y
            (insert p.x (B.erase (leaf r)))) ∧
        Function.Injective
          (fun r ↦ insert p.x (B.erase (leaf r)))) ∨
      ((∀ r,
          PrimitiveTwoRetainedPositiveStratumRows g y
            (insert p.z (B.erase (leaf r)))) ∧
        Function.Injective
          (fun r ↦ insert p.z (B.erase (leaf r)))) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let r₀ : Fin d := ⟨0, hd⟩
  have hcosetZ : ∀ r,
      pi (g (leaf r) - g p.z) = pi (g (leaf r₀) - g p.z) := by
    intro r
    exact cycle_quotient_displacement_eq_of_span
      g y a (g p.z) leaf hspan r r₀
  have hcosetX : ∀ r,
      pi (g (leaf r) - g p.x) = pi (g (leaf r₀) - g p.x) := by
    intro r
    exact cycle_quotient_displacement_eq_of_span
      g y a (g p.x) leaf hspan r r₀
  let b₀ : ↥B := ⟨leaf r₀, hleafB r₀⟩
  have horientation := hpres.owner_primitive_at_one_retained g y B p b₀
  rcases hpres with ⟨hmin, hretained, _hrows, _hfull⟩
  rcases horientation with hprimitiveZ | hprimitiveX
  · by_cases hthree : ∃ r : Fin d, ∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card
    · obtain ⟨_r, B₀, hB₀⟩ := hthree
      exact Or.inl ⟨B₀, hB₀⟩
    · right
      left
      refine ⟨?_, insert_erase_cycleLeaf_injective
        leaf hleafInj hleafB p.x_not_mem⟩
      intro r
      have hprimitiveZr :
          addOrderOf (pi (g (leaf r) - g p.z)) = 2 ^ t := by
        rw [hcosetZ r]
        simpa only [b₀, pi, H, Q] using hprimitiveZ
      let br : ↥B := ⟨leaf r, hleafB r⟩
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            br.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
              hprimitiveZr hminimal with
        hthreeR | hexact
      · exfalso
        apply hthree
        exact ⟨r, hthreeR⟩
      · simpa only [br] using hexact
  · by_cases hthree : ∃ r : Fin d, ∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card
    · obtain ⟨_r, B₀, hB₀⟩ := hthree
      exact Or.inl ⟨B₀, hB₀⟩
    · right
      right
      refine ⟨?_, insert_erase_cycleLeaf_injective
        leaf hleafInj hleafB p.z_not_mem⟩
      intro r
      have hprimitiveXr :
          addOrderOf (pi (g (leaf r) - g p.x)) = 2 ^ t := by
        rw [hcosetX r]
        simpa only [b₀, pi, H, Q] using hprimitiveX
      have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
        simpa only [pair_comm] using p.complement_eq
      let br : ↥B := ⟨leaf r, hleafB r⟩
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            br.property p.z_not_mem p.x_not_mem p.x_ne_z.symm
              hcomplementReverse hprimitiveXr hminimal with
        hthreeR | hexact
      · exfalso
        apply hthree
        exact ⟨r, hthreeR⟩
      · simpa only [br] using hexact

/-- Simultaneous cycle exchange in a directly comparable row normal form.
Unless C2 is reached, every missing leaf has a distinct punctured transversal
whose retained pair is oriented as `(missing leaf, fixed endpoint)` and whose
surviving cycle rows all have weight `-2`. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_to_purePresentations_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 4 < 2 ^ t) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ((∀ r,
          PrimitiveOneRetainedCyclePurePresentation g y
            (insert p.x (B.erase (leaf r))) leaf r p.z) ∧
        Function.Injective
          (fun r ↦ insert p.x (B.erase (leaf r)))) ∨
      ((∀ r,
          PrimitiveOneRetainedCyclePurePresentation g y
            (insert p.z (B.erase (leaf r))) leaf r p.x) ∧
        Function.Injective
          (fun r ↦ insert p.z (B.erase (leaf r)))) := by
  classical
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  rcases hpres.exchange_all_fullDeleted_cycleLeaves_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal hd leaf
        hleafInj a hleafB hspan with
    hthree | hx | hz
  · exact Or.inl hthree
  · right
    left
    refine ⟨?_, hx.2⟩
    intro r
    let Br : Finset (Fin n) := insert p.x (B.erase (leaf r))
    have hincidence : ∀ i, leaf i ∈ Br ↔ i ≠ r := by
      simpa only [Br] using cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside
    have hzBr : p.z ∉ Br := by
      simp only [Br, Finset.mem_insert, Finset.mem_erase, Ne.symm p.x_ne_z,
        false_or, p.z_not_mem, and_false, not_false_eq_true]
    have hrz : leaf r ≠ p.z := by
      intro hrz
      apply p.z_not_mem
      rw [← hrz]
      exact hleafB r
    apply PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
      g y Br (by simpa only [Br] using hx.1 r) hpow leaf a r hincidence
        hspan p.z hzBr hrz
  · right
    right
    refine ⟨?_, hz.2⟩
    intro r
    let Br : Finset (Fin n) := insert p.z (B.erase (leaf r))
    have hincidence : ∀ i, leaf i ∈ Br ↔ i ≠ r := by
      simpa only [Br] using cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside
    have hxBr : p.x ∉ Br := by
      simp only [Br, Finset.mem_insert, Finset.mem_erase, p.x_ne_z,
        false_or, p.x_not_mem, and_false, not_false_eq_true]
    have hrx : leaf r ≠ p.x := by
      intro hrx
      apply p.x_not_mem
      rw [← hrx]
      exact hleafB r
    apply PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
      g y Br (by simpa only [Br] using hz.1 r) hpow leaf a r hincidence
        hspan p.x hxBr hrx

/-- The simultaneous pure family carries an injective matrix of canonical
private witnesses at its one common inserted owner.  This is the first
cross-puncture invariant: the rows themselves, not only their deletion sets,
are pairwise distinct. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_to_injectivePrivateMatrix_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 4 < 2 ^ t) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (∃ M : PrimitivePuncturedCyclePrivateMatrix g y
          (fun r ↦ insert p.x (B.erase (leaf r))) leaf p.x p.z,
        Function.Injective M.commonCoeff) ∨
      (∃ M : PrimitivePuncturedCyclePrivateMatrix g y
          (fun r ↦ insert p.z (B.erase (leaf r))) leaf p.z p.x,
        Function.Injective M.commonCoeff) := by
  classical
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  have hcommonX :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t := by
    simpa using hpres.2.2.2.1
  have hcommonZ :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.z - g p.x)) = 2 ^ t := by
    have hneg : g p.z - g p.x = -(g p.x - g p.z) := by abel
    rw [hneg, map_neg, addOrderOf_neg]
    exact hcommonX
  rcases hpres.exchange_all_fullDeleted_cycleLeaves_to_purePresentations_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal hd leaf
        hleafInj a hleafB hspan hpow with
    hthree | hx | hz
  · exact Or.inl hthree
  · right
    left
    have hincidence : ∀ r i,
        leaf i ∈ insert p.x (B.erase (leaf r)) ↔ i ≠ r := by
      intro r
      exact cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside
    obtain ⟨M⟩ := exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
      g y (fun r ↦ insert p.x (B.erase (leaf r))) leaf p.x p.z a hx.1
        hleafInj (fun r ↦ Finset.mem_insert_self _ _) hincidence hx.2
          hcommonX hpow hspan
    exact ⟨M, M.commonCoeff_injective (by omega)⟩
  · right
    right
    have hincidence : ∀ r i,
        leaf i ∈ insert p.z (B.erase (leaf r)) ↔ i ≠ r := by
      intro r
      exact cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside
    obtain ⟨M⟩ := exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
      g y (fun r ↦ insert p.z (B.erase (leaf r))) leaf p.z p.x a hz.1
        hleafInj (fun r ↦ Finset.mem_insert_self _ _) hincidence hz.2
          hcommonZ hpow hspan
    exact ⟨M, M.commonCoeff_injective (by omega)⟩

/-- Preserve the original affine base and full-cycle data through the
simultaneous puncture construction.  The matrix branch is then no longer a
dangling terminal: for the live Mersenne cycles it returns one of the two
orientation-equivalent pure-edge witnesses at `h`, while strict
re-minimization still enters the existing three-retained C2 currency. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_to_pureEdgeWitness_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : d = 3 ∨ d = 4) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 4 < 2 ^ t) (horder : addOrderOf y = 2 ^ d - 1)
    (anchor : Fin n) (hbase : a = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      Witness g h (pureEdgeCoeffs p.z p.x anchor) ∨
      Witness g h (pureEdgeCoeffs p.x p.z anchor) := by
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  rcases hpres.exchange_all_fullDeleted_cycleLeaves_to_injectivePrivateMatrix_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal hdpos leaf
        hleafInj a hleafB hspan hpow with
    hthree | hmatrixX | hmatrixZ
  · exact Or.inl hthree
  · rcases hmatrixX with ⟨M, _hcoeffInjective⟩
    have hnegative :=
      M.all_negativeProfile_of_mersenne hg (by omega) a hspan horder
    have hcenter :=
      M.commonCenter_eq_zero_of_negativeProfiles_threeOrFour
        hg R hcycle hRne a hdouble hspan horder hnegative hd
    have hquotientOrder :
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t := by
      simpa using hpres.2.2.2.1
    have hanchors := fullOrder_pureEdgeCenter_endpoints_ne_anchor
      g y hh p.x p.z anchor hquotientOrder hpow hbase hcenter
    right
    left
    exact M.pureEdgeWitness_of_mersenne_threeOrFour
      hg R hcycle hRne a hdouble hspan (by omega) horder hd h anchor hbase
        hanchors.2 hanchors.1
  · rcases hmatrixZ with ⟨M, _hcoeffInjective⟩
    have hnegative :=
      M.all_negativeProfile_of_mersenne hg (by omega) a hspan horder
    have hcenter :=
      M.commonCenter_eq_zero_of_negativeProfiles_threeOrFour
        hg R hcycle hRne a hdouble hspan horder hnegative hd
    have hquotientOrder :
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.z - g p.x)) = 2 ^ t := by
      have hneg : g p.z - g p.x = -(g p.x - g p.z) := by abel
      rw [hneg, map_neg, addOrderOf_neg]
      simpa using hpres.2.2.2.1
    have hanchors := fullOrder_pureEdgeCenter_endpoints_ne_anchor
      g y hh p.z p.x anchor hquotientOrder hpow hbase hcenter
    right
    right
    exact M.pureEdgeWitness_of_mersenne_threeOrFour
      hg R hcycle hRne a hdouble hspan (by omega) horder hd h anchor hbase
        hanchors.2 hanchors.1

/-- Exchange an off-cycle owner through the missing leaf of a one-retained
cycle.  If that owner is primitive relative to the fixed retained endpoint,
the exchanged state contains the full cycle.  Consequently the established
full-deleted-cycle theorem returns C2 or a pure-edge witness whose second
omitted coordinate is genuinely outside the original cycle. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_offCycleOwner_to_freshPureEdgeWitness_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (pres : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B pres)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ t * q)) (p : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 18 < 2 ^ t) (horder : addOrderOf y = 2 ^ d - 1)
    (anchor : Fin n) (hbase : a = h + g anchor)
    (missing fixed : Fin n) (hmissing : leaf p = missing)
    (hmissingB : missing ∉ B) (hfixedB : fixed ∉ B)
    (hmissingFixed : missing ≠ fixed)
    (hcomplement : Finset.univ \ B = {missing, fixed})
    (b : ↥B) (hbOutside : (b : Fin n) ∉ Set.range leaf)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g (b : Fin n) - g fixed)) = 2 ^ t) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ x z : Fin n,
        Witness g h (pureEdgeCoeffs x z anchor) ∧
          z ∉ Set.range leaf := by
  classical
  rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd hpres.1 hpres.2.1
        b.property hmissingB hfixedB hmissingFixed hcomplement hprimitive
          hminimal with
    hthree | hstate
  · exact Or.inl hthree
  · have hleafExchange :
        ∀ i, leaf i ∈ insert missing (B.erase (b : Fin n)) := by
      intro i
      by_cases hip : i = p
      · subst i
        rw [hmissing]
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_, (hleafB i).2 hip⟩
        intro hleafEq
        apply hbOutside
        exact ⟨i, hleafEq⟩
    obtain ⟨pres₀, hpres₀, _hconstant⟩ :=
      hstate.fullDeletedCycle_exactPresentation
        g y (insert missing (B.erase (b : Fin n))) hpow (by omega)
          leaf R a hleafExchange hdouble
    rcases hpres₀.exchange_all_fullDeleted_cycleLeaves_to_pureEdgeWitness_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd
          (insert missing (B.erase (b : Fin n))) pres₀ hminimal hd leaf
            hleafInj R hcycle hRne a hleafExchange hdouble hspan (by omega)
              horder anchor hbase with
      hthree | hwitnessX | hwitnessZ
    · exact Or.inl hthree
    · right
      refine ⟨pres₀.z, pres₀.x, hwitnessX, ?_⟩
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      apply pres₀.x_not_mem
      rw [← hi]
      exact hleafExchange i
    · right
      refine ⟨pres₀.x, pres₀.z, hwitnessZ, ?_⟩
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      apply pres₀.z_not_mem
      rw [← hi]
      exact hleafExchange i

/-- Every positive-stratum exact-two state reaches C2 or the uniform
full-order two-retained state.  The first-stratum trivial-difference case is
handled by the primitive owner furnished by minimality. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.positiveStratum_exchange_to_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hnormal := p.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
    ht g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with hfirst | hhalf | hfull
  · rcases hfirst with ⟨rfl, _htrivial, b, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · rcases hhalf.2 with ⟨b, _hbweight, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · right
    refine ⟨B, hmin, hrows.1, hrows, p, ?_⟩
    exact hfull

/-- Lossless fifth-stratum connection of the pure-pair quotient rejoin to
uniform exchange minimization.  Exchanging the primitive half-order owner
inserts the actual missing cycle leaf, so the equality arm retains a fully
deleted cycle.  The already-full arm retains its original one-missing-leaf
orientation and presentation. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_exchangeRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ ∧
          ((∀ i, leaf i ∈ B₀) ∨
            (B₀ = B ∧
              ∃ pres : TwoRetainedFiveWeightPresentation g y B,
                ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = -2) ∨
                  (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = 0)) ∧
                addOrderOf
                  ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                    (g pres.x - g pres.z)) = 32)) := by
  classical
  obtain ⟨pres, hpure, hnormal⟩ :=
    hrows.oneRetainedCycle_criticalFifthStratum_quotientRejoin
      hq g hg hcritical hunique hne y hyq hfullOdd hrTwo B hminimal leaf
        hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB hdouble hspan
  rcases hnormal with hhalf | hfull
  · rcases hhalf with
      ⟨_hindex, b, hbweight, hbprimitive, hbOutside⟩
    rcases hpure with hpureX | hpureZ
    · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.x_not_mem pres.z_not_mem
            pres.x_ne_z pres.complement_eq hbprimitive hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.x (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureX.1
          hbOutside
    · have hbprimitiveX :=
        pres.primitive_otherRetained_of_weight_eq_neg_one
          (t := 5) (q := q) g y B b hbweight hbprimitive
      have hcomplementReverse : Finset.univ \ B = {pres.z, pres.x} := by
        simpa only [pair_comm] using pres.complement_eq
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.z_not_mem pres.x_not_mem
            pres.x_ne_z.symm hcomplementReverse hbprimitiveX hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.z (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureZ.1
          hbOutside
  · right
    have hstate : PrimitiveTwoRetainedPositiveStratumRows g y B := by
      refine ⟨hmin, hrows.1, hrows, pres, ?_⟩
      simpa using hfull
    exact ⟨B, hstate, Or.inr ⟨rfl, pres, hpure, hfull.1⟩⟩

/-- Presentation-aligned fifth-stratum terminal.  Both the exchanged
fully-deleted cycle and the unexchanged one-retained pure cycle now expose
the very presentation that carries the full-order exact two-lift rows. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_alignedExchangeRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        ∃ pres : TwoRetainedFiveWeightPresentation g y B₀,
          PrimitiveTwoRetainedPositiveStratumPresentation g y B₀ pres ∧
            ((∃ hleafB₀ : ∀ i, leaf i ∈ B₀,
                ∀ i j,
                  pres.weight ⟨leaf i, hleafB₀ i⟩ =
                    pres.weight ⟨leaf j, hleafB₀ j⟩) ∨
              (B₀ = B ∧
                ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B₀),
                    pres.weight ⟨leaf i, hi⟩ = -2) ∨
                  (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B₀),
                    pres.weight ⟨leaf i, hi⟩ = 0)))) := by
  classical
  rcases hrows.oneRetainedCycle_criticalFifthStratum_exchangeRejoin
      hq g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B hmin
        hminimal leaf hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB
          hdouble hspan with
    hthree | ⟨B₀, hstate, hgeometry⟩
  · exact Or.inl hthree
  · right
    rcases hgeometry with hall | ⟨hB₀, pres, hpure, horder⟩
    · obtain ⟨pres, hpres, hconstant⟩ :=
        hstate.fullDeletedCycle_exactPresentation
          g y B₀ (by norm_num) (by omega) leaf R a hall hdouble
      exact ⟨B₀, pres, hpres, Or.inl ⟨hall, hconstant⟩⟩
    · subst B₀
      have hnormal := pres.fifthStratum_quotientRowNormalForm
        g hg hunique hne y hyq hfullOdd B hrows hminimal
      rcases hnormal with hhalf | hfull
      · have hfalse : (16 : ℕ) = 32 := hhalf.1.symm.trans horder
        norm_num at hfalse
      · refine ⟨B, pres, ?_, Or.inr ⟨rfl, hpure⟩⟩
        exact ⟨hmin, hrows.1, hrows, by simpa using hfull⟩

/-- Rejoin the critical fifth-stratum cycle at the first presentation-level
caller that still carries the original affine base.  Exact Mersenne order is
derived from the full doubling span.  The fully deleted branch is consumed by
HAF, so the only non-C2, non-fresh-half-witness output is the already-full
one-retained pure presentation on the original transversal. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_alignedExchangeRejoin_to_pureEdgeWitness
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (anchor : Fin n) (hbase : a = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (∃ x z : Fin n,
          Witness g h (pureEdgeCoeffs x z anchor) ∧
            z ∉ Set.range leaf) ∨
      ∃ pres : TwoRetainedFiveWeightPresentation g y B,
        PrimitiveTwoRetainedPositiveStratumPresentation g y B pres ∧
          ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
              pres.weight ⟨leaf i, hi⟩ = -2) ∨
            (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
              pres.weight ⟨leaf i, hi⟩ = 0)) := by
  have horder : addOrderOf y = 2 ^ d - 1 := by
    have hqMersenne := oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
      g hg y hyq hfullOdd leaf hleafInj R hcycle hRne a (by
        intro i
        simpa only [two_nsmul, two_zsmul] using hdouble i) hspan
    calc
      addOrderOf y = q := Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
      _ = 2 ^ d - 1 := hqMersenne
  rcases hrows.oneRetainedCycle_criticalFifthStratum_alignedExchangeRejoin
      hq g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B hmin
        hminimal leaf hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB
          hdouble hspan with
    hthree | ⟨B₀, pres, hpres, hgeometry⟩
  · exact Or.inl hthree
  · rcases hgeometry with ⟨hleafB₀, _hconstant⟩ | ⟨hB₀, hpure⟩
    · rcases hpres.exchange_all_fullDeleted_cycleLeaves_to_pureEdgeWitness_or_three
        (by omega) g hg hh hne hunique hno y hyq hfullOdd B₀ pres hminimal
          hd leaf hleafInj R hcycle hRne a hleafB₀ hdouble hspan
            (by norm_num) horder anchor hbase with
      hthree | hwitnessX | hwitnessZ
      · exact Or.inl hthree
      · right
        left
        refine ⟨pres.z, pres.x, hwitnessX, ?_⟩
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        apply pres.x_not_mem
        rw [← hi]
        exact hleafB₀ i
      · right
        left
        refine ⟨pres.x, pres.z, hwitnessZ, ?_⟩
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        apply pres.z_not_mem
        rw [← hi]
        exact hleafB₀ i
    · subst B₀
      exact Or.inr (Or.inr ⟨pres, hpres, hpure⟩)

/-- The honest terminal after exploiting every off-cycle owner of the
one-retained presentation.  A primitive orientation toward the fixed endpoint
is exchanged back to a full-deleted cycle and hence produces C2 or a genuinely
fresh half-witness.  Therefore the only remaining presentation-level branch
has every off-cycle owner primitive toward the missing cycle leaf. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_offCycleOwnerReduction
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (anchor : Fin n) (hbase : a = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (∃ x z : Fin n,
          Witness g h (pureEdgeCoeffs x z anchor) ∧
            z ∉ Set.range leaf) ∨
      ∃ pres : TwoRetainedFiveWeightPresentation g y B,
        n = d + 5 ∧
        (B \ (Finset.univ.image leaf)).card = 4 ∧
        PrimitiveTwoRetainedPositiveStratumPresentation g y B pres ∧
          ((leaf p = pres.x ∧
              (∀ i (hi : leaf i ∈ B),
                pres.weight ⟨leaf i, hi⟩ = -2) ∧
              ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
                addOrderOf
                    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                      (g (b : Fin n) - g pres.x)) = 32 ∧
                  (let pi :=
                      QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
                   let deltaQ := pi (g pres.x - g pres.z)
                   let betaQ := pi (g (b : Fin n) - g pres.z)
                   (pres.weight b = -4 ∧
                        (betaQ = (2 : ℕ) • deltaQ ∨
                          betaQ = (18 : ℕ) • deltaQ)) ∨
                     (pres.weight b = 0 ∧
                        (betaQ = 0 ∨
                          betaQ = (16 : ℕ) • deltaQ)))) ∨
            (leaf p = pres.z ∧
              (∀ i (hi : leaf i ∈ B),
                pres.weight ⟨leaf i, hi⟩ = 0) ∧
              ∀ b : ↥B, (b : Fin n) ∉ Set.range leaf →
                addOrderOf
                    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                      (g (b : Fin n) - g pres.z)) = 32 ∧
                  (let pi :=
                      QuotientAddGroup.mk' (AddSubgroup.zmultiples y)
                   let deltaQ := pi (g pres.x - g pres.z)
                   let betaQ := pi (g (b : Fin n) - g pres.z)
                   (pres.weight b = -2 ∧
                        (betaQ = deltaQ ∨
                          betaQ = (17 : ℕ) • deltaQ)) ∨
                     (pres.weight b = 2 ∧
                        (betaQ = -deltaQ ∨
                          betaQ = (15 : ℕ) • deltaQ))))) := by
  have hqMersenne := oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
    g hg y hyq hfullOdd leaf hleafInj R hcycle hRne a (by
      intro i
      simpa only [two_nsmul, two_zsmul] using hdouble i) hspan
  have horder : addOrderOf y = 2 ^ d - 1 := by
    calc
      addOrderOf y = q := Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
      _ = 2 ^ d - 1 := hqMersenne
  have hn : n = d + 5 :=
    criticalFifthStratum_mersenne_threeOrFour_dimension_eq_add_five
      g hg hcritical hd hqMersenne
  have hoffCycleCard :
      (B \ (Finset.univ.image leaf)).card = 4 :=
    card_offCycleOwners_eq_four_of_oneRetained_dimension
      leaf hleafInj B p hleafB hn hrows.1
  rcases hrows.oneRetainedCycle_criticalFifthStratum_alignedExchangeRejoin_to_pureEdgeWitness
      hq g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B hmin
        hminimal hd leaf hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB
          hdouble hspan anchor hbase with
    hthree | hfresh | ⟨pres, hpres, hpure⟩
  · exact Or.inl hthree
  · exact Or.inr (Or.inl hfresh)
  · rcases hpure with hpureX | hpureZ
    · by_cases hgood : ∃ b : ↥B,
          (b : Fin n) ∉ Set.range leaf ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g pres.z)) = 32
      · obtain ⟨b, hbOutside, hbprimitive⟩ := hgood
        rcases hpres.exchange_offCycleOwner_to_freshPureEdgeWitness_or_three
            (by omega) g hg hh hne hunique hno y hyq hfullOdd B pres
              hminimal hd leaf hleafInj R hcycle hRne a p hleafB hdouble
                hspan (by norm_num) horder anchor hbase pres.x pres.z
                  hpureX.1 pres.x_not_mem pres.z_not_mem pres.x_ne_z
                    pres.complement_eq b hbOutside hbprimitive with
          hthree | hfresh
        · exact Or.inl hthree
        · exact Or.inr (Or.inl hfresh)
      · right
        right
        refine ⟨pres, hn, hoffCycleCard, hpres,
          Or.inl ⟨hpureX.1, hpureX.2, ?_⟩⟩
        intro b hbOutside
        rcases hpres.owner_primitive_at_one_retained g y B pres b with
          hbFixed | hbMissing
        · exact False.elim (hgood ⟨b, hbOutside, by simpa using hbFixed⟩)
        · have hbMissing' :
              addOrderOf
                ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (b : Fin n) - g pres.x)) = 32 := by
            simpa using hbMissing
          refine ⟨hbMissing', ?_⟩
          exact hpres.fifthStratum_xPrimitive_ownerPosition
            g y B pres b hbMissing'
    · by_cases hgood : ∃ b : ↥B,
          (b : Fin n) ∉ Set.range leaf ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g pres.x)) = 32
      · obtain ⟨b, hbOutside, hbprimitive⟩ := hgood
        have hcomplementReverse : Finset.univ \ B = {pres.z, pres.x} := by
          simpa only [pair_comm] using pres.complement_eq
        rcases hpres.exchange_offCycleOwner_to_freshPureEdgeWitness_or_three
            (by omega) g hg hh hne hunique hno y hyq hfullOdd B pres
              hminimal hd leaf hleafInj R hcycle hRne a p hleafB hdouble
                hspan (by norm_num) horder anchor hbase pres.z pres.x
                  hpureZ.1 pres.z_not_mem pres.x_not_mem pres.x_ne_z.symm
                    hcomplementReverse b hbOutside hbprimitive with
          hthree | hfresh
        · exact Or.inl hthree
        · exact Or.inr (Or.inl hfresh)
      · right
        right
        refine ⟨pres, hn, hoffCycleCard, hpres,
          Or.inr ⟨hpureZ.1, hpureZ.2, ?_⟩⟩
        intro b hbOutside
        rcases hpres.owner_primitive_at_one_retained g y B pres b with
          hbMissing | hbFixed
        · have hbMissing' :
              addOrderOf
                ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (b : Fin n) - g pres.z)) = 32 := by
            simpa using hbMissing
          refine ⟨hbMissing', ?_⟩
          exact hpres.fifthStratum_zPrimitive_ownerPosition
            g y B pres b hbMissing'
        · exact False.elim (hgood ⟨b, hbOutside, by simpa using hbFixed⟩)

/-- Every nonzero element of a cyclic group of order seven or fifteen is the
difference of two equal-cardinality subsets of the displayed doubling powers.
This is the balanced form of the small Mersenne orbit cover. -/
theorem exists_balancedPowerDifference_of_order_seven_or_fifteen
    {G : Type*} [AddCommGroup G] (v C : G) {d : ℕ}
    (hd : d = 3 ∨ d = 4) (hv : addOrderOf v = 2 ^ d - 1)
    (hCmem : C ∈ AddSubgroup.zmultiples v) (hC0 : C ≠ 0) :
    ∃ A D : Finset (Fin d), A.card = D.card ∧
      C = (∑ i ∈ A, (2 ^ i.val) • v) -
        ∑ i ∈ D, (2 ^ i.val) • v := by
  rcases hd with rfl | rfl
  · have hv' : addOrderOf v = 7 := by norm_num at hv ⊢; exact hv
    obtain ⟨s, hs0, hslt, rfl⟩ :=
      exists_positive_nsmul_eq_of_mem_zmultiples
        (v := v) (t := C) (q := 7) (by norm_num) hv' hCmem hC0
    have hvzero : (7 : ℕ) • v = 0 := by
      simpa only [hv'] using addOrderOf_nsmul_eq_zero v
    have hneg (r k : ℕ) (hrk : r + k = 7) : r • v = -(k • v) := by
      calc
        r • v = (r + k) • v - k • v := by rw [add_nsmul]; abel
        _ = -(k • v) := by rw [hrk, hvzero]; simp
    interval_cases s
    · refine ⟨({1} : Finset (Fin 3)), {0}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({2} : Finset (Fin 3)), {1}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({2} : Finset (Fin 3)), {0}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({0} : Finset (Fin 3)), {2}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 4 3 (by norm_num)
      calc
        4 • v = -(3 • v) := hwrap
        _ = v - 4 • v := by module
    · refine ⟨({1} : Finset (Fin 3)), {2}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 5 2 (by norm_num)
      calc
        5 • v = -(2 • v) := hwrap
        _ = 2 • v - 4 • v := by module
    · refine ⟨({0} : Finset (Fin 3)), {1}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 6 1 (by norm_num)
      calc
        6 • v = -(1 • v) := hwrap
        _ = v - 2 • v := by module
  · have hv' : addOrderOf v = 15 := by norm_num at hv ⊢; exact hv
    obtain ⟨s, hs0, hslt, rfl⟩ :=
      exists_positive_nsmul_eq_of_mem_zmultiples
        (v := v) (t := C) (q := 15) (by norm_num) hv' hCmem hC0
    have hvzero : (15 : ℕ) • v = 0 := by
      simpa only [hv'] using addOrderOf_nsmul_eq_zero v
    have hneg (r k : ℕ) (hrk : r + k = 15) : r • v = -(k • v) := by
      calc
        r • v = (r + k) • v - k • v := by rw [add_nsmul]; abel
        _ = -(k • v) := by rw [hrk, hvzero]; simp
    interval_cases s
    · refine ⟨({1} : Finset (Fin 4)), {0}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({2} : Finset (Fin 4)), {1}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({2} : Finset (Fin 4)), {0}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({3} : Finset (Fin 4)), {2}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({1, 3} : Finset (Fin 4)), {0, 2}, by decide, ?_⟩
      have hsumA :
          (∑ i ∈ ({1, 3} : Finset (Fin 4)), (2 ^ i.val) • v) =
            2 • v + 8 • v := by
        rw [Finset.sum_insert
          (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
          Finset.sum_singleton]
        norm_num
      have hsumD :
          (∑ i ∈ ({0, 2} : Finset (Fin 4)), (2 ^ i.val) • v) =
            1 • v + 4 • v := by
        rw [Finset.sum_insert
          (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
          Finset.sum_singleton]
        norm_num
      rw [hsumA, hsumD]
      module
    · refine ⟨({3} : Finset (Fin 4)), {1}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({3} : Finset (Fin 4)), {0}, by decide, ?_⟩
      norm_num
      module
    · refine ⟨({0} : Finset (Fin 4)), {3}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 8 7 (by norm_num)
      calc
        8 • v = -(7 • v) := hwrap
        _ = v - 8 • v := by module
    · refine ⟨({1} : Finset (Fin 4)), {3}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 9 6 (by norm_num)
      calc
        9 • v = -(6 • v) := hwrap
        _ = 2 • v - 8 • v := by module
    · refine ⟨({0, 2} : Finset (Fin 4)), {1, 3}, by decide, ?_⟩
      have hsumA :
          (∑ i ∈ ({0, 2} : Finset (Fin 4)), (2 ^ i.val) • v) =
            1 • v + 4 • v := by
        rw [Finset.sum_insert
          (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
          Finset.sum_singleton]
        norm_num
      have hsumD :
          (∑ i ∈ ({1, 3} : Finset (Fin 4)), (2 ^ i.val) • v) =
            2 • v + 8 • v := by
        rw [Finset.sum_insert
          (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
          Finset.sum_singleton]
        norm_num
      rw [hsumA, hsumD]
      have hwrap := hneg 10 5 (by norm_num)
      calc
        10 • v = -(5 • v) := hwrap
        _ = (1 • v + 4 • v) - (2 • v + 8 • v) := by module
    · refine ⟨({2} : Finset (Fin 4)), {3}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 11 4 (by norm_num)
      calc
        11 • v = -(4 • v) := hwrap
        _ = 4 • v - 8 • v := by module
    · refine ⟨({0} : Finset (Fin 4)), {2}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 12 3 (by norm_num)
      calc
        12 • v = -(3 • v) := hwrap
        _ = v - 4 • v := by module
    · refine ⟨({1} : Finset (Fin 4)), {2}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 13 2 (by norm_num)
      calc
        13 • v = -(2 • v) := hwrap
        _ = 2 • v - 4 • v := by module
    · refine ⟨({0} : Finset (Fin 4)), {1}, by decide, ?_⟩
      norm_num
      have hwrap := hneg 14 1 (by norm_num)
      calc
        14 • v = -(1 • v) := hwrap
        _ = v - 2 • v := by module

/-- Outside a three- or four-leaf full Mersenne doubling cycle, quotienting by
the odd cycle kernel is injective on tuple coordinates.  A quotient collision
would be a balanced difference of cycle leaves and hence a forbidden
equal-cardinality subset-sum collision. -/
theorem validTuple_offCycle_quotient_injective_of_mersenne_threeOrFour
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ t * q)) {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (a : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (horder : addOrderOf y = 2 ^ d - 1)
    {b c : Fin n} (hbOutside : b ∉ Set.range leaf)
    (hcOutside : c ∉ Set.range leaf)
    (hdiff : g b - g c ∈ AddSubgroup.zmultiples y) :
    b = c := by
  classical
  by_contra hbc
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  let disp : Fin d → ZMod (2 ^ t * q) := fun r ↦ g (leaf r) - a
  have hdoubleN : ∀ i, disp (R i) = (2 : ℕ) • disp i := by
    intro i
    simpa only [disp, two_nsmul, two_zsmul] using hdouble i
  let root : Fin d := ⟨0, hdpos⟩
  let e : Fin d ≃ Fin d := fullCycleOrbitEquiv R hcycle hRne root
  let orbitLeaf : Fin d → Fin n := fun i ↦ leaf (e i)
  have horbitInj : Function.Injective orbitLeaf :=
    hleafInj.comp e.injective
  let v : ZMod (2 ^ t * q) := disp root
  let C : ZMod (2 ^ t * q) := g b - g c
  have hdispE : ∀ r : Fin d, disp (e r) = (2 ^ r.val) • v := by
    intro r
    exact fullCycleOrbitEquiv_doubling_eq_pow_two
      R hcycle hRne root disp hdoubleN r
  have hgroups : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y := by
    exact zmultiples_eq_of_isCycle_doubling_span
      R hcycle hRne disp hdoubleN y hspan root
  have hv : addOrderOf v = 2 ^ d - 1 := by
    calc
      addOrderOf v = addOrderOf y :=
        addOrderOf_eq_of_isCycle_doubling_span
          R hcycle hRne disp hdoubleN y hspan root
      _ = 2 ^ d - 1 := horder
  have hCmem : C ∈ AddSubgroup.zmultiples v := by
    rw [hgroups]
    exact hdiff
  have hC0 : C ≠ 0 := by
    intro hzero
    apply hbc
    apply validTuple_injective g hg
    exact sub_eq_zero.mp hzero
  obtain ⟨A, D, hcardAD, hC⟩ :=
    exists_balancedPowerDifference_of_order_seven_or_fifteen
      v C hd hv hCmem hC0
  have hsumA :
      (∑ i ∈ A, (2 ^ i.val) • v) =
        (∑ i ∈ A, g (orbitLeaf i)) - A.card • a := by
    calc
      (∑ i ∈ A, (2 ^ i.val) • v) =
          ∑ i ∈ A, disp (e i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact (hdispE i).symm
      _ = ∑ i ∈ A, (g (orbitLeaf i) - a) := rfl
      _ = (∑ i ∈ A, g (orbitLeaf i)) - A.card • a := by
        rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hsumD :
      (∑ i ∈ D, (2 ^ i.val) • v) =
        (∑ i ∈ D, g (orbitLeaf i)) - D.card • a := by
    calc
      (∑ i ∈ D, (2 ^ i.val) • v) =
          ∑ i ∈ D, disp (e i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact (hdispE i).symm
      _ = ∑ i ∈ D, (g (orbitLeaf i) - a) := rfl
      _ = (∑ i ∈ D, g (orbitLeaf i)) - D.card • a := by
        rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hbalanced :
      g b - g c =
        (∑ i ∈ A, g (orbitLeaf i)) - ∑ i ∈ D, g (orbitLeaf i) := by
    change C = _
    rw [hC, hsumA, hsumD, hcardAD]
    abel
  have hsumBase :
      g b + ∑ i ∈ D, g (orbitLeaf i) =
        g c + ∑ i ∈ A, g (orbitLeaf i) := by
    calc
      g b + ∑ i ∈ D, g (orbitLeaf i) =
          (g b - g c) + g c + ∑ i ∈ D, g (orbitLeaf i) := by abel
      _ = ((∑ i ∈ A, g (orbitLeaf i)) -
          ∑ i ∈ D, g (orbitLeaf i)) + g c +
            ∑ i ∈ D, g (orbitLeaf i) := by rw [hbalanced]
      _ = g c + ∑ i ∈ A, g (orbitLeaf i) := by abel
  have hbNotD : b ∉ D.image orbitLeaf := by
    intro hb
    obtain ⟨i, _hiD, hi⟩ := Finset.mem_image.mp hb
    exact hbOutside ⟨e i, hi⟩
  have hcNotA : c ∉ A.image orbitLeaf := by
    intro hc
    obtain ⟨i, _hiA, hi⟩ := Finset.mem_image.mp hc
    exact hcOutside ⟨e i, hi⟩
  let S : Finset (Fin n) := insert b (D.image orbitLeaf)
  let T : Finset (Fin n) := insert c (A.image orbitLeaf)
  have hcardST : S.card = T.card := by
    rw [show S.card = D.card + 1 by
      simp only [S, Finset.card_insert_of_notMem hbNotD,
        Finset.card_image_of_injective _ horbitInj],
      show T.card = A.card + 1 by
        simp only [T, Finset.card_insert_of_notMem hcNotA,
          Finset.card_image_of_injective _ horbitInj], hcardAD]
  have hsumS : (∑ i ∈ S, g i) =
      g b + ∑ i ∈ D, g (orbitLeaf i) := by
    rw [show S = insert b (D.image orbitLeaf) by rfl,
      Finset.sum_insert hbNotD, Finset.sum_image]
    exact horbitInj.injOn
  have hsumT : (∑ i ∈ T, g i) =
      g c + ∑ i ∈ A, g (orbitLeaf i) := by
    rw [show T = insert c (A.image orbitLeaf) by rfl,
      Finset.sum_insert hcNotA, Finset.sum_image]
    exact horbitInj.injOn
  have hsumST : (∑ i ∈ S, g i) = ∑ i ∈ T, g i :=
    hsumS.trans (hsumBase.trans hsumT.symm)
  let idEmb : Fin n ↪ Fin n := ⟨id, Function.injective_id⟩
  have hST : S = T := validTuple_subsetSum_eq_of_card_eq
    g hg idEmb hcardST (by
      change (∑ i ∈ S, g i) = ∑ i ∈ T, g i
      exact hsumST)
  have hbNotA : b ∉ A.image orbitLeaf := by
    intro hb
    obtain ⟨i, _hiA, hi⟩ := Finset.mem_image.mp hb
    exact hbOutside ⟨e i, hi⟩
  have hbT : b ∉ T := by
    intro hbmem
    rcases Finset.mem_insert.mp hbmem with hbc' | hbA
    · exact hbc hbc'
    · exact hbNotA hbA
  apply hbT
  rw [← hST]
  exact Finset.mem_insert_self b (D.image orbitLeaf)

/-- Close the critical fifth-stratum one-retained terminal.  Canonical unit
rows force two of the four off-cycle owners to collide in the quotient, while
the balanced Mersenne orbit cover proves that the quotient map is injective on
all off-cycle tuple coordinates.  Hence only C2 or a genuinely fresh
half-witness remains. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_offCycleOwnerClosure
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : d = 3 ∨ d = 4)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (anchor : Fin n) (hbase : a = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ x z : Fin n,
        Witness g h (pureEdgeCoeffs x z anchor) ∧
          z ∉ Set.range leaf := by
  have hqMersenne := oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
    g hg y hyq hfullOdd leaf hleafInj R hcycle hRne a (by
      intro i
      simpa only [two_nsmul, two_zsmul] using hdouble i) hspan
  have horder : addOrderOf y = 2 ^ d - 1 := by
    calc
      addOrderOf y = q := Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
      _ = 2 ^ d - 1 := hqMersenne
  rcases hrows.oneRetainedCycle_criticalFifthStratum_offCycleOwnerReduction
      hq g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B hmin
        hminimal hd leaf hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB
          hdouble hspan anchor hbase with
    hthree | hfresh | ⟨pres, _hn, hoffCycleCard, hpres, hgeometry⟩
  · exact Or.inl hthree
  · exact Or.inr hfresh
  · rcases hgeometry with hpureX | hpureZ
    · have hcollision :=
        hpres.fifthStratum_xPrimitive_offCycle_collision_of_canonicalRows
          g y B pres hyq hfullOdd leaf hoffCycleCard
            (fun b hbOutside ↦ (hpureX.2.2 b hbOutside).1)
      obtain ⟨b, hbS, c, hcS, hbc, hquotient⟩ := hcollision
      have hbOutside : b ∉ Set.range leaf := by
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        exact (Finset.mem_sdiff.mp hbS).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hcOutside : c ∉ Set.range leaf := by
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        exact (Finset.mem_sdiff.mp hcS).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hdiff : g b - g c ∈ AddSubgroup.zmultiples y := by
        apply (QuotientAddGroup.eq_zero_iff (g b - g c)).mp
        have hdecomp : g b - g c =
            (g b - g pres.z) - (g c - g pres.z) := by abel
        rw [hdecomp]
        change (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          ((g b - g pres.z) - (g c - g pres.z)) = 0
        rw [map_sub, hquotient, sub_self]
      have heq :=
        validTuple_offCycle_quotient_injective_of_mersenne_threeOrFour
          g hg y hd leaf hleafInj R hcycle hRne a hdouble hspan horder
            hbOutside hcOutside hdiff
      exact (hbc heq).elim
    · have hcollision :=
        hpres.fifthStratum_zPrimitive_offCycle_collision_of_canonicalRows
          g y B pres hyq hfullOdd leaf hoffCycleCard
            (fun b hbOutside ↦ (hpureZ.2.2 b hbOutside).1)
      obtain ⟨b, hbS, c, hcS, hbc, hquotient⟩ := hcollision
      have hbOutside : b ∉ Set.range leaf := by
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        exact (Finset.mem_sdiff.mp hbS).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hcOutside : c ∉ Set.range leaf := by
        intro hrange
        obtain ⟨i, hi⟩ := hrange
        exact (Finset.mem_sdiff.mp hcS).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hdiff : g b - g c ∈ AddSubgroup.zmultiples y := by
        apply (QuotientAddGroup.eq_zero_iff (g b - g c)).mp
        have hdecomp : g b - g c =
            (g b - g pres.z) - (g c - g pres.z) := by abel
        rw [hdecomp]
        change (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          ((g b - g pres.z) - (g c - g pres.z)) = 0
        rw [map_sub, hquotient, sub_self]
      have heq :=
        validTuple_offCycle_quotient_injective_of_mersenne_threeOrFour
          g hg y hd leaf hleafInj R hcycle hRne a hdouble hspan horder
            hbOutside hcOutside hdiff
      exact (hbc heq).elim

end MinModulus
