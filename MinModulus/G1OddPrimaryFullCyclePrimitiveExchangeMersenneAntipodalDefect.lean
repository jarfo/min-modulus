/-
# The localized floor defect at the antipodal Mersenne endpoint

Adding the antipodal pure external row to a leaf-supported witness at the
opposite target gives an integer zero relation.  Both displayed pure-edge
endpoints are outside the leaf except for the unique retained leaf.  Hence
the sum has coefficient exactly `-2` there and coefficient floor at least
`-1` everywhere else.  This isolates the only obstruction to applying
validity to the sum.

The endpoint theorem retains that localized zero relation together with the
same-target leaf competitor and the exact signed-binary alternative from the
pointed Mersenne orbit.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalArithmetic

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- A nonzero integer zero relation whose only failure of the witness floor
is one coefficient equal to `-2`. -/
structure SingleFloorDefectZeroRelation
    {n : ℕ} (g : Fin n → G) (r : Fin n) (q : Fin n → ℤ) : Prop where
  nonzero : q ≠ 0
  coeff_sum : (∑ i, q i) = 0
  weighted_sum : (∑ i, q i • g i) = 0
  defect : q r = -2
  floor_away : ∀ i, i ≠ r → -1 ≤ q i

/-- The distinguished coordinate is exactly the set where the witness floor
fails. -/
theorem SingleFloorDefectZeroRelation.lt_neg_one_iff
    {n : ℕ} {g : Fin n → G} {r i : Fin n} {q : Fin n → ℤ}
    (hrel : SingleFloorDefectZeroRelation g r q) :
    q i < -1 ↔ i = r := by
  constructor
  · intro hi
    by_contra hir
    have hfloor := hrel.floor_away i hir
    omega
  · intro hir
    subst i
    rw [hrel.defect]
    omega

/-- A pure edge and a leaf-supported witness at its opposite target add to a
zero relation with one exact floor defect.  The pure center and external
endpoint remain visible with coefficients `2` and `-1`. -/
theorem pureEdge_add_leafSupported_oppositeWitness_singleFloorDefect
    {n d : ℕ} (g : Fin n → G) (leaf : Fin d → Fin n)
    (t : G) (u c : Fin n → ℤ)
    (hu : Witness g t u) (hc : Witness g (-t) c)
    (hcoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0)
    (x b r : Fin n) (hxb : x ≠ b) (hxr : x ≠ r) (hbr : b ≠ r)
    (hshape : u = pureEdgeCoeffs x b r)
    (hxoff : x ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hboff : b ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hcr : c r = -1) :
    let q := u + c
    SingleFloorDefectZeroRelation g r q ∧ q x = 2 ∧ q b = -1 := by
  dsimp only
  let q : Fin n → ℤ := u + c
  have hcx : c x = 0 := hcoff x hxoff
  have hcb : c b = 0 := hcoff b hboff
  have hqr : q r = -2 := by
    simp [q, hshape, pureEdgeCoeffs, Ne.symm hxr, Ne.symm hbr, hcr]
  have hqx : q x = 2 := by
    simp [q, hshape, pureEdgeCoeffs, hxb, hxr, hcx]
  have hqb : q b = -1 := by
    simp [q, hshape, pureEdgeCoeffs, Ne.symm hxb, hbr, hcb]
  refine ⟨?_, hqx, hqb⟩
  refine ⟨?_, ?_, ?_, hqr, ?_⟩
  · intro hzero
    have hr := congrFun hzero r
    have hqr' : (u + c) r = -2 := by simpa only [q] using hqr
    rw [hqr'] at hr
    simp at hr
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hu.2.2.1, hc.2.2.1, add_zero]
  · calc
      (∑ i, q i • g i) =
          ∑ i, (u i • g i + c i • g i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [q, Pi.add_apply, add_smul]
      _ = (∑ i, u i • g i) + (∑ i, c i • g i) :=
        Finset.sum_add_distrib
      _ = t + -t := by rw [hu.2.2.2, hc.2.2.2]
      _ = 0 := add_neg_cancel t
  · intro i hir
    by_cases hix : i = x
    · subst i
      change -1 ≤ q x
      rw [hqx]
      omega
    by_cases hib : i = b
    · subst i
      change -1 ≤ q b
      rw [hqb]
    have hui : u i = 0 := by
      rw [hshape]
      simp [pureEdgeCoeffs, hix, hib, hir]
    have hci := hc.2.1 i
    change -1 ≤ q i
    simpa only [q, Pi.add_apply, hui, zero_add] using hci

/-- Complete antipodal endpoint with the localized zero relation exposed.
The unique retained leaf is the only coordinate below the witness floor. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_singleFloorDefect
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (k₀ k : ℤ)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ c q : Fin n → ℤ,
        Witness g (-(p.scalar b • y)) c ∧
        (∀ j,
          j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        c r = -1 ∧ q = p.coeff b + c ∧
        SingleFloorDefectZeroRelation g r q ∧
        q center = 2 ∧ q (b : Fin n) = -1 := by
  dsimp only
  let center : Fin n := if k₀ = -1 then p.z else p.x
  obtain ⟨hownerNeg, hshape, _s, _hs0, _hsq, _htarget,
      c, hc, hcoff, hcr⟩ :=
    p.exists_antipodal_mersenneLeaf_oppositeWitness
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb
        k₀ k r hr hantipodal howner hweight
  have hcenterB : center ≠ (b : Fin n) := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · simp only [hk₀, if_true]
      exact fun h ↦ p.z_not_mem (h.symm ▸ b.property)
    · have hk₀Ne : k₀ ≠ -1 := by omega
      simp only [hk₀Ne, if_false]
      exact fun h ↦ p.x_not_mem (h.symm ▸ b.property)
  have hcenterR : center ≠ r := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
      simpa only [hk₀, if_true, hrx] using p.x_ne_z.symm
    · have hk₀Ne : k₀ ≠ -1 := by omega
      have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
      simpa only [hk₀Ne, if_false, hrz] using p.x_ne_z
  have hbr : (b : Fin n) ≠ r := by
    intro hbr
    have hrB : r ∈ B := hbr ▸ b.property
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
      exact p.x_not_mem (hrx ▸ hrB)
    · have hk₀Ne : k₀ ≠ -1 := by omega
      have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
      exact p.z_not_mem (hrz ▸ hrB)
  have hcenterNotB : center ∉ B := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · simpa only [hk₀, if_true] using p.z_not_mem
    · have hk₀Ne : k₀ ≠ -1 := by omega
      simpa only [hk₀Ne, if_false] using p.x_not_mem
  have hcenterOff : center ∉
      (Finset.univ : Finset (Fin d)).image leaf := by
    intro hcenterLeaf
    exact hcenterNotB (hdeleted center hcenterLeaf hcenterR)
  obtain ⟨hdefect, hqcenter, hqb⟩ :=
    pureEdge_add_leafSupported_oppositeWitness_singleFloorDefect
      g leaf (p.scalar b • y) (p.coeff b) c (p.isWitness b) hc hcoff
        center (b : Fin n) r hcenterB hcenterR hbr
        (by simpa only [center] using hshape) hcenterOff hb hcr
  exact ⟨hownerNeg, hshape, c, p.coeff b + c,
    hc, hcoff, hcr, rfl, hdefect, hqcenter, hqb⟩

/-- Lossless antipodal package: the same witnesses expose the localized
floor defect and give either a common leaf omission or the two exact binary
integer lifts of the signed subset residual. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_localizedDefect_dichotomy
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (k₀ k : ℤ)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
        p.scalar b • y = s • v ∧
        ∃ cPlus cMinus q : Fin n → ℤ, ∃ i : Fin n,
          Witness g (p.scalar b • y) cPlus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cPlus j = 0) ∧
          Witness g (-(p.scalar b • y)) cMinus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cMinus j = 0) ∧
          cMinus r = -1 ∧
          i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          (i = r ∨ 2 ≤ cPlus i) ∧
          p.coeff b i + 2 ≤ cPlus i ∧
          q = p.coeff b + cMinus ∧
          SingleFloorDefectZeroRelation g r q ∧
          q center = 2 ∧ q (b : Fin n) = -1 ∧
          ((∃ j : Fin n,
              j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
                cPlus j = -1 ∧ cMinus j = -1) ∨
            ∃ A M : Finset (Fin d),
              cMinus = -cPlus ∧ Disjoint A M ∧ A.card = M.card ∧
              ⟨0, by omega⟩ ∈ A ∧
              (binarySubsetValue A = binarySubsetValue M + s ∨
                binarySubsetValue A + (2 ^ d - 1) =
                  binarySubsetValue M + s)) := by
  dsimp only
  let center : Fin n := if k₀ = -1 then p.z else p.x
  obtain ⟨hownerNeg, hshape, sPlus, _sMinus,
      hsPlus0, hsPlusQ, hplusTarget,
      _hsMinus0, _hsMinusQ, _hminusTarget, _hsum,
      cPlus, cMinus, i, hcPlus, hplusOff, hcMinus, hminusOff,
      hminusR, hiLeaf, hiLocalized, hiGap, hpair⟩ :=
    p.exists_antipodal_mersenneLeaf_pair_dichotomy
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic r hdeleted
        b hb k₀ k hr hantipodal howner hweight
  have hcenterB : center ≠ (b : Fin n) := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · simp only [hk₀, if_true]
      exact fun h ↦ p.z_not_mem (h.symm ▸ b.property)
    · have hk₀Ne : k₀ ≠ -1 := by omega
      simp only [hk₀Ne, if_false]
      exact fun h ↦ p.x_not_mem (h.symm ▸ b.property)
  have hcenterR : center ≠ r := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
      simpa only [hk₀, if_true, hrx] using p.x_ne_z.symm
    · have hk₀Ne : k₀ ≠ -1 := by omega
      have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
      simpa only [hk₀Ne, if_false, hrz] using p.x_ne_z
  have hbr : (b : Fin n) ≠ r := by
    intro hbr
    have hrB : r ∈ B := hbr ▸ b.property
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · have hrx : r = p.x := by simpa only [hk₀, if_true] using hr
      exact p.x_not_mem (hrx ▸ hrB)
    · have hk₀Ne : k₀ ≠ -1 := by omega
      have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
      exact p.z_not_mem (hrz ▸ hrB)
  have hcenterNotB : center ∉ B := by
    dsimp only [center]
    rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
    · simpa only [hk₀, if_true] using p.z_not_mem
    · have hk₀Ne : k₀ ≠ -1 := by omega
      simpa only [hk₀Ne, if_false] using p.x_not_mem
  have hcenterOff : center ∉
      (Finset.univ : Finset (Fin d)).image leaf := by
    intro hcenterLeaf
    exact hcenterNotB (hdeleted center hcenterLeaf hcenterR)
  obtain ⟨hdefect, hqcenter, hqb⟩ :=
    pureEdge_add_leafSupported_oppositeWitness_singleFloorDefect
      g leaf (p.scalar b • y) (p.coeff b) cMinus
        (p.isWitness b) hcMinus hminusOff center (b : Fin n) r
        hcenterB hcenterR hbr (by simpa only [center] using hshape)
        hcenterOff hb hminusR
  have houtcome :
      (∃ j : Fin n,
          j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
            cPlus j = -1 ∧ cMinus j = -1) ∨
        ∃ A M : Finset (Fin d),
          cMinus = -cPlus ∧ Disjoint A M ∧ A.card = M.card ∧
          ⟨0, by omega⟩ ∈ A ∧
          (binarySubsetValue A = binarySubsetValue M + sPlus ∨
            binarySubsetValue A + (2 ^ d - 1) =
              binarySubsetValue M + sPlus) := by
    rcases hpair with hcommon | ⟨hneg, _hplusR, hplusTernary, _hminusTernary⟩
    · exact Or.inl hcommon
    · right
      have hsubset : LeafEqualCardSubsetDifference
          g leaf (p.scalar b • y) r :=
        leafSupported_ternaryWitness_subsetDifference
          g leaf cPlus hcPlus hplusOff hplusTernary r (by
            have hrEq := congrFun hneg r
            simp only [Pi.neg_apply, hminusR] at hrEq
            omega)
      have hsubset' : LeafEqualCardSubsetDifference
          g leaf (sPlus • v) r := by
        rw [← hplusTarget]
        exact hsubset
      obtain ⟨A, M, hdisjoint, hcard, hzero, harith⟩ :=
        hsubset'.exists_pointed_binary_arithmetic
          hd g root v hv leaf hleaf e hnormal r hrzero hsPlus0 hsPlusQ
      exact ⟨A, M, hneg, hdisjoint, hcard, hzero, harith⟩
  exact ⟨hownerNeg, hshape, sPlus, hsPlus0, hsPlusQ, hplusTarget,
    cPlus, cMinus, p.coeff b + cMinus, i,
    hcPlus, hplusOff, hcMinus, hminusOff, hminusR,
    hiLeaf, hiLocalized, hiGap, rfl, hdefect, hqcenter, hqb, houtcome⟩

end MinModulus
