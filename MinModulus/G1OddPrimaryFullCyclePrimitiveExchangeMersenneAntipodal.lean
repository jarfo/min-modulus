/-
# Antipodal external rows on a pointed Mersenne leaf

The exact-Mersenne endpoint has one possible external parameter that is not
adjacent to the primary middle parameter.  The preceding leaf-comparison
theorems fix every external owner sign to `-1`; at the opposite extreme the
row is therefore exactly a pure edge with omissions at its owner and the
unique retained leaf.

This module uses the correct target arithmetic for that row.  Its target is a
nonzero element of the odd kernel, not the half-modulus involution.  A general
opposite-target combination lemma compares it with a leaf witness at the
negative target and forces that leaf witness to omit the retained leaf.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLeafRepresentations

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- The omissions of a nondegenerate pure edge are exactly its two displayed
endpoints. -/
theorem pureEdgeCoeffs_eq_neg_one_iff
    {n : ℕ} (x a b i : Fin n)
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    pureEdgeCoeffs x a b i = -1 ↔ i = a ∨ i = b := by
  by_cases hix : i = x
  · subst i
    simp [pureEdgeCoeffs, hxa, hxb]
  by_cases hia : i = a
  · subst i
    simp [pureEdgeCoeffs, hix, hab]
  by_cases hib : i = b
  · subst i
    simp [pureEdgeCoeffs, hix, hab.symm]
  simp [pureEdgeCoeffs, hix, hia, hib]

/-- Witness combination for opposite targets.  If witnesses at `t` and `-t`
share no omission, their sum is an admissible zero relation, so validity makes
the second coefficient vector the negative of the first. -/
theorem witness_opposite_combination
    {n : ℕ} (g : Fin n → G) (hg : ValidTuple g) {t : G}
    {c u : Fin n → ℤ} (hc : Witness g t c) (hu : Witness g (-t) u)
    (hshare : ∀ i, ¬(c i = -1 ∧ u i = -1)) :
    u = -c := by
  obtain ⟨hcne, hcfloor, hcsum, hcval⟩ := hc
  obtain ⟨hune, hufloor, husum, huval⟩ := hu
  have hno := (validTuple_iff_no_zero_witness g).mp hg
  by_contra hneg
  apply hno (c + u)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hneg
    funext i
    have hi := congrFun hzero i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    simp only [Pi.neg_apply]
    omega
  · intro i
    simp only [Pi.add_apply]
    by_cases hci : c i = -1
    · have hui : u i ≠ -1 := fun hui ↦ hshare i ⟨hci, hui⟩
      have hufloorI := hufloor i
      omega
    · have hcfloorI := hcfloor i
      have hufloorI := hufloor i
      omega
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hcsum, husum, add_zero]
  · have hterm : ∀ i, (c + u) i • g i = c i • g i + u i • g i := by
      intro i
      rw [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i,
      Finset.sum_add_distrib, hcval, huval, add_neg_cancel]

/-- A leaf-supported witness opposite to an external pure edge must omit the
other pure-edge endpoint.  The external endpoint cannot be a common omission
because the leaf witness vanishes there; without the retained omission,
opposite-target combination would make the leaf witness the negative pure
edge, again contradicting its external zero. -/
theorem mersenneLeaf_oppositeWitness_omits_pureEdgeEndpoint
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n)
    (t : G) (u : Fin n → ℤ) (hu : Witness g t u)
    (x b r : Fin n) (hxb : x ≠ b) (hxr : x ≠ r) (hbr : b ≠ r)
    (hshape : u = pureEdgeCoeffs x b r)
    (hb : b ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (c : Fin n → ℤ) (hc : Witness g (-t) c)
    (hcoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) :
    c r = -1 := by
  by_contra hcr
  have hshare : ∀ i, ¬(u i = -1 ∧ c i = -1) := by
    intro i hi
    have hiEdge : i = b ∨ i = r := by
      apply (pureEdgeCoeffs_eq_neg_one_iff x b r i hxb hxr hbr).1
      rw [← hshape]
      exact hi.1
    rcases hiEdge with hib | hir
    · subst i
      have hcb : c b = 0 := hcoff b hb
      omega
    · subst i
      exact hcr hi.2
  have hneg := witness_opposite_combination g hg hu hc hshare
  have hcb : c b = 0 := hcoff b hb
  have hub : u b = -1 := by
    rw [hshape]
    exact (pureEdgeCoeffs_eq_neg_one_iff x b r b hxb hxr hbr).2
      (Or.inl rfl)
  have hbEq := congrFun hneg b
  simp only [Pi.neg_apply, hcb, hub] at hbEq
  omega

/-- Normalize the negative of a pure-edge target on the pointed Mersenne leaf
and retain the forced omission at the pure edge's retained endpoint. -/
theorem exists_mersenneLeaf_oppositeWitness_omits_pureEdgeEndpoint
    {n d : ℕ} (hd : 3 ≤ d)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (g : Fin n → G) (hg : ValidTuple g) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (t : G) (ht : t ∈ AddSubgroup.zmultiples v) (ht0 : t ≠ 0)
    (u : Fin n → ℤ) (hu : Witness g t u)
    (x b r : Fin n) (hxb : x ≠ b) (hxr : x ≠ r) (hbr : b ≠ r)
    (hshape : u = pureEdgeCoeffs x b r)
    (hb : b ∉ (Finset.univ : Finset (Fin d)).image leaf) :
    ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧ -t = s • v ∧
      ∃ c : Fin n → ℤ, Witness g (-t) c ∧
        (∀ j, j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
        c r = -1 := by
  have hq : 0 < 2 ^ d - 1 := by
    have hpow : 0 < 2 ^ (d - 3) := pow_pos (by norm_num) _
    rw [show d = 3 + (d - 3) by omega, pow_add]
    norm_num
    omega
  have hnegMem : -t ∈ AddSubgroup.zmultiples v :=
    AddSubgroup.neg_mem _ ht
  have hneg0 : -t ≠ 0 := neg_ne_zero.mpr ht0
  obtain ⟨s, hs0, hsq, htarget⟩ :=
    exists_positive_nsmul_eq_of_mem_zmultiples hq hv hnegMem hneg0
  obtain ⟨c, hc, hcoff⟩ := exists_mersenneLeaf_ambientWitness_zero_off
    hd hs0 hsq root v hv g leaf hleaf e hnormal
  have hcTarget : Witness g (-t) c := by simpa only [htarget] using hc
  have hcr := mersenneLeaf_oppositeWitness_omits_pureEdgeEndpoint
    g hg leaf t u hu x b r hxb hxr hbr hshape hb c hcTarget hcoff
  exact ⟨s, hs0, hsq, htarget, c, hcTarget, hcoff, hcr⟩

/-- At the unique opposite external parameter, the fixed-sign canonical row
is exactly a pure edge centered at the retained coordinate opposite the
missing leaf. -/
theorem TwoRetainedCanonicalPrivatePresentation.external_coeff_eq_pureEdge_of_antipodal
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k₀ k : ℤ) (r : Fin n)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1)
    (hweight : p.weight b = 2 * k) :
    p.coeff b = pureEdgeCoeffs
      (if k₀ = -1 then p.z else p.x) (b : Fin n) r := by
  have hretained := p.retained_coefficients_of_owner_eq_neg_one
    g y B b k howner hweight
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  have hbx : (b : Fin n) ≠ p.x := fun h ↦ p.x_not_mem (h ▸ b.property)
  have hbz : (b : Fin n) ≠ p.z := fun h ↦ p.z_not_mem (h ▸ b.property)
  rcases hantipodal with ⟨hk₀, hk⟩ | ⟨hk₀, hk⟩
  · subst k₀
    subst k
    have hrx : r = p.x := by simpa only [if_true] using hr
    subst r
    have hx : p.coeff b p.x = -1 := by simpa using hretained.1
    have hz : p.coeff b p.z = 2 := by simpa using hretained.2
    funext i
    by_cases hib : i = (b : Fin n)
    · subst i
      simp [pureEdgeCoeffs, howner, hbx, hbz]
    by_cases hix : i = p.x
    · subst i
      simp [pureEdgeCoeffs, hx, hbx.symm, p.x_ne_z]
    by_cases hiz : i = p.z
    · subst i
      simp [pureEdgeCoeffs, hz, hbz.symm, p.x_ne_z.symm]
    have hiZero := hshape.2.1 i hib hix hiz
    simp [pureEdgeCoeffs, hiZero, hib, hix, hiz]
  · subst k₀
    subst k
    have hk₀Ne : (0 : ℤ) ≠ -1 := by norm_num
    have hrz : r = p.z := by simpa only [hk₀Ne, if_false] using hr
    subst r
    have hx : p.coeff b p.x = 2 := by simpa using hretained.1
    have hz : p.coeff b p.z = -1 := by simpa using hretained.2
    funext i
    by_cases hib : i = (b : Fin n)
    · subst i
      simp [pureEdgeCoeffs, howner, hbx, hbz]
    by_cases hix : i = p.x
    · subst i
      simp [pureEdgeCoeffs, hx, hbx.symm, p.x_ne_z]
    by_cases hiz : i = p.z
    · subst i
      simp [pureEdgeCoeffs, hz, hbz.symm, p.x_ne_z.symm]
    have hiZero := hshape.2.1 i hib hix hiz
    simp [pureEdgeCoeffs, hiZero, hib, hix, hiz]

/-- Complete antipodal endpoint: fix the row sign, identify its pure edge,
and construct a leaf-supported witness at the negative target which omits the
unique retained leaf. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_oppositeWitness
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (k₀ k : ℤ) (r : Fin n)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
        -(p.scalar b • y) = s • v ∧
        ∃ c : Fin n → ℤ, Witness g (-(p.scalar b • y)) c ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0) ∧
          c r = -1 := by
  dsimp only
  have hownerNeg := p.external_owner_eq_neg_one_of_mersenneLeaf
    g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb k
      howner hweight
  have hshape := p.external_coeff_eq_pureEdge_of_antipodal
    g y B b k₀ k r hr hantipodal hownerNeg hweight
  let center : Fin n := if k₀ = -1 then p.z else p.x
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
  have htMem : p.scalar b • y ∈ AddSubgroup.zmultiples v := by
    rw [hcyclic]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
  have hopp := exists_mersenneLeaf_oppositeWitness_omits_pureEdgeEndpoint
    hd root v hv g hg leaf hleaf e hnormal (p.scalar b • y) htMem
      (p.target_ne_zero b) (p.coeff b) (p.isWitness b) center (b : Fin n) r
      hcenterB hcenterR hbr (by simpa only [center] using hshape) hb
  exact ⟨hownerNeg, hshape, hopp⟩

end MinModulus
