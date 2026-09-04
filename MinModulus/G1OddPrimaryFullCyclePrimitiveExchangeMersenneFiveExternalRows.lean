/-
# Same-presentation row normal form for the five external coordinates

The exact Mersenne survivor has five deleted coordinates outside its pointed
super-increasing leaf cycle.  The exhaustive three-residue partition places
them in a secondary complete fiber and an optional final complete fiber.

This module retains the actual canonical row parameters and equations on the
same private presentation that points the leaf cycle.  Thus the three possible
external size profiles can be compared directly with the binary digit system;
no existential presentation alignment remains.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneFiveExternal

namespace MinModulus

open Finset

variable {n : ℕ}

/-- For a canonical unit row, the corrected owner coordinate is not merely in
the odd cyclic subgroup: it is exactly the private target scalar, with sign
given by the owner coefficient. -/
theorem TwoRetainedCanonicalPrivatePresentation.corrected_eq_owner_smul_scalar
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k : ℤ)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    g (b : Fin n) - g p.z + k • (g p.x - g p.z) =
      p.coeff b (b : Fin n) • (p.scalar b • y) := by
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases howner with hminus | hone
  · have hx : p.coeff b p.x = -k := by
      have hw := p.weight_eq b
      rw [hminus, hweight] at hw
      norm_num [twoRetainedOwnerNormalization] at hw
      omega
    rw [hshape.2.2, hshape.1, hminus, hx]
    module
  · have hx : p.coeff b p.x = k := by
      have hw := p.weight_eq b
      rw [hone, hweight] at hw
      norm_num [twoRetainedOwnerNormalization] at hw
      omega
    rw [hshape.2.2, hshape.1, hone, hx]
    module

/-- The exact five-coordinate external partition, with every secondary and
final canonical private-row equation retained on one presentation. -/
def PrimitiveMiddleExactMersenneFiveExternalRows
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B L : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Prop :=
  ∃ T : Finset (Fin n), ∃ k₁ : ℤ, ∃ t : Fin n,
    ∃ F : Finset (Fin n),
      3 ≤ T.card ∧ T.card ≤ 5 ∧ F.card ≤ 2 ∧
      T ⊆ B \ L ∧ t ∈ T ∧
      k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧ k₁ ≠ k₀ ∧
      (∀ b : ↥B, (b : Fin n) ∈ T →
        (p.coeff b (b : Fin n) = -1 ∨
          p.coeff b (b : Fin n) = 1) ∧
        p.weight b = 2 * k₁ ∧
        g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p.z) =
          -(k₁ •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p.x - g p.z))) ∧
      (∀ b : ↥B, (b : Fin n) ∈ T →
        g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) =
          p.coeff b (b : Fin n) • (p.scalar b • y)) ∧
      (∀ b : ↥B,
        ((b : Fin n) ∈ T ↔
          g (b : Fin n) - g t ∈ AddSubgroup.zmultiples y)) ∧
      (∀ b ∈ T, ∀ c ∈ L,
        g b - g c ∉ AddSubgroup.zmultiples y) ∧
      B \ L = T ∪ F ∧ Disjoint T F ∧
      T.card + F.card = 5 ∧
      ((T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2)) ∧
      (F = ∅ ∨
        ∃ k₂ : ℤ, ∃ f : Fin n,
          f ∈ F ∧
          k₂ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
          k₂ ≠ k₀ ∧ k₂ ≠ k₁ ∧
          (∀ b : ↥B, (b : Fin n) ∈ F →
            (p.coeff b (b : Fin n) = -1 ∨
              p.coeff b (b : Fin n) = 1) ∧
            p.weight b = 2 * k₂ ∧
            g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) ∈
              AddSubgroup.zmultiples y ∧
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.z) =
              -(k₂ •
                (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g p.x - g p.z))) ∧
          (∀ b : ↥B, (b : Fin n) ∈ F →
            g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) =
              p.coeff b (b : Fin n) • (p.scalar b • y)) ∧
          ∀ b : ↥B,
            ((b : Fin n) ∈ F ↔
              g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y)) ∧
      (∀ i j k : ℕ,
        L.card.choose i * T.card.choose j * F.card.choose k ≤ q) ∧
      48 * (L.card.choose (L.card / 2) *
        F.card.choose (F.card / 2)) < 2 ^ B.card

/-- Lossless endpoint in which the pointed leaf normal form and all five
external canonical rows use the same private presentation. -/
def PrimitiveMiddleExactMersenneFiveExternalRowNormalFormResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (base : ZMod (2 ^ 6 * q)) : Prop :=
  PrimitiveMiddleExactMersenneDimensionLockedResidual
      g y B leaf base ∧
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      ∃ S T₀ Sfull : Finset (Fin n), ∃ k₀ w : ℤ,
        PrimitiveMiddleExactMersenneFixedPresentationData
          g y B leaf p S T₀ Sfull k₀ w ∧
        let r := primitiveMiddleInsertedCoordinate p k₀
        let L := (Finset.univ : Finset (Fin d)).image leaf
        ∃ missing : Fin d, ∃ hd : 0 < d, ∃ e : Fin d ≃ Fin d,
          (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
          leaf missing = r ∧ Sfull = L.erase r ∧ w = -2 ∧
          n = d + 6 ∧ B.card = d + 4 ∧ 17 ≤ d ∧ d ≤ 57 ∧
          e ⟨0, hd⟩ = missing ∧
          addOrderOf (g (leaf missing) - base) = q ∧
          (∀ k : Fin d,
            g (leaf (e k)) =
              g (leaf missing) +
                a k.val • (g (leaf missing) - base)) ∧
          PrimitiveMiddleExactMersenneFiveExternalRows
            g y B L p k₀

/-- Rebuild the pointed cycle and the exhaustive external residue partition
from one dimension-locked presentation, retaining all row equations and
capacity bounds without changing witnesses. -/
theorem PrimitiveMiddleExactMersenneDimensionLockedResidual.toFiveExternalRowNormalFormResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hresidual :
      PrimitiveMiddleExactMersenneDimensionLockedResidual
        g y B leaf base) :
    PrimitiveMiddleExactMersenneFiveExternalRowNormalFormResidual
      g y B leaf base := by
  classical
  refine ⟨hresidual, ?_⟩
  rcases hresidual with
    ⟨p, S, T₀, Sfull, k₀, w, hfixed, missing, hpunctured,
      hmissing, hCeq, hSeq, hcard, hw, hleafOrder, hLcap,
      hLcoset, hLgap, hfive, hseparated, hsecondary,
      hcriticalBound, hn, hBcard, hexternal, hdLower, hdUpper⟩
  rcases hfixed with
    ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
      hrows, hcomplete, hwindow⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hSrows : ∀ b : ↥B, (b : Fin n) ∈ Sfull →
      p.weight b = 2 * k₀ := by
    intro b hb
    exact (hrows b hb).1
  have hthree := hsecondary.toThreeResiduePartition
    g y B L Sfull p k₀ hprimitive hyq hfullOdd hmiddle hwindow
      hSsub hSrows (by simpa only [r, L] using hcomplete)
  rcases hthree with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hUTcap, hfinal⟩
  rcases hfinal with ⟨F, hpartition, hFsub, hFcase⟩
  have hrL : r ∈ L := by
    exact Finset.mem_image.mpr
      ⟨missing, Finset.mem_univ _, by simpa only [r] using hmissing⟩
  have hLnonempty : L.Nonempty := ⟨r, hrL⟩
  have hFsimple : F = ∅ ∨
      ∃ f : Fin n, f ∈ F ∧
        ∀ b : ↥B,
          ((b : Fin n) ∈ F ↔
            g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y) := by
    rcases hFcase with hFempty | hFfull
    · exact Or.inl hFempty
    · rcases hFfull with
        ⟨_k₂, f, hfF, _hk₂Mem, _hk₂Ne₀, _hk₂Ne₁,
          _hFrows, hFcomplete⟩
      exact Or.inr ⟨f, hfF, hFcomplete⟩
  have hcap := primaryUnion_threeResidue_fullLayerCapacity
    g hg y B L Sfull T F p k₀ hyq hfullOdd hLnonempty hLcoset hrL
      (by simpa only [r] using hcomplete) t htT hTsub hTcomplete
        hUTcap hFsub hFsimple
  have hcrit :=
    fortyEight_mul_primaryFinalCentralChoose_lt_two_pow_transversalCard
      B L T F hretained hcritical hTcard hcap
  have hrNotB : r ∉ B := by
    intro hrB
    have hmB : leaf missing ∈ B := by
      rw [hmissing]
      exact hrB
    exact ((hpunctured missing).1 hmB) rfl
  have hSsubL : Sfull ⊆ L := by
    rw [hSeq]
    exact Finset.erase_subset _ _
  have hBinterL : B ∩ L = Sfull := by
    ext b
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hbB, hbL⟩
      rw [hSeq]
      exact Finset.mem_erase.mpr
        ⟨by
          intro hbr
          rw [hbr] at hbB
          exact hrNotB hbB,
         hbL⟩
    · intro hbS
      exact ⟨hSsub hbS, hSsubL hbS⟩
  obtain ⟨hexternalPartition, hTFdisjoint⟩ :=
    sdiff_eq_union_of_inter_threePartition
      B L Sfull T F hBinterL hTsub hpartition hFsub
  have hTFcard : T.card + F.card = 5 := by
    rw [hexternalPartition] at hexternal
    rw [Finset.card_union_of_disjoint hTFdisjoint] at hexternal
    exact hexternal
  have hTle : T.card ≤ 5 := by omega
  have hFle : F.card ≤ 2 := by omega
  have hprofiles :
      (T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2) := by
    omega
  have hd : 0 < d := by omega
  let e : Fin d ≃ Fin d := fullCycleOrbitEquiv R hcycle hRne missing
  have hezero : e ⟨0, hd⟩ = missing := by
    simp only [e, fullCycleOrbitEquiv_apply]
    rfl
  have hnormal : ∀ k : Fin d,
      g (leaf (e k)) =
        g (leaf missing) +
          a k.val • (g (leaf missing) - base) := by
    intro k
    exact fullCycleLeaf_eq_point_add_superincreasing
      g leaf R hcycle hRne missing base hdouble k
  have hTexact : ∀ b : ↥B, (b : Fin n) ∈ T →
      g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) =
        p.coeff b (b : Fin n) • (p.scalar b • y) := by
    intro b hbT
    exact p.corrected_eq_owner_smul_scalar g y B b k₁
      (hTrows b hbT).1 (hTrows b hbT).2.1
  have hFcaseExact :
      F = ∅ ∨
        ∃ k₂ : ℤ, ∃ f : Fin n,
          f ∈ F ∧
          k₂ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
          k₂ ≠ k₀ ∧ k₂ ≠ k₁ ∧
          (∀ b : ↥B, (b : Fin n) ∈ F →
            (p.coeff b (b : Fin n) = -1 ∨
              p.coeff b (b : Fin n) = 1) ∧
            p.weight b = 2 * k₂ ∧
            g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) ∈
              AddSubgroup.zmultiples y ∧
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.z) =
              -(k₂ •
                (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g p.x - g p.z))) ∧
          (∀ b : ↥B, (b : Fin n) ∈ F →
            g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) =
              p.coeff b (b : Fin n) • (p.scalar b • y)) ∧
          ∀ b : ↥B,
            ((b : Fin n) ∈ F ↔
              g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y) := by
    rcases hFcase with hFempty | hFfull
    · exact Or.inl hFempty
    · rcases hFfull with
        ⟨k₂, f, hfF, hk₂Mem, hk₂Ne₀, hk₂Ne₁,
          hFrows, hFcomplete⟩
      refine Or.inr ⟨k₂, f, hfF, hk₂Mem, hk₂Ne₀, hk₂Ne₁,
        hFrows, ?_, hFcomplete⟩
      intro b hbF
      exact p.corrected_eq_owner_smul_scalar g y B b k₂
        (hFrows b hbF).1 (hFrows b hbF).2.1
  refine ⟨p, S, T₀, Sfull, k₀, w, ?_, ?_⟩
  · exact ⟨hdata, hSsubset, hprimitive, hScard, hSsub, hmiddle,
      hrows, hcomplete, hwindow⟩
  · change ∃ missing : Fin d, ∃ hd : 0 < d, ∃ e : Fin d ≃ Fin d,
      (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
      leaf missing = r ∧ Sfull = L.erase r ∧ w = -2 ∧
      n = d + 6 ∧ B.card = d + 4 ∧ 17 ≤ d ∧ d ≤ 57 ∧
      e ⟨0, hd⟩ = missing ∧
      addOrderOf (g (leaf missing) - base) = q ∧
      (∀ k : Fin d,
        g (leaf (e k)) =
          g (leaf missing) +
            a k.val • (g (leaf missing) - base)) ∧
      PrimitiveMiddleExactMersenneFiveExternalRows
        g y B L p k₀
    refine ⟨missing, hd, e, hpunctured, hmissing, hSeq, hw,
      hn, hBcard, hdLower, hdUpper, hezero, hleafOrder missing,
      hnormal, ?_⟩
    exact ⟨T, k₁, t, F, hTcard, hTle, hFle, hTsub, htT,
      hk₁Mem, hk₁Ne, hTrows, hTexact, hTcomplete, hTseparated,
      hexternalPartition, hTFdisjoint, hTFcard, hprofiles,
      hFcaseExact, hcap, hcrit⟩

end MinModulus
