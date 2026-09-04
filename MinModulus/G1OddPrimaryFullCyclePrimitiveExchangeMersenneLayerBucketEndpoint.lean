/-
# The exact-Mersenne external endpoint is impossible

This module wires the lossless five-external-row geometry into the certified
four-layer bucket contradiction.  The four blocks are the complete pointed
leaf, secondary, and final fibers together with the retained coordinate not
used as the pointed root.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLayerBucketContradiction

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The mixed five-external-row endpoint cannot occur at exact Mersenne order.
The proof retains the actual secondary and final fibers and uses their
canonical row parameters as the quotient-coset representatives required by
the certified layer bucket. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.false_of_exactMersenneOrder
    {d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (h17 : 17 ≤ d) (h57 : d ≤ 57) (hq : q = 2 ^ d - 1)
    (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hleafMem : ∀ i, leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (L : Finset (Fin n))
    (hL : L = (Finset.univ : Finset (Fin d)).image leaf)
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows g y B L p k₀) :
    False := by
  classical
  rcases hfive with
    ⟨T, k₁, t, F, _hTcard, _hTle, _hFle, hTsub, htT,
      hk₁Mem, hk₁Ne, _hparameter, hTrows, _hTexact, _hTadjacent,
      hTcomplete, _hTseparated, hpartition, hTFdisjoint, _hcard,
      hprofiles, hFcase, hcap, _hcritical⟩
  have hprofile := exactMersenne_externalProfiles_four_or_three
    d q T F h17 h57 hq hprofiles (by
      simpa only [hL, Finset.card_image_of_injective _ hleaf,
        Finset.card_univ, Fintype.card_fin] using hcap)
  have hFne : F ≠ ∅ := by
    intro hF
    rcases hprofile.2 with hfour | hthree
    · rw [hF] at hfour
      simp at hfour
    · rw [hF] at hthree
      simp at hthree
  rcases hFcase with hFempty | hFdata
  · exact hFne hFempty
  rcases hFdata with
    ⟨k₂, f, hfF, hk₂Mem, hk₂Ne₀, hk₂Ne₁, _hFparameter,
      _hadjacent, hFrows, _hFexact, _hFavoid, hFcomplete⟩
  have hTsubB : T ⊆ B := fun x hx ↦ (Finset.mem_sdiff.mp (hTsub hx)).1
  have hFsub : F ⊆ B \ L := by
    intro x hx
    rw [hpartition]
    exact Finset.mem_union_right T hx
  have hFsubB : F ⊆ B := fun x hx ↦ (Finset.mem_sdiff.mp (hFsub hx)).1
  let s : Fin n := if k₀ = -1 then p.z else p.x
  have hsne : s ≠ r := by
    rw [hr]
    rcases hmiddle with hk | hk
    · simpa [s, hk] using p.x_ne_z.symm
    · simpa [s, hk] using p.x_ne_z
  have hsNotB : s ∉ B := by
    rcases hmiddle with hk | hk
    · simpa [s, hk] using p.z_not_mem
    · have hkNe : k₀ ≠ -1 := by omega
      simpa [s, hk, hkNe] using p.x_not_mem
  have hLroot_or_mem : ∀ x ∈ L, x = r ∨ x ∈ B := by
    intro x hx
    rw [hL] at hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    let i : Fin d := e.symm j
    have hei : e i = j := e.apply_symm_apply j
    rw [← hei]
    by_cases hi : i = ⟨0, by omega⟩
    · left
      rw [hi, hrzero]
    · right
      exact (hleafMem i).2 hi
  have hsNotL : s ∉ L := by
    intro hsL
    rcases hLroot_or_mem s hsL with hsr | hsB
    · exact hsne hsr
    · exact hsNotB hsB
  have hLT : Disjoint L T := by
    rw [Finset.disjoint_left]
    intro x hxL hxT
    exact (Finset.mem_sdiff.mp (hTsub hxT)).2 hxL
  have hLF : Disjoint L F := by
    rw [Finset.disjoint_left]
    intro x hxL hxF
    exact (Finset.mem_sdiff.mp (hFsub hxF)).2 hxL
  have hLs : Disjoint L ({s} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro x hxL hxs
    rw [Finset.mem_singleton.mp hxs] at hxL
    exact hsNotL hxL
  have hTs : Disjoint T ({s} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro x hxT hxs
    rw [Finset.mem_singleton.mp hxs] at hxT
    exact hsNotB (hTsubB hxT)
  have hFs : Disjoint F ({s} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro x hxF hxs
    rw [Finset.mem_singleton.mp hxs] at hxF
    exact hsNotB (hFsubB hxF)
  have hLcoset : ∀ x ∈ L,
      g x - g r ∈ AddSubgroup.zmultiples y := by
    intro x hx
    rw [hL] at hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    let i : Fin d := e.symm j
    have hei : e i = j := e.apply_symm_apply j
    rw [← hei, ← hrzero, hnormal i, hnormal ⟨0, by omega⟩]
    rw [← hcyclic]
    simpa [a] using
      (AddSubgroup.zmultiples v).nsmul_mem
        (AddSubgroup.mem_zmultiples v) (a i.val)
  have hTcoset : ∀ x ∈ T,
      g x - g t ∈ AddSubgroup.zmultiples y := by
    intro x hx
    exact (hTcomplete ⟨x, hTsubB hx⟩).mp hx
  have hFcoset : ∀ x ∈ F,
      g x - g f ∈ AddSubgroup.zmultiples y := by
    intro x hx
    exact (hFcomplete ⟨x, hFsubB hx⟩).mp hx
  have hscoset : ∀ x ∈ ({s} : Finset (Fin n)),
      g x - g s ∈ AddSubgroup.zmultiples y := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    simp
  have hrCorrected :
      g r - g p.z + k₀ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y := by
    rcases hmiddle with hk | hk
    · rw [hr]
      simp [hk]
    · rw [hr]
      simp [hk]
  have htCorrected :
      g t - g p.z + k₁ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y :=
    (hTrows ⟨t, hTsubB htT⟩ htT).2.2.1
  have hfCorrected :
      g f - g p.z + k₂ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y :=
    (hFrows ⟨f, hFsubB hfF⟩ hfF).2.2.1
  have hsCorrected :
      g s - g p.z + (-1 - k₀) • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y := by
    rcases hmiddle with hk | hk
    · simp [s, hk]
    · simp [s, hk]
  have horderVY : addOrderOf v = addOrderOf y := by
    have hcards := congrArg
      (fun H : AddSubgroup (ZMod (2 ^ 6 * q)) ↦ Nat.card H) hcyclic
    simpa only [Nat.card_zmultiples] using hcards
  have horderY : addOrderOf y = 2 ^ d - 1 := by omega
  let S := exactMersenneSelectedLayerProfiles
    d k₀ k₁ k₂ T.card F.card
  have hcertificate :
      MersenneExternalLayerBucketCertificate
        d k₀ k₁ k₂ T.card F.card S :=
    exactMersenneSelectedLayerProfiles_certificate
      d k₀ k₁ k₂ T.card F.card hprofile.1 h57 hmiddle
        hk₁Mem hk₂Mem hk₁Ne hk₂Ne₀ hk₂Ne₁ hprofile.2
  exact false_of_mersenneExternalLayerBucketCertificate
    g hg y L T F {s} hLT hLF hLs hTFdisjoint hTs hFs
      r t f s (g p.z) (g p.x - g p.z) k₀ k₁ k₂
      hLcoset hTcoset hFcoset hscoset
      hrCorrected htCorrected hfCorrected hsCorrected
      d T.card F.card
      (by simp [hL, Finset.card_image_of_injective _ hleaf])
      rfl rfl (by simp)
      S hcertificate horderY

/-- The lossless pointed normal-form residual is itself contradictory at the
exact Mersenne value of the odd factor. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRowNormalFormResidual.false_of_exactMersenneOrder
    {d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q)) (hq : q = 2 ^ d - 1)
    (hresidual : PrimitiveMiddleExactMersenneFiveExternalRowNormalFormResidual
      g y B leaf base) : False := by
  rcases hresidual.2 with ⟨p, S₀, T₀, Sfull, k₀, w, hfixed, hpointed⟩
  rcases hfixed with
    ⟨_hdata, _hSsubset, _hprimitive, _hScard, _hSsub, hmiddle,
      _hrows, _hcomplete, _hwindow⟩
  dsimp only at hpointed
  rcases hpointed with
    ⟨missing, hd, e, _hpunctured, hmissing, _hSfull, _hw,
      _hn, _hBcard, h17, h57, hezero, hleafOrder, hnormal,
      hcyclic, _μ, _ν, _hμ, _hν, _hnormalY, hleafMem,
      _hprimaryDigit, hfive⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hrzero : leaf (e ⟨0, by omega⟩) = r := by
    rw [hezero]
    simpa only [r] using hmissing
  have hv : addOrderOf (g (leaf missing) - base) = 2 ^ d - 1 :=
    hleafOrder.trans hq
  exact hfive.false_of_exactMersenneOrder
    g hg y (g (leaf missing)) (g (leaf missing) - base) B p
      h17 h57 hq hv leaf hleaf e hnormal hcyclic r hrzero
      hleafMem k₀ hmiddle rfl L rfl

/-- Consequently the earlier dimension-locked exact-Mersenne residual is
impossible whenever its pointed doubling cycle is retained. -/
theorem PrimitiveMiddleExactMersenneDimensionLockedResidual.false_of_exactMersenneOrder
    {d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hq : q = 2 ^ d - 1)
    (hresidual : PrimitiveMiddleExactMersenneDimensionLockedResidual
      g y B leaf base) : False := by
  have hnormal := hresidual.toFiveExternalRowNormalFormResidual
    g hg y hyq hfullOdd B hretained hcritical leaf R hcycle hRne
      base hdouble
  exact hnormal.false_of_exactMersenneOrder
    g hg y B leaf hleaf base hq

end MinModulus
