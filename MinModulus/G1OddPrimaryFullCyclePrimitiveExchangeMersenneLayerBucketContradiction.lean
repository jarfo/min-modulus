/-
# From a certified layer bucket to contradiction

The exact-Mersenne arithmetic table is independent of the geometry that
produces its four coordinate blocks.  This module supplies the bridge between
them.  Once four disjoint blocks have the certified cardinalities, lie in the
four prescribed kernel cosets, and the kernel generator has Mersenne order,
the common-bucket capacity theorem contradicts the certificate's strict mass
inequality.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLayerBucketTable

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- A certified external layer bucket whose four concrete blocks lie in the
prescribed quotient cosets cannot fit in a cyclic kernel of Mersenne order. -/
theorem false_of_mersenneExternalLayerBucketCertificate
    [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (A C D R : Finset (Fin n))
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hAR : Disjoint A R)
    (hCD : Disjoint C D) (hCR : Disjoint C R) (hDR : Disjoint D R)
    (a c e r : Fin n) (z δ : G) (k₀ k₁ k₂ : ℤ)
    (hAcoset : ∀ x ∈ A, g x - g a ∈ AddSubgroup.zmultiples y)
    (hCcoset : ∀ x ∈ C, g x - g c ∈ AddSubgroup.zmultiples y)
    (hDcoset : ∀ x ∈ D, g x - g e ∈ AddSubgroup.zmultiples y)
    (hRcoset : ∀ x ∈ R, g x - g r ∈ AddSubgroup.zmultiples y)
    (ha : g a - z + k₀ • δ ∈ AddSubgroup.zmultiples y)
    (hc : g c - z + k₁ • δ ∈ AddSubgroup.zmultiples y)
    (he : g e - z + k₂ • δ ∈ AddSubgroup.zmultiples y)
    (hr : g r - z + (-1 - k₀) • δ ∈ AddSubgroup.zmultiples y)
    (d t f : ℕ) (hAcard : A.card = d) (hCcard : C.card = t)
    (hDcard : D.card = f) (hRcard : R.card = 1)
    (S : Finset FourLayerProfile)
    (hcertificate :
      MersenneExternalLayerBucketCertificate d k₀ k₁ k₂ t f S)
    (horder : addOrderOf y = 2 ^ d - 1) : False := by
  classical
  rcases hcertificate with
    ⟨hSpos, _hfirst, _hsecond, _hthird, _hfourth,
      htotal, hweight, hmass⟩
  obtain ⟨P₀, hP₀⟩ := Finset.card_pos.mp hSpos
  let Pbase : ↑S := ⟨P₀, hP₀⟩
  let base : G :=
    Pbase.1.first • g a + Pbase.1.second • g c +
      Pbase.1.third • g e + Pbase.1.fourth • g r
  have hprofile : Function.Injective fun P : ↑S ↦
      ((P.1.first, P.1.second), (P.1.third, P.1.fourth)) := by
    intro P Q hPQ
    apply Subtype.ext
    rcases P with ⟨⟨pa, pc, pe, pr⟩, hP⟩
    rcases Q with ⟨⟨qa, qc, qe, qr⟩, hQ⟩
    simp only [Prod.mk.injEq] at hPQ
    rcases hPQ with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    rfl
  have hcommonTotal : ∀ P : ↑S,
      P.1.first + P.1.second + P.1.third + P.1.fourth = d / 2 + 3 := by
    intro P
    exact htotal P
  have hcorrection : ∀ P : ↑S,
      P.1.first • g a + P.1.second • g c + P.1.third • g e +
          P.1.fourth • g r - base ∈ AddSubgroup.zmultiples y := by
    intro P
    apply four_kernelCosetCorrection_sub_mem
      (AddSubgroup.zmultiples y) z δ (g a) (g c) (g e) (g r)
      k₀ k₁ k₂ (-1 - k₀) ha hc he hr
    · rw [hcommonTotal P, hcommonTotal Pbase]
    · exact hweight P Pbase
  have hcapacity :=
    sum_fourLayerChoices_le_addOrderOf_of_common_kernelBucket
      g hg y A C D R hAC hAD hAR hCD hCR hDR
      (fun P : ↑S ↦ P.1.first) (fun P : ↑S ↦ P.1.second)
      (fun P : ↑S ↦ P.1.third) (fun P : ↑S ↦ P.1.fourth)
      hprofile (d / 2 + 3) hcommonTotal a c e r
      hAcoset hCcoset hDcoset hRcoset base hcorrection
  have hcapacity' :
      (∑ P ∈ S, P.mass d t f) ≤ addOrderOf y := by
    rw [hAcard, hCcard, hDcard, hRcard] at hcapacity
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
    simpa only [FourLayerProfile.mass] using hcapacity
  rw [horder] at hcapacity'
  exact (Nat.not_lt_of_ge hcapacity') hmass

end MinModulus
