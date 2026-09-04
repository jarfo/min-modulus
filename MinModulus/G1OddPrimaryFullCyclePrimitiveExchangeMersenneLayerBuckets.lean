/-
# Same-cardinality subset buckets in a cyclic kernel

Fixed-layer capacity treats one prescribed cardinality in each kernel coset.
For the exact Mersenne endpoint this loses information: several different
layer profiles can have the same total cardinality and the same image in the
quotient.  Their subset sums then occupy one common bucket in the cyclic
kernel, so their cardinalities must be added before applying capacity.

This module isolates that principle without reference to the Mersenne
classification.  Any injectively parametrized family of equal-cardinality
coordinate subsets whose sums lie in one translate of `zmultiples y` has at
most `addOrderOf y` members.  The finset bucket form is the interface used by
the external-profile arithmetic.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneExternalProfileElimination

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- An arbitrary injectively parametrized family of equal-cardinality subset
sums fits in one cyclic-kernel bucket.  This is the all-layer version of the
fixed-layer capacity argument. -/
theorem fintype_card_le_addOrderOf_of_sameCard_kernelSubsetSums
    [Fintype G] {ι : Type*} [Fintype ι]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (subset : ι → Finset (Fin n)) (hsubset : Function.Injective subset)
    (r : ℕ) (hcard : ∀ u, (subset u).card = r)
    (base : G)
    (hkernel : ∀ u,
      (∑ i ∈ subset u, g i) - base ∈ AddSubgroup.zmultiples y) :
    Fintype.card ι ≤ addOrderOf y := by
  classical
  let encode : ι → AddSubgroup.zmultiples y := fun u ↦
    ⟨(∑ i ∈ subset u, g i) - base, hkernel u⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    have hvalue := congrArg Subtype.val huv
    dsimp only [encode] at hvalue
    have hsum : (∑ i ∈ subset u, g i) = ∑ i ∈ subset v, g i := by
      exact sub_left_injective hvalue
    apply hsubset
    apply validTuple_subsetSum_eq_of_card_eq g hg
      (Function.Embedding.refl (Fin n))
    · rw [hcard u, hcard v]
    · simpa using hsum
  have hbound := Fintype.card_le_of_injective encode hencode
  simpa only [← Nat.card_eq_fintype_card, Nat.card_zmultiples] using hbound

/-- Equal-cardinality coordinate subsets whose sums lie in one translate of
the cyclic kernel. -/
noncomputable def kernelSubsetSumBucket
    (g : Fin n → G) (y : G) (r : ℕ) (base : G) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard r).filter fun S ↦
    (∑ i ∈ S, g i) - base ∈ AddSubgroup.zmultiples y

/-- Every full same-cardinality kernel bucket has cyclic capacity. -/
theorem card_kernelSubsetSumBucket_le_addOrderOf
    [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (r : ℕ) (base : G) :
    (kernelSubsetSumBucket g y r base).card ≤ addOrderOf y := by
  classical
  let ι := ↑(kernelSubsetSumBucket g y r base)
  let subset : ι → Finset (Fin n) := fun S ↦ S.1
  have hsubset : Function.Injective subset := by
    intro S T hST
    exact Subtype.ext hST
  have hcard : ∀ S : ι, (subset S).card = r := by
    intro S
    have hmem := S.2
    change S.1 ∈ (Finset.univ.powersetCard r).filter (fun U ↦
      (∑ i ∈ U, g i) - base ∈ AddSubgroup.zmultiples y) at hmem
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hmem).1).2
  have hkernel : ∀ S : ι,
      (∑ i ∈ subset S, g i) - base ∈ AddSubgroup.zmultiples y := by
    intro S
    have hmem := S.2
    change S.1 ∈ (Finset.univ.powersetCard r).filter (fun U ↦
      (∑ i ∈ U, g i) - base ∈ AddSubgroup.zmultiples y) at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hbound :=
    fintype_card_le_addOrderOf_of_sameCard_kernelSubsetSums
      g hg y subset hsubset r hcard base hkernel
  simpa only [ι, Fintype.card_coe] using hbound

/-- Choices of one prescribed-cardinality layer in each of four coordinate
blocks. -/
abbrev FourLayerChoices
    {α : Type*} (A C D R : Finset α) (i j k l : ℕ) :=
  ↥(A.powersetCard i) ×
    ↥(C.powersetCard j) ×
      ↥(D.powersetCard k) × ↥(R.powersetCard l)

/-- Union the four selected layers into one coordinate subset. -/
def fourLayerCombined
    {α : Type*} [DecidableEq α] {A C D R : Finset α} {i j k l : ℕ}
    (P : FourLayerChoices A C D R i j k l) : Finset α :=
  ((P.1.1 ∪ P.2.1.1) ∪ P.2.2.1.1) ∪ P.2.2.2.1

theorem fourLayerCombined_card
    {α : Type*} [DecidableEq α]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hAR : Disjoint A R)
    (hCD : Disjoint C D) (hCR : Disjoint C R) (hDR : Disjoint D R)
    (P : FourLayerChoices A C D R i j k l) :
    (fourLayerCombined P).card = i + j + k + l := by
  have ha := (Finset.mem_powersetCard.mp P.1.2).2
  have hc := (Finset.mem_powersetCard.mp P.2.1.2).2
  have hd := (Finset.mem_powersetCard.mp P.2.2.1.2).2
  have hr := (Finset.mem_powersetCard.mp P.2.2.2.2).2
  have hac : Disjoint P.1.1 P.2.1.1 :=
    hAC.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.1.2).1
  have had : Disjoint P.1.1 P.2.2.1.1 :=
    hAD.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hcd : Disjoint P.2.1.1 P.2.2.1.1 :=
    hCD.mono (Finset.mem_powersetCard.mp P.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have har : Disjoint P.1.1 P.2.2.2.1 :=
    hAR.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hcr : Disjoint P.2.1.1 P.2.2.2.1 :=
    hCR.mono (Finset.mem_powersetCard.mp P.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hdr : Disjoint P.2.2.1.1 P.2.2.2.1 :=
    hDR.mono (Finset.mem_powersetCard.mp P.2.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hacdR : Disjoint ((P.1.1 ∪ P.2.1.1) ∪ P.2.2.1.1) P.2.2.2.1 := by
    rw [Finset.disjoint_left]
    intro x hx hxr
    rcases Finset.mem_union.mp hx with hac | hd
    · rcases Finset.mem_union.mp hac with ha | hc
      · exact Finset.disjoint_left.mp har ha hxr
      · exact Finset.disjoint_left.mp hcr hc hxr
    · exact Finset.disjoint_left.mp hdr hd hxr
  have hacD : Disjoint (P.1.1 ∪ P.2.1.1) P.2.2.1.1 := by
    rw [Finset.disjoint_left]
    intro x hx hxd
    rcases Finset.mem_union.mp hx with ha | hc
    · exact Finset.disjoint_left.mp had ha hxd
    · exact Finset.disjoint_left.mp hcd hc hxd
  rw [fourLayerCombined,
    Finset.card_union_of_disjoint hacdR,
    Finset.card_union_of_disjoint hacD,
    Finset.card_union_of_disjoint hac, ha, hc, hd, hr]

theorem fourLayerCombined_sum
    {α : Type*} [DecidableEq α] {H : Type*} [AddCommGroup H]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hAR : Disjoint A R)
    (hCD : Disjoint C D) (hCR : Disjoint C R) (hDR : Disjoint D R)
    (value : α → H) (P : FourLayerChoices A C D R i j k l) :
    (∑ x ∈ fourLayerCombined P, value x) =
      (∑ x ∈ P.1.1, value x) + (∑ x ∈ P.2.1.1, value x) +
        (∑ x ∈ P.2.2.1.1, value x) +
          ∑ x ∈ P.2.2.2.1, value x := by
  have hac : Disjoint P.1.1 P.2.1.1 :=
    hAC.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.1.2).1
  have had : Disjoint P.1.1 P.2.2.1.1 :=
    hAD.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hcd : Disjoint P.2.1.1 P.2.2.1.1 :=
    hCD.mono (Finset.mem_powersetCard.mp P.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have har : Disjoint P.1.1 P.2.2.2.1 :=
    hAR.mono (Finset.mem_powersetCard.mp P.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hcr : Disjoint P.2.1.1 P.2.2.2.1 :=
    hCR.mono (Finset.mem_powersetCard.mp P.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hdr : Disjoint P.2.2.1.1 P.2.2.2.1 :=
    hDR.mono (Finset.mem_powersetCard.mp P.2.2.1.2).1
      (Finset.mem_powersetCard.mp P.2.2.2.2).1
  have hacdR : Disjoint ((P.1.1 ∪ P.2.1.1) ∪ P.2.2.1.1) P.2.2.2.1 := by
    rw [Finset.disjoint_left]
    intro x hx hxr
    rcases Finset.mem_union.mp hx with hac | hd
    · rcases Finset.mem_union.mp hac with ha | hc
      · exact Finset.disjoint_left.mp har ha hxr
      · exact Finset.disjoint_left.mp hcr hc hxr
    · exact Finset.disjoint_left.mp hdr hd hxr
  have hacD : Disjoint (P.1.1 ∪ P.2.1.1) P.2.2.1.1 := by
    rw [Finset.disjoint_left]
    intro x hx hxd
    rcases Finset.mem_union.mp hx with ha | hc
    · exact Finset.disjoint_left.mp had ha hxd
    · exact Finset.disjoint_left.mp hcd hc hxd
  rw [fourLayerCombined,
    Finset.sum_union hacdR,
    Finset.sum_union hacD, Finset.sum_union hac]

theorem fourLayerCombined_inter_first
    {α : Type*} [DecidableEq α]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hAR : Disjoint A R)
    (P : FourLayerChoices A C D R i j k l) :
    fourLayerCombined P ∩ A = P.1.1 := by
  ext x
  simp only [fourLayerCombined, Finset.mem_inter, Finset.mem_union]
  have haSub := (Finset.mem_powersetCard.mp P.1.2).1
  have hcSub := (Finset.mem_powersetCard.mp P.2.1.2).1
  have hdSub := (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hrSub := (Finset.mem_powersetCard.mp P.2.2.2.2).1
  constructor
  · rintro ⟨((ha | hc) | hd) | hr, hxA⟩
    · exact ha
    · exact (Finset.disjoint_left.mp hAC hxA (hcSub hc)).elim
    · exact (Finset.disjoint_left.mp hAD hxA (hdSub hd)).elim
    · exact (Finset.disjoint_left.mp hAR hxA (hrSub hr)).elim
  · intro ha
    exact ⟨Or.inl (Or.inl (Or.inl ha)), haSub ha⟩

theorem fourLayerCombined_inter_second
    {α : Type*} [DecidableEq α]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAC : Disjoint A C) (hCD : Disjoint C D) (hCR : Disjoint C R)
    (P : FourLayerChoices A C D R i j k l) :
    fourLayerCombined P ∩ C = P.2.1.1 := by
  ext x
  simp only [fourLayerCombined, Finset.mem_inter, Finset.mem_union]
  have haSub := (Finset.mem_powersetCard.mp P.1.2).1
  have hcSub := (Finset.mem_powersetCard.mp P.2.1.2).1
  have hdSub := (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hrSub := (Finset.mem_powersetCard.mp P.2.2.2.2).1
  constructor
  · rintro ⟨((ha | hc) | hd) | hr, hxC⟩
    · exact (Finset.disjoint_left.mp hAC (haSub ha) hxC).elim
    · exact hc
    · exact (Finset.disjoint_left.mp hCD hxC (hdSub hd)).elim
    · exact (Finset.disjoint_left.mp hCR hxC (hrSub hr)).elim
  · intro hc
    exact ⟨Or.inl (Or.inl (Or.inr hc)), hcSub hc⟩

theorem fourLayerCombined_inter_third
    {α : Type*} [DecidableEq α]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAD : Disjoint A D) (hCD : Disjoint C D) (hDR : Disjoint D R)
    (P : FourLayerChoices A C D R i j k l) :
    fourLayerCombined P ∩ D = P.2.2.1.1 := by
  ext x
  simp only [fourLayerCombined, Finset.mem_inter, Finset.mem_union]
  have haSub := (Finset.mem_powersetCard.mp P.1.2).1
  have hcSub := (Finset.mem_powersetCard.mp P.2.1.2).1
  have hdSub := (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hrSub := (Finset.mem_powersetCard.mp P.2.2.2.2).1
  constructor
  · rintro ⟨((ha | hc) | hd) | hr, hxD⟩
    · exact (Finset.disjoint_left.mp hAD (haSub ha) hxD).elim
    · exact (Finset.disjoint_left.mp hCD (hcSub hc) hxD).elim
    · exact hd
    · exact (Finset.disjoint_left.mp hDR hxD (hrSub hr)).elim
  · intro hd
    exact ⟨Or.inl (Or.inr hd), hdSub hd⟩

theorem fourLayerCombined_inter_fourth
    {α : Type*} [DecidableEq α]
    {A C D R : Finset α} {i j k l : ℕ}
    (hAR : Disjoint A R) (hCR : Disjoint C R) (hDR : Disjoint D R)
    (P : FourLayerChoices A C D R i j k l) :
    fourLayerCombined P ∩ R = P.2.2.2.1 := by
  ext x
  simp only [fourLayerCombined, Finset.mem_inter, Finset.mem_union]
  have haSub := (Finset.mem_powersetCard.mp P.1.2).1
  have hcSub := (Finset.mem_powersetCard.mp P.2.1.2).1
  have hdSub := (Finset.mem_powersetCard.mp P.2.2.1.2).1
  have hrSub := (Finset.mem_powersetCard.mp P.2.2.2.2).1
  constructor
  · rintro ⟨((ha | hc) | hd) | hr, hxR⟩
    · exact (Finset.disjoint_left.mp hAR (haSub ha) hxR).elim
    · exact (Finset.disjoint_left.mp hCR (hcSub hc) hxR).elim
    · exact (Finset.disjoint_left.mp hDR (hdSub hd) hxR).elim
    · exact hr
  · intro hr
    exact ⟨Or.inr hr, hrSub hr⟩

/-- A finite collection of four-block layer profiles that share one total
cardinality and one cyclic-kernel coset may be counted together.  The sum,
not merely each individual product, is bounded by the kernel order. -/
theorem sum_fourLayerChoices_le_addOrderOf_of_common_kernelBucket
    [Fintype G] {ι : Type*} [Fintype ι]
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (A C D R : Finset (Fin n))
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hAR : Disjoint A R)
    (hCD : Disjoint C D) (hCR : Disjoint C R) (hDR : Disjoint D R)
    (ia ic id ir : ι → ℕ)
    (hprofile : Function.Injective fun u ↦ ((ia u, ic u), (id u, ir u)))
    (total : ℕ) (htotal : ∀ u, ia u + ic u + id u + ir u = total)
    (a c d r : Fin n)
    (hAcoset : ∀ x ∈ A, g x - g a ∈ AddSubgroup.zmultiples y)
    (hCcoset : ∀ x ∈ C, g x - g c ∈ AddSubgroup.zmultiples y)
    (hDcoset : ∀ x ∈ D, g x - g d ∈ AddSubgroup.zmultiples y)
    (hRcoset : ∀ x ∈ R, g x - g r ∈ AddSubgroup.zmultiples y)
    (base : G)
    (hcorrection : ∀ u,
      ia u • g a + ic u • g c + id u • g d + ir u • g r - base ∈
        AddSubgroup.zmultiples y) :
    (∑ u : ι,
      A.card.choose (ia u) * C.card.choose (ic u) *
        D.card.choose (id u) * R.card.choose (ir u)) ≤ addOrderOf y := by
  classical
  let X := Σ u : ι, FourLayerChoices A C D R (ia u) (ic u) (id u) (ir u)
  let subset : X → Finset (Fin n) := fun P ↦ fourLayerCombined P.2
  have hsubset : Function.Injective subset := by
    rintro ⟨u, P⟩ ⟨v, Q⟩ hPQ
    dsimp only [subset] at hPQ
    have haeq : P.1.1 = Q.1.1 := by
      calc
        P.1.1 = fourLayerCombined P ∩ A :=
          (fourLayerCombined_inter_first hAC hAD hAR P).symm
        _ = fourLayerCombined Q ∩ A := by rw [hPQ]
        _ = Q.1.1 := fourLayerCombined_inter_first hAC hAD hAR Q
    have hceq : P.2.1.1 = Q.2.1.1 := by
      calc
        P.2.1.1 = fourLayerCombined P ∩ C :=
          (fourLayerCombined_inter_second hAC hCD hCR P).symm
        _ = fourLayerCombined Q ∩ C := by rw [hPQ]
        _ = Q.2.1.1 := fourLayerCombined_inter_second hAC hCD hCR Q
    have hdeq : P.2.2.1.1 = Q.2.2.1.1 := by
      calc
        P.2.2.1.1 = fourLayerCombined P ∩ D :=
          (fourLayerCombined_inter_third hAD hCD hDR P).symm
        _ = fourLayerCombined Q ∩ D := by rw [hPQ]
        _ = Q.2.2.1.1 := fourLayerCombined_inter_third hAD hCD hDR Q
    have hreq : P.2.2.2.1 = Q.2.2.2.1 := by
      calc
        P.2.2.2.1 = fourLayerCombined P ∩ R :=
          (fourLayerCombined_inter_fourth hAR hCR hDR P).symm
        _ = fourLayerCombined Q ∩ R := by rw [hPQ]
        _ = Q.2.2.2.1 := fourLayerCombined_inter_fourth hAR hCR hDR Q
    have hia : ia u = ia v := by
      rw [← (Finset.mem_powersetCard.mp P.1.2).2,
        ← (Finset.mem_powersetCard.mp Q.1.2).2, haeq]
    have hic : ic u = ic v := by
      rw [← (Finset.mem_powersetCard.mp P.2.1.2).2,
        ← (Finset.mem_powersetCard.mp Q.2.1.2).2, hceq]
    have hid : id u = id v := by
      rw [← (Finset.mem_powersetCard.mp P.2.2.1.2).2,
        ← (Finset.mem_powersetCard.mp Q.2.2.1.2).2, hdeq]
    have hir : ir u = ir v := by
      rw [← (Finset.mem_powersetCard.mp P.2.2.2.2).2,
        ← (Finset.mem_powersetCard.mp Q.2.2.2.2).2, hreq]
    have huv : u = v := hprofile (by
      apply Prod.ext
      · exact Prod.ext hia hic
      · exact Prod.ext hid hir)
    subst v
    have hp : P = Q := by
      apply Prod.ext
      · exact Subtype.ext haeq
      · apply Prod.ext
        · exact Subtype.ext hceq
        · apply Prod.ext
          · exact Subtype.ext hdeq
          · exact Subtype.ext hreq
    exact congrArg (fun W ↦ Sigma.mk u W) hp
  have hcard : ∀ P : X, (subset P).card = total := by
    rintro ⟨u, P⟩
    dsimp only [subset]
    rw [fourLayerCombined_card hAC hAD hAR hCD hCR hDR P, htotal]
  have hkernel : ∀ P : X,
      (∑ x ∈ subset P, g x) - base ∈ AddSubgroup.zmultiples y := by
    rintro ⟨u, P⟩
    have hdevA : (∑ x ∈ P.1.1, (g x - g a)) ∈
        AddSubgroup.zmultiples y :=
      AddSubgroup.sum_mem _ fun x hx ↦
        hAcoset x ((Finset.mem_powersetCard.mp P.1.2).1 hx)
    have hdevC : (∑ x ∈ P.2.1.1, (g x - g c)) ∈
        AddSubgroup.zmultiples y :=
      AddSubgroup.sum_mem _ fun x hx ↦
        hCcoset x ((Finset.mem_powersetCard.mp P.2.1.2).1 hx)
    have hdevD : (∑ x ∈ P.2.2.1.1, (g x - g d)) ∈
        AddSubgroup.zmultiples y :=
      AddSubgroup.sum_mem _ fun x hx ↦
        hDcoset x ((Finset.mem_powersetCard.mp P.2.2.1.2).1 hx)
    have hdevR : (∑ x ∈ P.2.2.2.1, (g x - g r)) ∈
        AddSubgroup.zmultiples y :=
      AddSubgroup.sum_mem _ fun x hx ↦
        hRcoset x ((Finset.mem_powersetCard.mp P.2.2.2.2).1 hx)
    have hdev :
        (((∑ x ∈ P.1.1, (g x - g a)) +
          ∑ x ∈ P.2.1.1, (g x - g c)) +
          ∑ x ∈ P.2.2.1.1, (g x - g d)) +
          ∑ x ∈ P.2.2.2.1, (g x - g r) ∈
            AddSubgroup.zmultiples y :=
      AddSubgroup.add_mem _
        (AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hdevA hdevC) hdevD)
        hdevR
    have hrewrite :
        (∑ x ∈ subset ⟨u, P⟩, g x) - base =
          ((((∑ x ∈ P.1.1, (g x - g a)) +
            ∑ x ∈ P.2.1.1, (g x - g c)) +
            ∑ x ∈ P.2.2.1.1, (g x - g d)) +
            ∑ x ∈ P.2.2.2.1, (g x - g r)) +
          (ia u • g a + ic u • g c + id u • g d + ir u • g r - base) := by
      dsimp only [subset]
      rw [fourLayerCombined_sum hAC hAD hAR hCD hCR hDR g P]
      simp_rw [Finset.sum_sub_distrib, Finset.sum_const]
      rw [(Finset.mem_powersetCard.mp P.1.2).2,
        (Finset.mem_powersetCard.mp P.2.1.2).2,
        (Finset.mem_powersetCard.mp P.2.2.1.2).2,
        (Finset.mem_powersetCard.mp P.2.2.2.2).2]
      abel
    rw [hrewrite]
    exact AddSubgroup.add_mem _ hdev (hcorrection u)
  have hbound :=
    fintype_card_le_addOrderOf_of_sameCard_kernelSubsetSums
      g hg y subset hsubset total hcard base hkernel
  dsimp only [X] at hbound
  rw [Fintype.card_sigma] at hbound
  simpa only [FourLayerChoices, Fintype.card_prod, Fintype.card_coe,
    Finset.card_powersetCard, Nat.mul_assoc] using hbound

/-- Layer profiles with the same total size and the same weighted quotient
residue have correction terms in one kernel coset. -/
theorem four_kernelCosetCorrection_sub_mem
    (H : AddSubgroup G) (z δ a c d r : G) (ka kc kd kr : ℤ)
    (ha : a - z + ka • δ ∈ H) (hc : c - z + kc • δ ∈ H)
    (hd : d - z + kd • δ ∈ H) (hr : r - z + kr • δ ∈ H)
    (ia ic id ir ja jc jd jr : ℕ)
    (htotal : ia + ic + id + ir = ja + jc + jd + jr)
    (hweight :
      (ia : ℤ) * ka + (ic : ℤ) * kc + (id : ℤ) * kd + (ir : ℤ) * kr =
        (ja : ℤ) * ka + (jc : ℤ) * kc + (jd : ℤ) * kd + (jr : ℤ) * kr) :
    ia • a + ic • c + id • d + ir • r -
        (ja • a + jc • c + jd • d + jr • r) ∈ H := by
  have hleft :
      ia • (a - z + ka • δ) + ic • (c - z + kc • δ) +
          id • (d - z + kd • δ) + ir • (r - z + kr • δ) ∈ H :=
    H.add_mem
      (H.add_mem
        (H.add_mem (H.nsmul_mem ha ia) (H.nsmul_mem hc ic))
        (H.nsmul_mem hd id))
      (H.nsmul_mem hr ir)
  have hright :
      ja • (a - z + ka • δ) + jc • (c - z + kc • δ) +
          jd • (d - z + kd • δ) + jr • (r - z + kr • δ) ∈ H :=
    H.add_mem
      (H.add_mem
        (H.add_mem (H.nsmul_mem ha ja) (H.nsmul_mem hc jc))
        (H.nsmul_mem hd jd))
      (H.nsmul_mem hr jr)
  have htotalZ :
      (ia : ℤ) + ic + id + ir = (ja : ℤ) + jc + jd + jr := by
    exact_mod_cast htotal
  have htotalG :
      ia • z + ic • z + id • z + ir • z =
        ja • z + jc • z + jd • z + jr • z := by
    have hz := congrArg (fun k : ℤ => k • z) htotalZ
    simpa only [add_smul, natCast_zsmul] using hz
  have hweightG :
      ia • (ka • δ) + ic • (kc • δ) + id • (kd • δ) + ir • (kr • δ) =
        ja • (ka • δ) + jc • (kc • δ) + jd • (kd • δ) + jr • (kr • δ) := by
    have hδ := congrArg (fun k : ℤ => k • δ) hweight
    simpa only [add_smul, mul_smul, natCast_zsmul] using hδ
  have hexpand :
      ia • a + ic • c + id • d + ir • r -
          (ja • a + jc • c + jd • d + jr • r) =
        (ia • (a - z + ka • δ) + ic • (c - z + kc • δ) +
            id • (d - z + kd • δ) + ir • (r - z + kr • δ) -
          (ja • (a - z + ka • δ) + jc • (c - z + kc • δ) +
            jd • (d - z + kd • δ) + jr • (r - z + kr • δ))) +
        ((ia • z + ic • z + id • z + ir • z) -
          (ja • z + jc • z + jd • z + jr • z)) -
        ((ia • (ka • δ) + ic • (kc • δ) + id • (kd • δ) + ir • (kr • δ)) -
          (ja • (ka • δ) + jc • (kc • δ) + jd • (kd • δ) + jr • (kr • δ))) := by
    module
  rw [hexpand, htotalG, hweightG]
  simpa using H.sub_mem hleft hright

end MinModulus
