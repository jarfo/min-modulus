/-
# Elimination of the five-owner Mersenne external profile

The exact Mersenne endpoint has `17 <= d <= 57` and three possible external
profiles `(5,0)`, `(4,1)`, and `(3,2)`.  Its full layer capacity is already
strong enough to remove the first profile: the middle leaf layer times the
middle layer of five points has size

  `10 * choose d (d/2) > 2^d - 1`

throughout that dimension range.  The same comparison with factor six shows
that either remaining mixed profile requires `d >= 23`.

The final theorem performs this reduction without losing the concrete
secondary/final fibers, their layer and critical capacities, the injective
target capacity, or the selected-incidence charge.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneExternalIncidenceCharge

namespace MinModulus

open Finset

/-- Ten middle-layer copies exceed the Mersenne group throughout the locked
dimension range. -/
theorem mersenne_lt_ten_mul_middle_choose_of_seventeen_le_of_le_fiftySeven
    (d : ℕ) (h17 : 17 ≤ d) (h57 : d ≤ 57) :
    2 ^ d - 1 < d.choose (d / 2) * 10 := by
  interval_cases d <;> norm_num [Nat.choose]

/-- Six middle-layer copies already exceed the Mersenne group below
dimension twenty-three. -/
theorem mersenne_lt_six_mul_middle_choose_of_seventeen_le_of_le_twentyTwo
    (d : ℕ) (h17 : 17 ≤ d) (h22 : d ≤ 22) :
    2 ^ d - 1 < d.choose (d / 2) * 6 := by
  interval_cases d <;> norm_num [Nat.choose]

/-- Exact layer capacity eliminates `(5,0)` and forces `d >= 23` in either
remaining external profile. -/
theorem exactMersenne_externalProfiles_four_or_three
    {α : Type*} (d q : ℕ) (T F : Finset α)
    (h17 : 17 ≤ d) (h57 : d ≤ 57) (hq : q = 2 ^ d - 1)
    (hprofiles :
      (T.card = 5 ∧ F.card = 0) ∨
        (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2))
    (hcap : ∀ i j k : ℕ,
      d.choose i * T.card.choose j * F.card.choose k ≤ q) :
    23 ≤ d ∧
      ((T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2)) := by
  have hnotFive : ¬ (T.card = 5 ∧ F.card = 0) := by
    rintro ⟨hTfive, hFzero⟩
    have hmiddle := hcap (d / 2) 2 0
    rw [hTfive, hFzero, hq] at hmiddle
    norm_num [Nat.choose] at hmiddle
    have hstrict :=
      mersenne_lt_ten_mul_middle_choose_of_seventeen_le_of_le_fiftySeven
        d h17 h57
    omega
  have hmixed :
      (T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2) := hprofiles.resolve_left hnotFive
  refine ⟨?_, hmixed⟩
  by_contra hnot
  have h22 : d ≤ 22 := by omega
  have hstrict :=
    mersenne_lt_six_mul_middle_choose_of_seventeen_le_of_le_twentyTwo
      d h17 h22
  rcases hmixed with hfour | hthree
  · have hmiddle := hcap (d / 2) 2 0
    rw [hfour.1, hfour.2, hq] at hmiddle
    norm_num [Nat.choose] at hmiddle
    omega
  · have hmiddle := hcap (d / 2) 1 1
    rw [hthree.1, hthree.2, hq] at hmiddle
    norm_num [Nat.choose] at hmiddle
    omega

variable {G : Type*} [AddCommGroup G]

/-- Named selected-incidence alternative used by the reduced-profile
endpoint. -/
def MersenneExternalSelectedIncidenceAlternative
    {n d : ℕ} (g : Fin n → G) (y v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d) (r : Fin n)
    (z : Fin d) (T : Finset (Fin n)) : Prop :=
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  let E := deletedOwnerSubfiber B T
  2 * E.card =
      2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).image leaf,
        (adjacentHeavyOwnersAt g y v B p leaf E i).card ∨
    2 * E.card ≤
      2 * (ownersSatisfying E (fun b ↦
        AntipodalRepairRootCommonOmission g (p.scalar b • y) r)).card +
      2 * ∑ i ∈ (Finset.univ : Finset (Fin d)).erase z,
        (primaryOmissionOwnersAt g y B p f z r E i).card + 2 +
      ∑ b ∈ ownersSatisfying E (fun b ↦
        AntipodalRepairResidualMatrix g y B p f z r v b),
          antipodalRepairResidualIncidenceMass g y B p f z r v b

/-- Lossless reduced-profile endpoint.  Only `(4,1)` and `(3,2)` survive,
`d >= 23`, and all capacity and selected-incidence information remains on the
same concrete secondary/final fibers. -/
theorem PrimitiveMiddleExactMersenneFiveExternalRows.mixedExternalProfile_endpoint
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (h17 : 17 ≤ d) (h57 : d ≤ 57)
    (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (L : Finset (Fin n))
    (hL : L = (Finset.univ : Finset (Fin d)).image leaf)
    (hfive : PrimitiveMiddleExactMersenneFiveExternalRows g y B L p k₀) :
    ∃ T F : Finset (Fin n),
      23 ≤ d ∧ T ⊆ B \ L ∧ B \ L = T ∪ F ∧ Disjoint T F ∧
      ((T.card = 4 ∧ F.card = 1) ∨
        (T.card = 3 ∧ F.card = 2)) ∧
      (∀ i j k : ℕ,
        d.choose i * T.card.choose j * F.card.choose k ≤ q) ∧
      48 * (d.choose (d / 2) * F.card.choose (F.card / 2)) <
        2 ^ B.card ∧
      T.card ≤ addOrderOf y - 1 ∧
      MersenneExternalSelectedIncidenceAlternative
        g y v B p leaf e r ⟨0, by omega⟩ T := by
  rcases hfive with
    ⟨T, k, _t, F, hTcard, _hTle, _hFle, hTsub, _htT,
      _hkMem, _hkNe, hparameter, hrows, _hTexact, _hTadjacent,
      _hTcomplete, _hTseparated, hpartition, hdisjoint,
      _hcard, hprofiles, _hFcase, hcap, hcritical⟩
  have horderY : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  have horderVY : addOrderOf v = addOrderOf y := by
    have hcards := congrArg
      (fun H : AddSubgroup (ZMod (2 ^ 6 * q)) ↦ Nat.card H) hcyclic
    simpa only [Nat.card_zmultiples] using hcards
  have hq : q = 2 ^ d - 1 := by omega
  have hd : 3 ≤ d := by omega
  have hLcard : L.card = d := by
    rw [hL, Finset.card_image_of_injective _ hleaf, Finset.card_univ,
      Fintype.card_fin]
  have hcapD : ∀ i j k : ℕ,
      d.choose i * T.card.choose j * F.card.choose k ≤ q := by
    simpa only [hLcard] using hcap
  have hcriticalD :
      48 * (d.choose (d / 2) * F.card.choose (F.card / 2)) <
        2 ^ B.card := by
    simpa only [hLcard] using hcritical
  have hprofile := exactMersenne_externalProfiles_four_or_three
    d q T F h17 h57 hq hprofiles hcapD
  let E := deletedOwnerSubfiber B T
  have hTsubB : T ⊆ B := fun i hi ↦ (Finset.mem_sdiff.mp (hTsub hi)).1
  have hEcard : E.card = T.card := by
    simpa only [E] using card_deletedOwnerSubfiber B T hTsubB
  have howner : ∀ b, b ∈ E → p.coeff b (b : Fin n) = -1 := by
    intro b hbE
    have hbT := (mem_deletedOwnerSubfiber_iff B T b).mp
      (by simpa only [E] using hbE)
    have hbOutside : (b : Fin n) ∉
        (Finset.univ : Finset (Fin d)).image leaf := by
      simpa only [← hL] using (Finset.mem_sdiff.mp (hTsub hbT)).2
    exact p.external_owner_eq_neg_one_of_mersenneLeaf
      g hg y root v B hd hv leaf hleaf e hnormal
        hcyclic b hbOutside k (hrows b hbT).1 (hrows b hbT).2.1
  have hweight : ∀ b, b ∈ E → p.weight b = 2 * k := by
    intro b hbE
    exact (hrows b ((mem_deletedOwnerSubfiber_iff B T b).mp
      (by simpa only [E] using hbE))).2.1
  have hEcapacity : E.card ≤ addOrderOf y - 1 :=
    p.card_fixedWeight_negOne_le_order_sub_one
      g hg y B E k howner hweight
  have hweighted := completeExternalFiber_selectedIncidenceCharge
    g hg y root v B p hyq hfullOdd hprimitive hd hv
      leaf hleaf e hnormal hcyclic r hrzero hdeleted hleafMem k₀ k
        hmiddle hprimaryWeight T (by simpa only [← hL] using hTsub) hr
          hparameter (fun b hbT ↦ ⟨(hrows b hbT).1, (hrows b hbT).2.1⟩)
  have hweighted' : MersenneExternalSelectedIncidenceAlternative
      g y v B p leaf e r ⟨0, by omega⟩ T := by
    simpa only [MersenneExternalSelectedIncidenceAlternative] using hweighted
  refine ⟨T, F, hprofile.1, hTsub, hpartition, hdisjoint, hprofile.2,
    hcapD, hcriticalD, ?_, hweighted'⟩
  omega

end MinModulus
