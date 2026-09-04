import MinModulus.G1OddPrimaryFullCycleQuotientRejoin
import MinModulus.G1OddPrimaryFullCycleExactDivisorDescent
import MinModulus.G1OddPrimaryFullCycleFifthStratumTransition

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A finite cyclic group of even order has at most one nonzero element
killed by doubling.  Naming one such element identifies every other one. -/
theorem eq_zero_or_eq_of_add_self_eq_zero_of_isAddCyclic_even_card
    {Q : Type*} [AddCommGroup Q] [Fintype Q] [IsAddCyclic Q]
    {N M : ℕ} [NeZero N]
    (hcard : Nat.card Q = N) (hN : N = 2 * M)
    {v u : Q} (hvne : v ≠ 0) (hv : v + v = 0) (hu : u + u = 0) :
    u = 0 ∨ u = v := by
  let equiv : Q ≃+ ZMod N :=
    (zmodAddCyclicAddEquiv (G := Q) inferInstance).symm.trans
      (ZMod.ringEquivCongr hcard).toAddEquiv
  have hvImage : equiv v + equiv v = 0 := by
    rw [← map_add, hv, map_zero]
  have huImage : equiv u + equiv u = 0 := by
    rw [← map_add, hu, map_zero]
  have hvHalf : equiv v = (M : ZMod N) := by
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN (equiv v) hvImage with
      hvZero | hvHalf
    · exact (hvne (equiv.injective (hvZero.trans (map_zero equiv).symm))).elim
    · exact hvHalf
  rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN (equiv u) huImage with
    huZero | huHalf
  · exact Or.inl (equiv.injective (huZero.trans (map_zero equiv).symm))
  · right
    apply equiv.injective
    exact huHalf.trans hvHalf.symm

/-- In a cyclic group of order `2^t`, an element of order `2^(t-1)` contains
the unique nonzero involution once `t ≥ 2`. -/
theorem eq_zero_or_quarter_nsmul_of_add_self_eq_zero_of_twoPower_card
    {Q : Type*} [AddCommGroup Q] [Fintype Q] [IsAddCyclic Q]
    (t : ℕ) (ht : 2 ≤ t) (hcard : Nat.card Q = 2 ^ t)
    (delta u : Q) (hdelta : addOrderOf delta = 2 ^ (t - 1))
    (hu : u + u = 0) :
    u = 0 ∨ u = (2 ^ (t - 2) : ℕ) • delta := by
  let v : Q := (2 ^ (t - 2) : ℕ) • delta
  have hquarterLt : 2 ^ (t - 2) < 2 ^ (t - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hvne : v ≠ 0 := by
    intro hvZero
    have hdvd : addOrderOf delta ∣ 2 ^ (t - 2) :=
      addOrderOf_dvd_of_nsmul_eq_zero hvZero
    rw [hdelta] at hdvd
    exact (Nat.not_le_of_gt hquarterLt
      (Nat.le_of_dvd (pow_pos (by omega) _) hdvd)).elim
  have hhalfEq : 2 * 2 ^ (t - 2) = 2 ^ (t - 1) := by
    calc
      2 * 2 ^ (t - 2) = 2 ^ (t - 2) * 2 := Nat.mul_comm _ _
      _ = 2 ^ (t - 2 + 1) := (pow_succ 2 (t - 2)).symm
      _ = 2 ^ (t - 1) := by congr 1; omega
  have hdeltaZero : (2 ^ (t - 1) : ℕ) • delta = 0 := by
    rw [← hdelta]
    exact addOrderOf_nsmul_eq_zero delta
  have hv : v + v = 0 := by
    calc
      v + v = (2 * 2 ^ (t - 2) : ℕ) • delta := by
        dsimp only [v]
        module
      _ = (2 ^ (t - 1) : ℕ) • delta := by rw [hhalfEq]
      _ = 0 := hdeltaZero
  have hpowEq : 2 ^ t = 2 * 2 ^ (t - 1) := by
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := pow_succ 2 (t - 1)
      _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
  exact eq_zero_or_eq_of_add_self_eq_zero_of_isAddCyclic_even_card
    hcard hpowEq hvne hv hu

/-- A full-order retained difference in the `2^t` quotient rules out the
unique odd normalized row weight, uniformly in the positive stratum. -/
theorem TwoRetainedFiveWeightPresentation.weight_ne_neg_one_of_fullOrder
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 2 ^ t) :
    ∀ b : ↥B, p.weight b ≠ -1 := by
  classical
  intro b hb
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  have hquotientModulus : (2 ^ t * q) / addOrderOf y = 2 ^ t := by
    rw [Nat.mul_div_assoc (2 ^ t) hyq, hfullOdd]
    simp
  have hQcardNat : Nat.card Q = 2 ^ t := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ t * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ t * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hQcard : Fintype.card Q = 2 ^ t := by
    simpa only [Nat.card_eq_fintype_card] using hQcardNat
  have hquotientRelation :
      (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (b : Fin n) - g p.z) +
        p.weight b • (g p.x - g p.z))).mpr
    exact p.row_mem b
  have hdeltaDouble : deltaQ = (2 : ℕ) • betaQ := by
    rw [hb] at hquotientRelation
    change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
    have hrelation' : betaQ + betaQ - deltaQ = 0 := by
      simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
        hquotientRelation
    calc
      deltaQ = (betaQ + betaQ - deltaQ) + deltaQ := by
        rw [hrelation', zero_add]
      _ = betaQ + betaQ := by abel
      _ = (2 : ℕ) • betaQ := (two_nsmul betaQ).symm
  have hcardBeta : (2 ^ t : ℕ) • betaQ = 0 := by
    have hcardBeta' : Fintype.card Q • betaQ = 0 :=
      card_nsmul_eq_zero
    simpa only [hQcard] using hcardBeta'
  have hpowEq : 2 ^ t = 2 ^ (t - 1) * 2 := by
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := pow_succ 2 (t - 1)
  have hhalfDelta : (2 ^ (t - 1) : ℕ) • deltaQ = 0 := by
    rw [hdeltaDouble]
    calc
      (2 ^ (t - 1) : ℕ) • ((2 : ℕ) • betaQ) =
          (2 ^ t : ℕ) • betaQ := by
        calc
          (2 ^ (t - 1) : ℕ) • ((2 : ℕ) • betaQ) =
              (2 * 2 ^ (t - 1) : ℕ) • betaQ :=
            (mul_nsmul betaQ 2 (2 ^ (t - 1))).symm
          _ = (2 ^ t : ℕ) • betaQ := by
            apply congrArg (fun k : ℕ ↦ k • betaQ)
            exact (Nat.mul_comm _ _).trans hpowEq.symm
      _ = 0 := hcardBeta
  have hdvd : addOrderOf deltaQ ∣ 2 ^ (t - 1) :=
    addOrderOf_dvd_of_nsmul_eq_zero hhalfDelta
  have horderQ : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using hprimitive
  rw [horderQ] at hdvd
  have hlt : 2 ^ (t - 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  exact (Nat.not_le_of_gt hlt
    (Nat.le_of_dvd (pow_pos (by omega) _) hdvd)).elim

/-- In a minimal `2^t`-stratum modulus with `t ≥ 2`, an index-two retained
difference forces the odd normalized row weight in the same presentation. -/
theorem TwoRetainedFiveWeightPresentation.exists_weight_eq_neg_one_of_halfOrder
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    (hindex :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 2 ^ (t - 1)) :
    ∃ b : ↥B, p.weight b = -1 := by
  classical
  by_contra hnoHeavy
  push Not at hnoHeavy
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ t * q) := g p.x - g p.z
  let deltaQ : Q := pi delta
  let K : AddSubgroup (ZMod (2 ^ t * q)) :=
    H ⊔ AddSubgroup.zmultiples delta
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
    (QuotientAddGroup.mk'_surjective H)
  have hquotientModulus : (2 ^ t * q) / addOrderOf y = 2 ^ t := by
    rw [Nat.mul_div_assoc (2 ^ t) hyq, hfullOdd]
    simp
  have hQcardNat : Nat.card Q = 2 ^ t := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ t * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ t * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hdeltaOrder : addOrderOf deltaQ = 2 ^ (t - 1) := by
    simpa only [deltaQ, delta, pi, H, Q] using hindex
  have hdeletedQuotient : ∀ b : ↥B,
      pi (g (b : Fin n) - g p.z) ∈ AddSubgroup.zmultiples deltaQ := by
    intro b
    obtain ⟨k, hk⟩ :=
      twoRetainedNormalizedWeight_eq_two_mul_of_ne_neg_one
        (p.weight_mem b) (hnoHeavy b)
    let betaQ : Q := pi (g (b : Fin n) - g p.z)
    let uQ : Q := betaQ + k • deltaQ
    have hquotientRelation :
        (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff
        ((2 : ℤ) • (g (b : Fin n) - g p.z) +
          p.weight b • (g p.x - g p.z))).mpr
      exact p.row_mem b
    have huDouble : uQ + uQ = 0 := by
      calc
        uQ + uQ = (2 : ℤ) • betaQ + p.weight b • deltaQ := by
          rw [hk]
          dsimp only [uQ]
          module
        _ = 0 := hquotientRelation
    have huCases : uQ = 0 ∨ uQ = (2 ^ (t - 2) : ℕ) • deltaQ :=
      eq_zero_or_quarter_nsmul_of_add_self_eq_zero_of_twoPower_card
        t ht hQcardNat deltaQ uQ hdeltaOrder huDouble
    have huMem : uQ ∈ AddSubgroup.zmultiples deltaQ := by
      rcases huCases with hzero | hu
      · rw [hzero]
        exact AddSubgroup.zero_mem _
      · rw [hu]
        exact AddSubgroup.nsmul_mem _
          (AddSubgroup.mem_zmultiples deltaQ) (2 ^ (t - 2))
    have hkMem : k • deltaQ ∈ AddSubgroup.zmultiples deltaQ :=
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples deltaQ) k
    have hbetaEq : betaQ = uQ - k • deltaQ := by
      simp only [uQ]
      module
    change betaQ ∈ AddSubgroup.zmultiples deltaQ
    rw [hbetaEq]
    exact AddSubgroup.sub_mem _ huMem hkMem
  have hquotientMem_lift : ∀ v : ZMod (2 ^ t * q),
      pi v ∈ AddSubgroup.zmultiples deltaQ → v ∈ K := by
    intro v hv
    obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    have hdiffH : v - c • delta ∈ H := by
      apply (QuotientAddGroup.eq_zero_iff (v - c • delta)).mp
      change pi (v - c • delta) = 0
      rw [map_sub, map_zsmul]
      change pi v - c • deltaQ = 0
      rw [← hc]
      simp
    apply AddSubgroup.mem_sup.mpr
    refine ⟨v - c • delta, hdiffH, c • delta, ?_, ?_⟩
    · exact AddSubgroup.zsmul_mem _
        (AddSubgroup.mem_zmultiples delta) c
    · module
  have hcoordinate : ∀ i, g i - g p.z ∈ K := by
    intro i
    by_cases hiB : i ∈ B
    · exact hquotientMem_lift (g i - g p.z)
        (hdeletedQuotient ⟨i, hiB⟩)
    · have hiComplement : i ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩
      rw [p.complement_eq] at hiComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiComplement
      rcases hiComplement with hix | hiz
      · subst i
        exact AddSubgroup.mem_sup_right
          (AddSubgroup.mem_zmultiples delta)
      · subst i
        simp
  let gK : Fin n → K := fun i ↦ ⟨g i - g p.z, hcoordinate i⟩
  have hgK : ValidTuple gK := by
    apply validTuple_of_comp K.subtype
    simpa only [gK, AddSubgroup.coe_subtype] using
      validTuple_sub_const g hg (g p.z)
  let e : ℤ := addOrderOf deltaQ
  have he : e ≠ 0 := by
    change (addOrderOf deltaQ : ℤ) ≠ 0
    exact_mod_cast (Nat.ne_of_gt (addOrderOf_pos deltaQ))
  have heMem : e • delta ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff (e • delta)).mp
    change pi (e • delta) = 0
    rw [map_zsmul]
    change (addOrderOf deltaQ : ℤ) • deltaQ = 0
    simpa only [natCast_zsmul] using addOrderOf_nsmul_eq_zero deltaQ
  have hKcard : Nat.card K ≤ 2 ^ (t - 1) * addOrderOf y := by
    have hbound := card_sup_zmultiples_le_natAbs_mul H delta e he heMem
    have henatAbs : e.natAbs = 2 ^ (t - 1) := by
      simp [e, hdeltaOrder]
    rw [henatAbs] at hbound
    simpa only [K, H, Nat.card_zmultiples] using hbound
  have hqpos : 0 < q := by
    have hNpos : 0 < 2 ^ t * q := NeZero.pos (2 ^ t * q)
    exact Nat.pos_of_mul_pos_left hNpos
  have hyLe : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hyq
  have hhalfLt : 2 ^ (t - 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hKlt : Nat.card K < 2 ^ t * q := by
    calc
      Nat.card K ≤ 2 ^ (t - 1) * addOrderOf y := hKcard
      _ ≤ 2 ^ (t - 1) * q := Nat.mul_le_mul_left _ hyLe
      _ < 2 ^ t * q := Nat.mul_lt_mul_of_pos_right hhalfLt hqpos
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKdiv : Nat.card K ∣ 2 ^ t * q := by
    have hdiv : Nat.card K ∣ Nat.card (ZMod (2 ^ t * q)) :=
      AddSubgroup.card_addSubgroup_dvd_card K
    simpa only [Nat.card_zmod] using hdiv
  letI : IsAddCyclic K := AddSubgroup.isAddCyclic K
  let equiv : K ≃+ ZMod (Nat.card K) :=
    (zmodAddCyclicAddEquiv (G := K) inferInstance).symm
  have hAdmits : AdmitsValidTuple n (Nat.card K) := by
    refine ⟨fun i ↦ equiv (gK i), ?_⟩
    exact validTuple_comp hgK equiv.toAddMonoidHom equiv.injective
  exact (hminimal (Nat.card K) hKpos hKlt hKdiv hAdmits).elim

/-- Uniform quotient phase for one fixed row presentation.  At every stratum
`t ≥ 2`, the index-two branch exposes an odd row while the full-order branch
makes all rows even. -/
theorem TwoRetainedFiveWeightPresentation.positiveStratum_phase
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    (addOrderOf (pi (g p.x - g p.z)) = 2 ^ (t - 1) ∧
        ∃ b : ↥B, p.weight b = -1) ∨
      (addOrderOf (pi (g p.x - g p.z)) = 2 ^ t ∧
        ∀ b : ↥B, p.weight b ≠ -1) := by
  have horder :=
    hrows.retainedDifference_quotientOrder_eq_half_or_full_of_positiveStratum_minimal
      (t := t) (q := q) (by omega) g hg hunique hne y hyq hfullOdd B
        hminimal p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases horder with hindex | hprimitive
  · exact Or.inl ⟨hindex,
      p.exists_weight_eq_neg_one_of_halfOrder ht g hg y hyq hfullOdd B
        hminimal hindex⟩
  · exact Or.inr ⟨hprimitive,
      p.weight_ne_neg_one_of_fullOrder (by omega) g y B hyq hfullOdd
        hprimitive⟩

/-- A half of an element of order `2^(t-1)` in a group of order `2^t` has
full order, once the half-order subgroup has a nontrivial involution. -/
theorem addOrderOf_eq_full_twoPower_of_two_nsmul_eq_halfOrder
    {Q : Type*} [AddCommGroup Q] [Fintype Q]
    (t : ℕ) (ht : 2 ≤ t) (hcard : Nat.card Q = 2 ^ t)
    (delta beta : Q) (hdelta : addOrderOf delta = 2 ^ (t - 1))
    (hdouble : (2 : ℕ) • beta = delta) :
    addOrderOf beta = 2 ^ t := by
  have hhalfDvd : 2 ^ (t - 1) ∣ addOrderOf beta := by
    rw [← hdelta, ← hdouble]
    exact addOrderOf_smul_dvd 2
  have horderDvd : addOrderOf beta ∣ 2 ^ t := by
    rw [← hcard]
    simpa only [Nat.card_eq_fintype_card] using
      (addOrderOf_dvd_card (x := beta))
  have horderLe : addOrderOf beta ≤ 2 ^ t :=
    Nat.le_of_dvd (pow_pos (by omega) _) horderDvd
  obtain ⟨k, hk⟩ := hhalfDvd
  have hhalfPos : 0 < 2 ^ (t - 1) := pow_pos (by omega) _
  have hfullEq : 2 ^ t = 2 ^ (t - 1) * 2 := by
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := pow_succ 2 (t - 1)
  have hkPos : 0 < k :=
    Nat.pos_of_mul_pos_left (hk ▸ addOrderOf_pos beta)
  have hkLe : k ≤ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (t - 1))
    · rw [← hk]
      exact horderLe.trans_eq hfullEq
    · exact hhalfPos
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with hkOne | hkTwo
  · subst k
    simp only [Nat.mul_one] at hk
    have hbetaZero : (2 ^ (t - 1) : ℕ) • beta = 0 := by
      simpa only [hk] using addOrderOf_nsmul_eq_zero beta
    have hquarterEq : 2 * 2 ^ (t - 2) = 2 ^ (t - 1) := by
      calc
        2 * 2 ^ (t - 2) = 2 ^ (t - 2) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (t - 2 + 1) := (pow_succ 2 (t - 2)).symm
        _ = 2 ^ (t - 1) := by congr 1; omega
    have hquarterDelta : (2 ^ (t - 2) : ℕ) • delta = 0 := by
      rw [← hdouble]
      calc
        (2 ^ (t - 2) : ℕ) • ((2 : ℕ) • beta) =
            (2 * 2 ^ (t - 2) : ℕ) • beta :=
          (mul_nsmul beta 2 (2 ^ (t - 2))).symm
        _ = (2 ^ (t - 1) : ℕ) • beta := by
          apply congrArg (fun j : ℕ ↦ j • beta)
          exact hquarterEq
        _ = 0 := hbetaZero
    have hdvd : addOrderOf delta ∣ 2 ^ (t - 2) :=
      addOrderOf_dvd_of_nsmul_eq_zero hquarterDelta
    rw [hdelta] at hdvd
    have hquarterLt : 2 ^ (t - 2) < 2 ^ (t - 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    exact (Nat.not_le_of_gt hquarterLt
      (Nat.le_of_dvd (pow_pos (by omega) _) hdvd)).elim
  · subst k
    exact hk.trans hfullEq.symm

/-- A primitive element of a cyclic group of order `2^t` names its unique
nonzero involution as `2^(t-1)` times that element. -/
theorem eq_zero_or_half_nsmul_of_add_self_eq_zero_of_twoPower_card
    {Q : Type*} [AddCommGroup Q] [Fintype Q] [IsAddCyclic Q]
    (t : ℕ) (ht : 1 ≤ t) (hcard : Nat.card Q = 2 ^ t)
    (delta u : Q) (hdelta : addOrderOf delta = 2 ^ t)
    (hu : u + u = 0) :
    u = 0 ∨ u = (2 ^ (t - 1) : ℕ) • delta := by
  let v : Q := (2 ^ (t - 1) : ℕ) • delta
  have hhalfLt : 2 ^ (t - 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hvne : v ≠ 0 := by
    intro hvZero
    have hdvd : addOrderOf delta ∣ 2 ^ (t - 1) :=
      addOrderOf_dvd_of_nsmul_eq_zero hvZero
    rw [hdelta] at hdvd
    exact (Nat.not_le_of_gt hhalfLt
      (Nat.le_of_dvd (pow_pos (by omega) _) hdvd)).elim
  have hfullEq : 2 * 2 ^ (t - 1) = 2 ^ t := by
    calc
      2 * 2 ^ (t - 1) = 2 ^ (t - 1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ (t - 1 + 1) := (pow_succ 2 (t - 1)).symm
      _ = 2 ^ t := by congr 1; omega
  have hdeltaZero : (2 ^ t : ℕ) • delta = 0 := by
    rw [← hdelta]
    exact addOrderOf_nsmul_eq_zero delta
  have hv : v + v = 0 := by
    calc
      v + v = (2 * 2 ^ (t - 1) : ℕ) • delta := by
        dsimp only [v]
        module
      _ = (2 ^ t : ℕ) • delta := by
        apply congrArg (fun j : ℕ ↦ j • delta)
        exact hfullEq
      _ = 0 := hdeltaZero
  have hcardEq : 2 ^ t = 2 * 2 ^ (t - 1) := hfullEq.symm
  exact eq_zero_or_eq_of_add_self_eq_zero_of_isAddCyclic_even_card
    hcard hcardEq hvne hv hu

/-- Exact solution of every quotient row for one fixed presentation,
uniformly over all strata `t ≥ 2`. -/
theorem TwoRetainedFiveWeightPresentation.positiveStratum_quotientRowNormalForm
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (addOrderOf deltaQ = 2 ^ (t - 1) ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) ∨
      (addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)) := by
  classical
  have hphase := p.positiveStratum_phase
    ht g hg hunique hne y hyq hfullOdd B hrows hminimal
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
    (QuotientAddGroup.mk'_surjective H)
  have hquotientModulus : (2 ^ t * q) / addOrderOf y = 2 ^ t := by
    rw [Nat.mul_div_assoc (2 ^ t) hyq, hfullOdd]
    simp
  have hQcardNat : Nat.card Q = 2 ^ t := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ t * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ t * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  change
    (addOrderOf deltaQ = 2 ^ (t - 1) ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) ∨
      (addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ))
  rcases hphase with ⟨hindex, b, hb⟩ | ⟨hprimitive, hallEven⟩
  · left
    refine ⟨hindex, b, hb, ?_⟩
    let betaQ : Q := pi (g (b : Fin n) - g p.z)
    have hquotientRelation :
        (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff
        ((2 : ℤ) • (g (b : Fin n) - g p.z) +
          p.weight b • (g p.x - g p.z))).mpr
      exact p.row_mem b
    have hdouble : (2 : ℕ) • betaQ = deltaQ := by
      rw [hb] at hquotientRelation
      change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
      have hrelation' : betaQ + betaQ - deltaQ = 0 := by
        simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
          hquotientRelation
      calc
        (2 : ℕ) • betaQ = betaQ + betaQ := two_nsmul betaQ
        _ = (betaQ + betaQ - deltaQ) + deltaQ := by abel
        _ = deltaQ := by rw [hrelation', zero_add]
    have hdeltaOrder : addOrderOf deltaQ = 2 ^ (t - 1) := by
      simpa only [deltaQ, pi, H, Q] using hindex
    simpa only [betaQ, pi, H, Q] using
      addOrderOf_eq_full_twoPower_of_two_nsmul_eq_halfOrder
        t ht hQcardNat deltaQ betaQ hdeltaOrder hdouble
  · right
    refine ⟨hprimitive, ?_⟩
    intro b
    obtain ⟨k, hk⟩ :=
      twoRetainedNormalizedWeight_eq_two_mul_of_ne_neg_one
        (p.weight_mem b) (hallEven b)
    refine ⟨k, hk, ?_⟩
    let betaQ : Q := pi (g (b : Fin n) - g p.z)
    let uQ : Q := betaQ + k • deltaQ
    have hquotientRelation :
        (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff
        ((2 : ℤ) • (g (b : Fin n) - g p.z) +
          p.weight b • (g p.x - g p.z))).mpr
      exact p.row_mem b
    have huDouble : uQ + uQ = 0 := by
      calc
        uQ + uQ = (2 : ℤ) • betaQ + p.weight b • deltaQ := by
          rw [hk]
          dsimp only [uQ]
          module
        _ = 0 := hquotientRelation
    have hdeltaOrder : addOrderOf deltaQ = 2 ^ t := by
      simpa only [deltaQ, pi, H, Q] using hprimitive
    rcases eq_zero_or_half_nsmul_of_add_self_eq_zero_of_twoPower_card
        t (by omega) hQcardNat deltaQ uQ hdeltaOrder huDouble with
      hzero | hhalf
    · left
      change betaQ = -(k • deltaQ)
      dsimp only [uQ] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    · right
      change betaQ = (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ
      dsimp only [uQ] at hhalf
      apply eq_sub_of_add_eq
      exact hhalf

/-- Fifth-stratum specialization of the uniform fixed-presentation phase. -/
theorem TwoRetainedFiveWeightPresentation.fifthStratum_phase
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 5 * q) →+ ZMod (2 ^ 5 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    (addOrderOf (pi (g p.x - g p.z)) = 16 ∧
        ∃ b : ↥B, p.weight b = -1) ∨
      (addOrderOf (pi (g p.x - g p.z)) = 32 ∧
        ∀ b : ↥B, p.weight b ≠ -1) := by
  simpa using p.positiveStratum_phase (t := 5) (q := q) (by omega)
    g hg hunique hne y hyq hfullOdd B hrows hminimal

/-- Fifth-stratum specialization of the uniform quotient-row normal form. -/
theorem TwoRetainedFiveWeightPresentation.fifthStratum_quotientRowNormalForm
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 5 * q) →+ ZMod (2 ^ 5 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (addOrderOf deltaQ = 16 ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 32) ∨
      (addOrderOf deltaQ = 32 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (16 : ℕ) • deltaQ - k • deltaQ)) := by
  simpa using p.positiveStratum_quotientRowNormalForm
    (t := 5) (q := q) (by omega) g hg hunique hne y hyq hfullOdd B hrows
      hminimal

/-- The critical fifth-stratum endpoint and its quotient phase on one
definitionally shared presentation. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_presentationAndPhase
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
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
    ∃ pres : TwoRetainedFiveWeightPresentation g y B,
      ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
          pres.weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
          pres.weight ⟨leaf i, hi⟩ = 0)) ∧
      (let H := AddSubgroup.zmultiples y
       let pi : ZMod (2 ^ 5 * q) →+ ZMod (2 ^ 5 * q) ⧸ H :=
         QuotientAddGroup.mk' H
       (addOrderOf (pi (g pres.x - g pres.z)) = 16 ∧
           ∃ b : ↥B, pres.weight b = -1) ∨
         (addOrderOf (pi (g pres.x - g pres.z)) = 32 ∧
           ∀ b : ↥B, pres.weight b ≠ -1)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement,
      hweight, hrowMem, hpure⟩ :=
    hrows.oneRetainedCycle_criticalFifthStratum_purePair
      hq g hg hcritical hunique hne y hyq hrTwo B hminimal leaf hleafInj
        R hcycle hRne a p i₀ hi₀ hRi₀ hleafB hdouble hspan
  let pres : TwoRetainedFiveWeightPresentation g y B :=
    ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hrowMem⟩
  refine ⟨pres, ?_, ?_⟩
  · simpa only [pres] using hpure
  · exact pres.fifthStratum_phase
      g hg hunique hne y hyq hfullOdd B hrows hminimal

/-- Lossless critical fifth-stratum rejoin.  The half-order arm supplies a
primitive odd row outside the displayed pure leaf cycle; the full-order arm
solves every owner row by the two exact quotient lifts. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_quotientRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
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
    ∃ pres : TwoRetainedFiveWeightPresentation g y B,
      ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
          pres.weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
          pres.weight ⟨leaf i, hi⟩ = 0)) ∧
      (let H := AddSubgroup.zmultiples y
       let pi : ZMod (2 ^ 5 * q) →+ ZMod (2 ^ 5 * q) ⧸ H :=
         QuotientAddGroup.mk' H
       let deltaQ := pi (g pres.x - g pres.z)
       (addOrderOf deltaQ = 16 ∧
           ∃ b : ↥B, pres.weight b = -1 ∧
             addOrderOf (pi (g (b : Fin n) - g pres.z)) = 32 ∧
             (b : Fin n) ∉ Set.range leaf) ∨
         (addOrderOf deltaQ = 32 ∧
           ∀ b : ↥B, ∃ k : ℤ, pres.weight b = 2 * k ∧
             (pi (g (b : Fin n) - g pres.z) = -(k • deltaQ) ∨
               pi (g (b : Fin n) - g pres.z) =
                 (16 : ℕ) • deltaQ - k • deltaQ))) := by
  classical
  obtain ⟨pres, hpure, _hphase⟩ :=
    hrows.oneRetainedCycle_criticalFifthStratum_presentationAndPhase
      hq g hg hcritical hunique hne y hyq hfullOdd hrTwo B hminimal leaf
        hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB hdouble hspan
  refine ⟨pres, hpure, ?_⟩
  have hnormal := pres.fifthStratum_quotientRowNormalForm
    g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with ⟨hindex, b, hb, hbprimitive⟩ |
      ⟨hprimitive, hrowsSolved⟩
  · left
    refine ⟨hindex, b, hb, hbprimitive, ?_⟩
    intro hbrange
    obtain ⟨i, hi⟩ := hbrange
    have hiB : leaf i ∈ B := by
      rw [hi]
      exact b.property
    have hsubtype : (⟨leaf i, hiB⟩ : ↥B) = b := Subtype.ext hi
    rcases hpure with ⟨_hpX, hminusTwo⟩ | ⟨_hpZ, hzero⟩
    · have hweightEq := congrArg pres.weight hsubtype
      rw [hminusTwo i hiB, hb] at hweightEq
      norm_num at hweightEq
    · have hweightEq := congrArg pres.weight hsubtype
      rw [hzero i hiB, hb] at hweightEq
      norm_num at hweightEq
  · exact Or.inr ⟨hprimitive, hrowsSolved⟩

/-- Complete quotient-row normal form at the first positive stratum.  The
half-order branch is now the explicit residual `deltaQ = 0`; in the full-order
branch the quotient has two elements and every row has the same two affine
solutions as in the uniform higher-stratum theorem. -/
theorem TwoRetainedFiveWeightPresentation.firstStratum_quotientRowNormalForm
    {q : ℕ} [NeZero (2 ^ 1 * q)]
    (g : Fin n → ZMod (2 ^ 1 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 1 * q)}
    (hunique : ∀ u : ZMod (2 ^ 1 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 1 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 1 * q → M ∣ 2 ^ 1 * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 1 * q) →+ ZMod (2 ^ 1 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (addOrderOf deltaQ = 1) ∨
      (addOrderOf deltaQ = 2 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) = deltaQ - k • deltaQ)) := by
  classical
  have horder :=
    hrows.retainedDifference_quotientOrder_eq_half_or_full_of_positiveStratum_minimal
      (t := 1) (q := q) (by omega) g hg hunique hne y hyq hfullOdd B
        hminimal p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  let H : AddSubgroup (ZMod (2 ^ 1 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 1 * q) ⧸ H
  let pi : ZMod (2 ^ 1 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
    (QuotientAddGroup.mk'_surjective H)
  have hquotientModulus : (2 ^ 1 * q) / addOrderOf y = 2 := by
    rw [Nat.mul_div_assoc (2 ^ 1) hyq, hfullOdd]
    norm_num
  have hQcardNat : Nat.card Q = 2 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 1 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 1 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  change
    (addOrderOf deltaQ = 1) ∨
      (addOrderOf deltaQ = 2 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) = deltaQ - k • deltaQ))
  rcases horder with htrivial | hprimitive
  · exact Or.inl (by simpa [deltaQ, pi, H, Q] using htrivial)
  · right
    have hprimitive' : addOrderOf deltaQ = 2 := by
      simpa [deltaQ, pi, H, Q] using hprimitive
    refine ⟨hprimitive', ?_⟩
    have hallEven : ∀ b : ↥B, p.weight b ≠ -1 :=
      p.weight_ne_neg_one_of_fullOrder (t := 1) (q := q) (by omega)
        g y B hyq hfullOdd hprimitive
    intro b
    obtain ⟨k, hk⟩ :=
      twoRetainedNormalizedWeight_eq_two_mul_of_ne_neg_one
        (p.weight_mem b) (hallEven b)
    refine ⟨k, hk, ?_⟩
    let betaQ : Q := pi (g (b : Fin n) - g p.z)
    let uQ : Q := betaQ + k • deltaQ
    have hquotientRelation :
        (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff
        ((2 : ℤ) • (g (b : Fin n) - g p.z) +
          p.weight b • (g p.x - g p.z))).mpr
      exact p.row_mem b
    have huDouble : uQ + uQ = 0 := by
      calc
        uQ + uQ = (2 : ℤ) • betaQ + p.weight b • deltaQ := by
          rw [hk]
          dsimp only [uQ]
          module
        _ = 0 := hquotientRelation
    rcases eq_zero_or_half_nsmul_of_add_self_eq_zero_of_twoPower_card
        1 (by omega) hQcardNat deltaQ uQ hprimitive' huDouble with
      hzero | hhalf
    · left
      change betaQ = -(k • deltaQ)
      dsimp only [uQ] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    · right
      change betaQ = deltaQ - k • deltaQ
      norm_num at hhalf
      dsimp only [uQ] at hhalf
      apply eq_sub_of_add_eq
      exact hhalf

/-- If the retained difference is trivial in the first-stratum quotient,
minimality forces a deleted owner into the other quotient coset.  Its
displacement from `z` therefore has the full quotient order two and supplies
the exact exchange seed missing from the raw row normal form. -/
theorem TwoRetainedFiveWeightPresentation.exists_primitiveOwner_of_firstStratum_trivialRetained
    {q : ℕ} [NeZero (2 ^ 1 * q)]
    (g : Fin n → ZMod (2 ^ 1 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 1 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 1 * q → M ∣ 2 ^ 1 * q →
        ¬ AdmitsValidTuple n M)
    (htrivial :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 1 * q) →+ ZMod (2 ^ 1 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 1) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 1 * q) →+ ZMod (2 ^ 1 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    ∃ b : ↥B, addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 := by
  classical
  let H : AddSubgroup (ZMod (2 ^ 1 * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 1 * q) ⧸ H
  let pi : ZMod (2 ^ 1 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  have hquotientModulus : (2 ^ 1 * q) / addOrderOf y = 2 := by
    rw [Nat.mul_div_assoc (2 ^ 1) hyq, hfullOdd]
    norm_num
  have hQcardNat : Nat.card Q = 2 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 1 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 1 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hdeltaOrder : addOrderOf deltaQ = 1 := by
    simpa only [deltaQ, pi, H, Q] using htrivial
  have hdeltaZero : deltaQ = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp hdeltaOrder
  have hownerNonzero : ∃ b : ↥B,
      pi (g (b : Fin n) - g p.z) ≠ 0 := by
    by_contra hnone
    have hallZero : ∀ b : ↥B,
        pi (g (b : Fin n) - g p.z) = 0 := by
      intro b
      by_contra hb
      exact hnone ⟨b, hb⟩
    have hcoordinate : ∀ i, g i - g p.z ∈ H := by
      intro i
      by_cases hiB : i ∈ B
      · apply (QuotientAddGroup.eq_zero_iff (g i - g p.z)).mp
        exact hallZero ⟨i, hiB⟩
      · have hiComplement : i ∈ Finset.univ \ B :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩
        rw [p.complement_eq] at hiComplement
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiComplement
        rcases hiComplement with hix | hiz
        · subst i
          apply (QuotientAddGroup.eq_zero_iff (g p.x - g p.z)).mp
          exact hdeltaZero
        · subst i
          simp
    let gH : Fin n → H := fun i ↦ ⟨g i - g p.z, hcoordinate i⟩
    have hgH : ValidTuple gH := by
      apply validTuple_of_comp H.subtype
      simpa only [gH, AddSubgroup.coe_subtype] using
        validTuple_sub_const g hg (g p.z)
    have hHpos : 0 < Nat.card H := Nat.card_pos
    have hqpos : 0 < q := by
      have hNpos : 0 < 2 ^ 1 * q := NeZero.pos (2 ^ 1 * q)
      exact Nat.pos_of_mul_pos_left hNpos
    have hHlt : Nat.card H < 2 ^ 1 * q := by
      calc
        Nat.card H = addOrderOf y := by
          simp only [H, Nat.card_zmultiples]
        _ ≤ q := Nat.le_of_dvd hqpos hyq
        _ < 2 ^ 1 * q := by omega
    have hHdiv : Nat.card H ∣ 2 ^ 1 * q := by
      have hdiv : Nat.card H ∣ Nat.card (ZMod (2 ^ 1 * q)) :=
        AddSubgroup.card_addSubgroup_dvd_card H
      simpa only [Nat.card_zmod] using hdiv
    letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
    let equiv : H ≃+ ZMod (Nat.card H) :=
      (zmodAddCyclicAddEquiv (G := H) inferInstance).symm
    have hAdmits : AdmitsValidTuple n (Nat.card H) := by
      refine ⟨fun i ↦ equiv (gH i), ?_⟩
      exact validTuple_comp hgH equiv.toAddMonoidHom equiv.injective
    exact (hminimal (Nat.card H) hHpos hHlt hHdiv hAdmits).elim
  obtain ⟨b, hb⟩ := hownerNonzero
  refine ⟨b, ?_⟩
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hbetaNe : betaQ ≠ 0 := by
    simpa only [betaQ] using hb
  have horderDvd : addOrderOf betaQ ∣ 2 := by
    have horderDvdCard : addOrderOf betaQ ∣ Nat.card Q := by
      simpa only [Nat.card_eq_fintype_card] using
        (addOrderOf_dvd_card (x := betaQ))
    simpa only [hQcardNat] using horderDvdCard
  have horderLe : addOrderOf betaQ ≤ 2 :=
    Nat.le_of_dvd (by omega) horderDvd
  have horderNeOne : addOrderOf betaQ ≠ 1 := by
    intro horder
    exact hbetaNe (AddMonoid.addOrderOf_eq_one_iff.mp horder)
  have horderPos : 0 < addOrderOf betaQ := addOrderOf_pos betaQ
  have horder : addOrderOf betaQ = 2 := by omega
  simpa only [betaQ, pi, H, Q] using horder

/-- One all-positive-stratum quotient endpoint.  For `t=1` it records the
only genuinely new residual, namely trivial retained difference in the
two-element quotient.  Every other arm has the uniform primitive-owner or
two-lift row normal form. -/
theorem TwoRetainedFiveWeightPresentation.positiveStratum_completeQuotientRowNormalForm
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (t = 1 ∧ addOrderOf deltaQ = 1) ∨
      (addOrderOf deltaQ = 2 ^ (t - 1) ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) ∨
      (addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)) := by
  by_cases htOne : t = 1
  · subst t
    have hfirst := p.firstStratum_quotientRowNormalForm
      (q := q) g hg hunique hne y hyq hfullOdd B hrows hminimal
    rcases hfirst with htrivial | hfull
    · exact Or.inl ⟨rfl, htrivial⟩
    · exact Or.inr (Or.inr (by simpa using hfull))
  · have htTwo : 2 ≤ t := by omega
    have hnormal := p.positiveStratum_quotientRowNormalForm
      htTwo g hg hunique hne y hyq hfullOdd B hrows hminimal
    rcases hnormal with hhalf | hfull
    · exact Or.inr (Or.inl hhalf)
    · exact Or.inr (Or.inr hfull)

/-- The complete positive-stratum quotient endpoint with the first-stratum
exchange seed retained.  The sole algebraically trivial retained-difference
arm already contains a deleted owner of full quotient order two. -/
theorem TwoRetainedFiveWeightPresentation.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (t = 1 ∧ addOrderOf deltaQ = 1 ∧
        ∃ b : ↥B,
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 2) ∨
      (addOrderOf deltaQ = 2 ^ (t - 1) ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) ∨
      (addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)) := by
  have hnormal := p.positiveStratum_completeQuotientRowNormalForm
    ht g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with hfirst | hhalf | hfull
  · rcases hfirst with ⟨htOne, htrivial⟩
    subst t
    have howner := p.exists_primitiveOwner_of_firstStratum_trivialRetained
      (q := q) g hg y hyq hfullOdd B hminimal htrivial
    exact Or.inl ⟨rfl, htrivial, howner⟩
  · exact Or.inr (Or.inl hhalf)
  · exact Or.inr (Or.inr hfull)

end MinModulus
