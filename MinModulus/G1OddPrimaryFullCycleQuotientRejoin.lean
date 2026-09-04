import MinModulus.G1OddPrimaryFullCycleRowPartition

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- One concrete presentation of the normalized exact-two private rows. -/
structure TwoRetainedFiveWeightPresentation
    (g : Fin n → G) (y : G) (B : Finset (Fin n)) where
  x : Fin n
  z : Fin n
  weight : ↥B → ℤ
  x_not_mem : x ∉ B
  z_not_mem : z ∉ B
  x_ne_z : x ≠ z
  complement_eq : Finset.univ \ B = {x, z}
  weight_mem : ∀ b, weight b ∈ twoRetainedNormalizedWeightLevels
  row_mem : ∀ b : ↥B,
    (2 : ℤ) • (g (b : Fin n) - g z) +
      weight b • (g x - g z) ∈ AddSubgroup.zmultiples y

/-- Extract one presentation once, so downstream leaf and quotient arguments
share definitionally identical retained coordinates and weights. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fiveWeightPresentation
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B) :
    Nonempty (TwoRetainedFiveWeightPresentation g y B) := by
  classical
  rcases hrows with
    ⟨_hretained, x, z, scalar, coeff, weight,
      hxB, hzB, hxz, hcomplement, _hcoeffInjective,
      _hrowData, hweightData⟩
  refine ⟨⟨x, z, weight, hxB, hzB, hxz, hcomplement,
    fun b ↦ (hweightData b).1, ?_⟩⟩
  intro b
  have htarget :
      twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
          (scalar b • y) ∈ AddSubgroup.zmultiples y := by
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
  convert htarget using 1
  rw [(hweightData b).2.2]
  module

/-- A primitive retained difference rules out the unique odd row weight. -/
theorem TwoRetainedFiveWeightPresentation.weight_ne_neg_one_of_primitive
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (y : ZMod (2 ^ 6 * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64) :
    ∀ b : ↥B, p.weight b ≠ -1 := by
  classical
  intro b hb
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 6 * q) ⧸ H
  let pi : ZMod (2 ^ 6 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  have hquotientModulus :
      (2 ^ 6 * q) / addOrderOf y = 64 := by
    rw [Nat.mul_div_assoc (2 ^ 6) hyq, hfullOdd]
    norm_num
  have hQcardNat : Nat.card Q = 64 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 6 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 6 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hQcard : Fintype.card Q = 64 := by
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
  have hcardBeta : (64 : ℕ) • betaQ = 0 := by
    rw [← hQcard]
    exact card_nsmul_eq_zero
  have hthirtyTwoDelta : (32 : ℕ) • deltaQ = 0 := by
    rw [hdeltaDouble]
    calc
      (32 : ℕ) • ((2 : ℕ) • betaQ) = (64 : ℕ) • betaQ := by module
      _ = 0 := hcardBeta
  have hdvd : addOrderOf deltaQ ∣ 32 :=
    addOrderOf_dvd_of_nsmul_eq_zero hthirtyTwoDelta
  have horderQ : addOrderOf deltaQ = 64 := by
    simpa only [deltaQ, pi, H, Q] using hprimitive
  rw [horderQ] at hdvd
  norm_num at hdvd

/-- In a minimal sixth-stratum modulus, an index-two retained difference
forces the unique odd row weight in the same concrete presentation. -/
theorem TwoRetainedFiveWeightPresentation.exists_weight_eq_neg_one_of_indexTwo
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (hindex :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 32) :
    ∃ b : ↥B, p.weight b = -1 := by
  classical
  by_contra hnoHeavy
  push Not at hnoHeavy
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 6 * q) ⧸ H
  let pi : ZMod (2 ^ 6 * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ 6 * q) := g p.x - g p.z
  let deltaQ : Q := pi delta
  let K : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    H ⊔ AddSubgroup.zmultiples delta
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
    (QuotientAddGroup.mk'_surjective H)
  have hquotientModulus :
      (2 ^ 6 * q) / addOrderOf y = 64 := by
    rw [Nat.mul_div_assoc (2 ^ 6) hyq, hfullOdd]
    norm_num
  have hQcardNat : Nat.card Q = 64 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 6 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 6 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  have hdeltaOrder : addOrderOf deltaQ = 32 := by
    simpa only [deltaQ, delta, pi, H, Q] using hindex
  have hdeletedQuotient : ∀ b : ↥B,
      pi (g (b : Fin n) - g p.z) ∈
        AddSubgroup.zmultiples deltaQ := by
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
    have huCases : uQ = 0 ∨ uQ = (16 : ℕ) • deltaQ :=
      eq_zero_or_sixteen_nsmul_of_add_self_eq_zero_of_card_sixtyFour
        hQcardNat deltaQ uQ hdeltaOrder huDouble
    have huMem : uQ ∈ AddSubgroup.zmultiples deltaQ := by
      rcases huCases with hzero | hu
      · rw [hzero]
        exact AddSubgroup.zero_mem _
      · rw [hu]
        exact AddSubgroup.nsmul_mem _
          (AddSubgroup.mem_zmultiples deltaQ) 16
    have hkMem : k • deltaQ ∈ AddSubgroup.zmultiples deltaQ :=
      AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples deltaQ) k
    have hbetaEq : betaQ = uQ - k • deltaQ := by
      simp only [uQ]
      module
    change betaQ ∈ AddSubgroup.zmultiples deltaQ
    rw [hbetaEq]
    exact AddSubgroup.sub_mem _ huMem hkMem
  have hquotientMem_lift : ∀ v : ZMod (2 ^ 6 * q),
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
  have hKcard : Nat.card K ≤ 32 * addOrderOf y := by
    have hbound := card_sup_zmultiples_le_natAbs_mul H delta e he heMem
    have henatAbs : e.natAbs = 32 := by simp [e, hdeltaOrder]
    rw [henatAbs] at hbound
    simpa only [K, H, Nat.card_zmultiples] using hbound
  have hqpos : 0 < q := by
    have hNpos : 0 < 2 ^ 6 * q := NeZero.pos (2 ^ 6 * q)
    omega
  have hyLe : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hyq
  have hKlt : Nat.card K < 2 ^ 6 * q := by
    calc
      Nat.card K ≤ 32 * addOrderOf y := hKcard
      _ ≤ 32 * q := Nat.mul_le_mul_left 32 hyLe
      _ < 2 ^ 6 * q := by norm_num; omega
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKdiv : Nat.card K ∣ 2 ^ 6 * q := by
    have hdiv : Nat.card K ∣ Nat.card (ZMod (2 ^ 6 * q)) :=
      AddSubgroup.card_addSubgroup_dvd_card K
    simpa only [Nat.card_zmod] using hdiv
  letI : IsAddCyclic K := AddSubgroup.isAddCyclic K
  let equiv : K ≃+ ZMod (Nat.card K) :=
    (zmodAddCyclicAddEquiv (G := K) inferInstance).symm
  have hAdmits : AdmitsValidTuple n (Nat.card K) := by
    refine ⟨fun i ↦ equiv (gK i), ?_⟩
    exact validTuple_comp hgK equiv.toAddMonoidHom equiv.injective
  exact (hminimal (Nat.card K) hKpos hKlt hKdiv hAdmits).elim

/-- Exact quotient phase for a fixed presentation, with no existential-data
realignment between the quotient and leaf arguments. -/
theorem TwoRetainedFiveWeightPresentation.sixthStratum_phase
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    (addOrderOf (pi (g p.x - g p.z)) = 32 ∧
        ∃ b : ↥B, p.weight b = -1) ∨
      (addOrderOf (pi (g p.x - g p.z)) = 64 ∧
        ∀ b : ↥B, p.weight b ≠ -1) := by
  have horder :=
    hrows.retainedDifference_quotientOrder_eq_thirtyTwo_or_sixtyFour_of_sixthStratum_minimal
      g hg hunique hne y hyq hfullOdd B hminimal p.x p.z
        p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases horder with hindex | hprimitive
  · exact Or.inl ⟨hindex,
      p.exists_weight_eq_neg_one_of_indexTwo
        g hg y hyq hfullOdd B hminimal hindex⟩
  · exact Or.inr ⟨hprimitive,
      p.weight_ne_neg_one_of_primitive g y B hyq hfullOdd hprimitive⟩

/-- Exact solution of every quotient row for one fixed presentation. -/
theorem TwoRetainedFiveWeightPresentation.sixthStratum_quotientRowNormalForm
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    (addOrderOf deltaQ = 32 ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 64) ∨
      (addOrderOf deltaQ = 64 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (32 : ℕ) • deltaQ - k • deltaQ)) := by
  classical
  have hphase := p.sixthStratum_phase
    g hg hunique hne y hyq hfullOdd B hrows hminimal
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ 6 * q) ⧸ H
  let pi : ZMod (2 ^ 6 * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsAddCyclic Q := isAddCyclic_of_surjective pi
    (QuotientAddGroup.mk'_surjective H)
  have hquotientModulus :
      (2 ^ 6 * q) / addOrderOf y = 64 := by
    rw [Nat.mul_div_assoc (2 ^ 6) hyq, hfullOdd]
    norm_num
  have hQcardNat : Nat.card Q = 64 := by
    have hmul : Nat.card Q * addOrderOf y = 2 ^ 6 * q := by
      simpa only [Q, H, Nat.card_zmod] using
        nat_card_quotient_zmultiples_mul_addOrderOf y
    have hcard : Nat.card Q = (2 ^ 6 * q) / addOrderOf y := by
      exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
    exact hcard.trans hquotientModulus
  change
    (addOrderOf deltaQ = 32 ∧
        ∃ b : ↥B, p.weight b = -1 ∧
          addOrderOf (pi (g (b : Fin n) - g p.z)) = 64) ∨
      (addOrderOf deltaQ = 64 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (32 : ℕ) • deltaQ - k • deltaQ))
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
    have hdeltaOrder : addOrderOf deltaQ = 32 := by
      simpa only [deltaQ, pi, H, Q] using hindex
    simpa only [betaQ, pi, H, Q] using
      addOrderOf_eq_sixtyFour_of_two_nsmul_eq_order_thirtyTwo_of_card_sixtyFour
        hQcardNat deltaQ betaQ hdeltaOrder hdouble
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
    have hdeltaOrder : addOrderOf deltaQ = 64 := by
      simpa only [deltaQ, pi, H, Q] using hprimitive
    rcases eq_zero_or_thirtyTwo_nsmul_of_add_self_eq_zero_of_card_sixtyFour
        hQcardNat deltaQ uQ hdeltaOrder huDouble with hzero | hhalf
    · left
      change betaQ = -(k • deltaQ)
      dsimp only [uQ] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    · right
      change betaQ = (32 : ℕ) • deltaQ - k • deltaQ
      dsimp only [uQ] at hhalf
      apply eq_sub_of_add_eq
      exact hhalf

/-- The fully deleted leaf-cycle terminal for one fixed row presentation. -/
theorem TwoRetainedFiveWeightPresentation.fullDeleted_weight_constant_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ 6 * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∀ i j,
      p.weight ⟨leaf i, hleafB i⟩ = p.weight ⟨leaf j, hleafB j⟩ := by
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let delta : ZMod (2 ^ 6 * q) := g p.x - g p.z
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
  let cycleWeight : Fin d → ℤ := fun i ↦ p.weight ⟨leaf i, hleafB i⟩
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
  · have he32 :=
      hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
        g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
          p.x_ne_z p.complement_eq e he (by omega) (by omega) (by
            simpa only [delta, H] using heMem)
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · simpa only [cycleWeight] using hconstant

/-- Lossless rejoin of the full-deleted leaf terminal with the all-owner
quotient normal form.  A heavy primitive owner is either genuinely off the
cycle, or forces every displayed leaf weight to be `-1`. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fullDeleted_sixthStratum_quotientRejoin
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ 6 * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      (∀ i j,
        p.weight ⟨leaf i, hleafB i⟩ =
          p.weight ⟨leaf j, hleafB j⟩) ∧
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      (addOrderOf deltaQ = 32 ∧
          ∃ b : ↥B, p.weight b = -1 ∧
            addOrderOf (pi (g (b : Fin n) - g p.z)) = 64 ∧
            ((b : Fin n) ∉ Set.range leaf ∨
              ∀ i, p.weight ⟨leaf i, hleafB i⟩ = -1)) ∨
        (addOrderOf deltaQ = 64 ∧
          ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
            (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
              pi (g (b : Fin n) - g p.z) =
                (32 : ℕ) • deltaQ - k • deltaQ)) := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hconstant := p.fullDeleted_weight_constant_of_sixthStratum_minimal
    g hg hunique hne y hyq B hrows hminimal hd leaf R a hleafB hdouble
  refine ⟨p, hconstant, ?_⟩
  have hnormal := p.sixthStratum_quotientRowNormalForm
    g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with ⟨hindex, b, hb, hbprimitive⟩ |
      ⟨hprimitive, hrowsSolved⟩
  · left
    refine ⟨hindex, b, hb, hbprimitive, ?_⟩
    by_cases hbrange : (b : Fin n) ∈ Set.range leaf
    · right
      obtain ⟨i, hi⟩ := hbrange
      intro j
      calc
        p.weight ⟨leaf j, hleafB j⟩ =
            p.weight ⟨leaf i, hleafB i⟩ := hconstant j i
        _ = p.weight b := by
          congr 1
          exact Subtype.ext hi
        _ = -1 := hb
    · exact Or.inl hbrange
  · exact Or.inr ⟨hprimitive, hrowsSolved⟩

/-- Fixed-presentation form of the exceptional two-leaf pure-pair endpoint. -/
theorem TwoRetainedFiveWeightPresentation.oneRetainedTwoLeaf_purePair_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (leaf : Fin 2 → Fin n) (a : ZMod (2 ^ 6 * q)) (r : Fin 2)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin 2 ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    (leaf r = p.x ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = -2) ∨
      (leaf r = p.z ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = 0) := by
  classical
  obtain ⟨i₀, hi₀r⟩ :=
    Fintype.exists_ne_of_one_lt_card (by simp : 1 < Fintype.card (Fin 2)) r
  have hi₀B : leaf i₀ ∈ B := (hleafB i₀).2 hi₀r
  let b : ↥B := ⟨leaf i₀, hi₀B⟩
  let w : ℤ := p.weight b
  have hw : w ∈ twoRetainedNormalizedWeightLevels := p.weight_mem b
  have hi₀Disp : g (leaf i₀) - a ∈ AddSubgroup.zmultiples y := by
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i₀, rfl⟩
  have htransitionSimple :
      (-w) • (g p.x - g p.z) + (2 : ℤ) • (g p.z - a) ∈
        AddSubgroup.zmultiples y := by
    have hsub := (AddSubgroup.zmultiples y).sub_mem (p.row_mem b)
      ((AddSubgroup.zmultiples y).zsmul_mem hi₀Disp 2)
    have hneg := (AddSubgroup.zmultiples y).neg_mem hsub
    convert hneg using 1
    dsimp only [b, w]
    module
  have hterminal := constantFiveWeight_transition_terminal
    (g p.x) (g p.z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
  have hrNotB : leaf r ∉ B := by
    intro hrB
    exact (hleafB r).1 hrB rfl
  have hrPair : leaf r = p.x ∨ leaf r = p.z := by
    have hrComplement : leaf r ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hrNotB⟩
    rw [p.complement_eq] at hrComplement
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hrComplement
  have hrDisp : g (leaf r) - a ∈ AddSubgroup.zmultiples y := by
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨r, rfl⟩
  have hother : ∀ i : Fin 2, i ≠ r → i = i₀ := by
    intro i hir
    fin_omega
  have hweightOther : ∀ i (hi : leaf i ∈ B),
      p.weight ⟨leaf i, hi⟩ = w := by
    intro i hi
    have hir : i ≠ r := (hleafB i).1 hi
    have hii : i = i₀ := hother i hir
    subst i
    have hb : (⟨leaf i₀, hi⟩ : ↥B) = b := by
      apply Subtype.ext
      rfl
    exact (congrArg p.weight hb).trans rfl
  rcases hrPair with hrX | hrZ
  · have hxMem : g p.x - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hrX] using hrDisp
    rcases hterminal.1 hxMem with hsmall | hwMinusTwo
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
            p.x_ne_z p.complement_eq e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inl ⟨hrX, fun i hi ↦
        (hweightOther i hi).trans hwMinusTwo⟩
  · have hzMem : g p.z - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hrZ] using hrDisp
    rcases hterminal.2 hzMem with hsmall | hwZero
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
            p.x_ne_z p.complement_eq e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inr ⟨hrZ, fun i hi ↦
        (hweightOther i hi).trans hwZero⟩

/-- With at least three leaves, the punctured recurrence forces constant
weight on every displayed deleted leaf of one fixed presentation. -/
theorem TwoRetainedFiveWeightPresentation.oneRetained_weight_constant_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 2 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 6 * q)) (r : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∀ i (hi : leaf i ∈ B) j (hj : leaf j ∈ B),
      p.weight ⟨leaf i, hi⟩ = p.weight ⟨leaf j, hj⟩ := by
  classical
  obtain ⟨i₀, hi₀r, hi₀prev⟩ :=
    Fin.exists_ne_and_ne_of_two_lt r (R.symm r) hd
  have hRi₀ : R i₀ ≠ r := by
    intro hRi₀
    apply hi₀prev
    calc
      i₀ = R.symm (R i₀) := (R.symm_apply_apply i₀).symm
      _ = R.symm r := congrArg R.symm hRi₀
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let delta : ZMod (2 ^ 6 * q) := g p.x - g p.z
  have htransition : ∀ i (hi : i ≠ r) (hRi : R i ≠ r),
      (p.weight ⟨leaf (R i), (hleafB (R i)).2 hRi⟩ -
          2 * p.weight ⟨leaf i, (hleafB i).2 hi⟩) • delta +
        (2 : ℤ) • (g p.z - a) ∈ H := by
    intro i hi hRi
    have hiB : leaf i ∈ B := (hleafB i).2 hi
    have hRiB : leaf (R i) ∈ B := (hleafB (R i)).2 hRi
    have hsub := H.sub_mem (p.row_mem ⟨leaf (R i), hRiB⟩)
      (H.zsmul_mem (p.row_mem ⟨leaf i, hiB⟩) 2)
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
  let u : Fin d := R.symm r
  let v : Fin d := R r
  have hu : u ≠ r := by
    intro hur
    apply hRne r
    have happly : R (R.symm r) = r := R.apply_symm_apply r
    simpa only [u, hur] using happly
  have hv : v ≠ r := by simpa only [v] using hRne r
  have huB : leaf u ∈ B := (hleafB u).2 hu
  have hvB : leaf v ∈ B := (hleafB v).2 hv
  have hfour : g (leaf v) - a = (4 : ℤ) • (g (leaf u) - a) := by
    have huStep : g (leaf r) - a =
        (2 : ℤ) • (g (leaf u) - a) := by
      have hstep := hdouble u
      simpa only [u, R.apply_symm_apply] using hstep
    calc
      g (leaf v) - a = (2 : ℤ) • (g (leaf r) - a) := by
        simpa only [v] using hdouble r
      _ = (2 : ℤ) • ((2 : ℤ) • (g (leaf u) - a)) := by rw [huStep]
      _ = (4 : ℤ) • (g (leaf u) - a) := by module
  have htwoStep :
      (p.weight ⟨leaf v, hvB⟩ - 4 * p.weight ⟨leaf u, huB⟩) •
          delta + (6 : ℤ) • (g p.z - a) ∈ H := by
    have hsub := H.sub_mem (p.row_mem ⟨leaf v, hvB⟩)
      (H.zsmul_mem (p.row_mem ⟨leaf u, huB⟩) 4)
    convert hsub using 1
    dsimp only [H, delta]
    have hvValue : g (leaf v) = (4 : ℤ) • (g (leaf u) - a) + a := by
      calc
        g (leaf v) = (g (leaf v) - a) + a := by abel
        _ = (4 : ℤ) • (g (leaf u) - a) + a := by rw [hfour]
    rw [hvValue]
    module
  let cycleWeight : Fin d → ℤ := fun i ↦
    if hi : leaf i ∈ B then p.weight ⟨leaf i, hi⟩ else 0
  have hcycleWeight : ∀ i, i ≠ r →
      cycleWeight i ∈ twoRetainedNormalizedWeightLevels := by
    intro i hi
    have hiB : leaf i ∈ B := (hleafB i).2 hi
    simp only [cycleWeight, dif_pos hiB]
    exact p.weight_mem ⟨leaf i, hiB⟩
  have hcycleTransition : ∀ i, i ≠ r → R i ≠ r →
      (cycleWeight (R i) - 2 * cycleWeight i) • delta +
        (2 : ℤ) • (g p.z - a) ∈ H := by
    intro i hi hRi
    have hiB : leaf i ∈ B := (hleafB i).2 hi
    have hRiB : leaf (R i) ∈ B := (hleafB (R i)).2 hRi
    simpa only [cycleWeight, dif_pos hiB, dif_pos hRiB] using
      htransition i hi hRi
  have hcycleTwoStep :
      (cycleWeight (R r) - 4 * cycleWeight (R.symm r)) • delta +
        (3 : ℤ) • ((2 : ℤ) • (g p.z - a)) ∈ H := by
    have hvValue : cycleWeight (R r) = p.weight ⟨leaf v, hvB⟩ := by
      simp only [cycleWeight, v, dif_pos hvB]
    have huValue : cycleWeight (R.symm r) = p.weight ⟨leaf u, huB⟩ := by
      simp only [cycleWeight, u, dif_pos huB]
    rw [hvValue, huValue]
    convert htwoStep using 1
    module
  have hkernel32 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 32 := by
    intro e he helow hehigh heMem
    exact hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
      g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
        p.x_ne_z p.complement_eq e he helow hehigh (by
          simpa only [delta, H] using heMem)
  have hconstant :=
    fiveWeightPuncturedPermutation_thirtyTwo_weight_constant
      R r i₀ (hRne r) hi₀r hRi₀ cycleWeight hcycleWeight delta
        ((2 : ℤ) • (g p.z - a)) H hcycleTransition hcycleTwoStep hkernel32
  intro i hiB j hjB
  have hi : i ≠ r := (hleafB i).1 hiB
  have hj : j ≠ r := (hleafB j).1 hjB
  have hiValue : cycleWeight i = p.weight ⟨leaf i, hiB⟩ := by
    simp only [cycleWeight, dif_pos hiB]
  have hjValue : cycleWeight j = p.weight ⟨leaf j, hjB⟩ := by
    simp only [cycleWeight, dif_pos hjB]
  rw [← hiValue, ← hjValue]
  exact hconstant i hi j hj

/-- Fixed-presentation pure-pair endpoint for a unique retained leaf in a
cycle of length at least three. -/
theorem TwoRetainedFiveWeightPresentation.oneRetained_purePair_of_sixthStratum_minimal
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 2 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 6 * q)) (r : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    (leaf r = p.x ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = -2) ∨
      (leaf r = p.z ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = 0) := by
  classical
  have hconstant := p.oneRetained_weight_constant_of_sixthStratum_minimal
    g hg hunique hne y hyq B hrows hminimal hd leaf R hRne a r hleafB hdouble
  obtain ⟨i₀, hi₀r, hi₀prev⟩ :=
    Fin.exists_ne_and_ne_of_two_lt r (R.symm r) hd
  have hRi₀ : R i₀ ≠ r := by
    intro hRi₀
    apply hi₀prev
    calc
      i₀ = R.symm (R i₀) := (R.symm_apply_apply i₀).symm
      _ = R.symm r := congrArg R.symm hRi₀
  have hi₀B : leaf i₀ ∈ B := (hleafB i₀).2 hi₀r
  have hRi₀B : leaf (R i₀) ∈ B := (hleafB (R i₀)).2 hRi₀
  let w : ℤ := p.weight ⟨leaf i₀, hi₀B⟩
  have hw : w ∈ twoRetainedNormalizedWeightLevels :=
    p.weight_mem ⟨leaf i₀, hi₀B⟩
  have hwEdge : p.weight ⟨leaf (R i₀), hRi₀B⟩ = w := by
    simpa only [w] using hconstant (R i₀) hRi₀B i₀ hi₀B
  have htransitionSimple :
      (-w) • (g p.x - g p.z) + (2 : ℤ) • (g p.z - a) ∈
        AddSubgroup.zmultiples y := by
    let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
    have hsub := H.sub_mem (p.row_mem ⟨leaf (R i₀), hRi₀B⟩)
      (H.zsmul_mem (p.row_mem ⟨leaf i₀, hi₀B⟩) 2)
    have hvalue :
        g (leaf (R i₀)) = (2 : ℤ) • g (leaf i₀) - a := by
      calc
        g (leaf (R i₀)) = (g (leaf (R i₀)) - a) + a := by abel
        _ = (2 : ℤ) • (g (leaf i₀) - a) + a := by rw [hdouble i₀]
        _ = (2 : ℤ) • g (leaf i₀) - a := by module
    convert hsub using 1
    dsimp only [H]
    rw [hvalue, hwEdge]
    dsimp only [w]
    module
  have hterminal := constantFiveWeight_transition_terminal
    (g p.x) (g p.z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
  have hrNotB : leaf r ∉ B := by
    intro hrB
    exact (hleafB r).1 hrB rfl
  have hrPair : leaf r = p.x ∨ leaf r = p.z := by
    have hrComplement : leaf r ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hrNotB⟩
    rw [p.complement_eq] at hrComplement
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hrComplement
  have hrDisp : g (leaf r) - a ∈ AddSubgroup.zmultiples y := by
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨r, rfl⟩
  rcases hrPair with hrX | hrZ
  · have hxMem : g p.x - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hrX] using hrDisp
    rcases hterminal.1 hxMem with hsmall | hwMinusTwo
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
            p.x_ne_z p.complement_eq e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inl ⟨hrX, fun i hi ↦
        (hconstant i hi i₀ hi₀B).trans hwMinusTwo⟩
  · have hzMem : g p.z - a ∈ AddSubgroup.zmultiples y := by
      simpa only [hrZ] using hrDisp
    rcases hterminal.2 hzMem with hsmall | hwZero
    · obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
      have he32 :=
        hrows.boundedKernelCoefficient_natAbs_eq_thirtyTwo_of_sixthStratum_minimal
          g hg hunique hne y hyq B hminimal p.x p.z p.x_not_mem p.z_not_mem
            p.x_ne_z p.complement_eq e he (by omega) (by omega) heMem
      have he32Z : (e.natAbs : ℤ) = 32 := by exact_mod_cast he32
      rcases Int.natAbs_eq e with hePos | heNeg <;> exfalso <;> omega
    · exact Or.inr ⟨hrZ, fun i hi ↦
        (hconstant i hi i₀ hi₀B).trans hwZero⟩

/-- Uniform fixed-presentation pure-pair endpoint, including the special
two-leaf cycle where no deleted-to-deleted edge is available. -/
theorem TwoRetainedFiveWeightPresentation.oneRetained_purePair_of_two_le
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (p : TwoRetainedFiveWeightPresentation g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 6 * q)) (r : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    (leaf r = p.x ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = -2) ∨
      (leaf r = p.z ∧ ∀ i (hi : leaf i ∈ B),
        p.weight ⟨leaf i, hi⟩ = 0) := by
  by_cases hdTwo : d = 2
  · subst d
    exact p.oneRetainedTwoLeaf_purePair_of_sixthStratum_minimal
      g hg hunique hne y hyq B hrows hminimal leaf a r hleafB hspan
  · have hdThree : 2 < d := by omega
    exact p.oneRetained_purePair_of_sixthStratum_minimal
      g hg hunique hne y hyq B hrows hminimal hdThree leaf R hRne a r
        hleafB hdouble hspan

/-- Lossless rejoin of the unique-retained pure-pair terminal with the exact
all-owner quotient normal form.  In the index-two phase its primitive heavy
owner is necessarily outside the displayed leaf cycle. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetained_sixthStratum_quotientRejoin
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 6 * q)) (r : Fin d)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - a)) =
      AddSubgroup.zmultiples y) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      ((leaf r = p.x ∧ ∀ i (hi : leaf i ∈ B),
          p.weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf r = p.z ∧ ∀ i (hi : leaf i ∈ B),
          p.weight ⟨leaf i, hi⟩ = 0)) ∧
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      (addOrderOf deltaQ = 32 ∧
          ∃ b : ↥B, p.weight b = -1 ∧
            addOrderOf (pi (g (b : Fin n) - g p.z)) = 64 ∧
            (b : Fin n) ∉ Set.range leaf) ∨
        (addOrderOf deltaQ = 64 ∧
          ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
            (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
              pi (g (b : Fin n) - g p.z) =
                (32 : ℕ) • deltaQ - k • deltaQ)) := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hpure := p.oneRetained_purePair_of_two_le
    g hg hunique hne y hyq B hrows hminimal hd leaf R hRne a r hleafB
      hdouble hspan
  refine ⟨p, hpure, ?_⟩
  have hnormal := p.sixthStratum_quotientRowNormalForm
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
    rcases hpure with ⟨_hrX, hminusTwo⟩ | ⟨_hrZ, hzero⟩
    · have hweightEq := congrArg p.weight hsubtype
      rw [hminusTwo i hiB, hb] at hweightEq
      norm_num at hweightEq
    · have hweightEq := congrArg p.weight hsubtype
      rw [hzero i hiB, hb] at hweightEq
      norm_num at hweightEq
  · exact Or.inr ⟨hprimitive, hrowsSolved⟩

end MinModulus
