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

end MinModulus
