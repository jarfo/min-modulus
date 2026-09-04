/-
# Uniform positive-stratum exchange

The complete quotient normal form exposes a deleted owner of full quotient
order in every non-full retained-difference arm, including the formerly
degenerate first stratum.  Exchange that owner with one retained coordinate
and minimize the resulting cyclic-kernel transversal.

A strict minimization enters the already separated three-retained C2 branch.
Otherwise the literal exchanged set remains minimal, has two retained
coordinates with quotient difference of order `2^t`, and inherits the exact
two-lift row normal form.  Thus no positive stratum needs a separate exchange
argument.
-/
import MinModulus.G1OddPrimaryFullCyclePositiveStratumQuotientPhase
import MinModulus.G1OddPrimaryFullCycleTransversalExchange

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A weight-`-1` owner primitive relative to `z` is equally primitive
relative to `x`: its row says that the retained difference is twice the
owner displacement, so the second displacement is its negative. -/
theorem TwoRetainedFiveWeightPresentation.primitive_otherRetained_of_weight_eq_neg_one
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (b : ↥B) (hweight : p.weight b = -1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hquotientRelation :
      (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (b : Fin n) - g p.z) +
        p.weight b • (g p.x - g p.z))).mpr
    exact p.row_mem b
  have hdeltaDouble : deltaQ = (2 : ℕ) • betaQ := by
    rw [hweight] at hquotientRelation
    change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
    have hrelation' : betaQ + betaQ - deltaQ = 0 := by
      simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
        hquotientRelation
    calc
      deltaQ = (betaQ + betaQ - deltaQ) + deltaQ := by
        rw [hrelation', zero_add]
      _ = betaQ + betaQ := by abel
      _ = (2 : ℕ) • betaQ := (two_nsmul betaQ).symm
  have hdecomp :
      g (b : Fin n) - g p.x =
        (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
    abel
  have hquotient : pi (g (b : Fin n) - g p.x) = -betaQ := by
    rw [hdecomp, map_sub]
    change betaQ - deltaQ = -betaQ
    rw [hdeltaDouble]
    module
  change addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t
  rw [hquotient, addOrderOf_neg]
  simpa only [betaQ, pi, H, Q] using hprimitive

/-- Exchanging an owner outside a one-missing-leaf range for that missing
leaf puts the entire range into the exchanged deletion set. -/
theorem cycleRange_subset_insert_erase_missing
    {d : ℕ} (leaf : Fin d → Fin n) (p : Fin d)
    {B : Finset (Fin n)} {b x : Fin n}
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hmissing : leaf p = x) (hbOutside : b ∉ Set.range leaf) :
    ∀ i, leaf i ∈ insert x (B.erase b) := by
  classical
  intro i
  by_cases hip : i = p
  · subst i
    rw [hmissing]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, (hleafB i).2 hip⟩
    intro hleafb
    exact hbOutside ⟨i, hleafb⟩

/-- The full-order two-retained state after positive-stratum exchange. -/
def PrimitiveTwoRetainedPositiveStratumRows
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)

/-- Minimize one literal positive-stratum primitive-owner exchange.  A strict
shrink enters C2; equality retains the literal exchanged deletion set as a
full-order two-retained state. -/
theorem exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g b - g z)) = 2 ^ t)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedPositiveStratumRows g y
        (insert x (B.erase b)) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have htwo : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hquotientNe : pi (g b - g z) ≠ 0 := by
    intro hzero
    have horder : addOrderOf (pi (g b - g z)) = 2 ^ t := by
      simpa only [pi, H] using hprimitive
    rw [hzero] at horder
    norm_num at horder
    omega
  have hdiff : g b - g z ∉ AddSubgroup.zmultiples y := by
    intro hmem
    exact hquotientNe ((QuotientAddGroup.eq_zero_iff (g b - g z)).2 hmem)
  let Bexchange : Finset (Fin n) := insert x (B.erase b)
  have hBexchange : CyclicKernelSupportTransversal g y Bexchange := by
    simpa only [Bexchange] using
      cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
        g y hmin.1 hb hxB hzB hxz hcomplement hdiff
  obtain ⟨B₀, hB₀sub, hB₀min⟩ :=
    exists_minimalCyclicKernelSupportTransversal_subset g y hBexchange
  have hBexchangeCard : Bexchange.card = B.card := by
    simpa only [Bexchange] using card_erase_insert_retained_eq hb hxB
  have hB₀card : B₀.card ≤ B.card := by
    calc
      B₀.card ≤ Bexchange.card := Finset.card_le_card hB₀sub
      _ = B.card := hBexchangeCard
  by_cases hstrict : B₀.card < B.card
  · left
    refine ⟨B₀, hB₀min, ?_⟩
    have hBcard : B.card ≤ n := by
      simpa using Finset.card_le_univ B
    omega
  · right
    have hcardEq : B₀.card = B.card := by omega
    have hB₀eq : B₀ = Bexchange := by
      apply Finset.eq_of_subset_of_card_le hB₀sub
      rw [hBexchangeCard, hcardEq]
    have hretained₀ : n - B₀.card = 2 := by omega
    have hrows₀ := twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
      g hg hh hne hunique hno y hB₀min hretained₀
    have hfive₀ := hrows₀.fiveWeightRows g y B₀
    obtain ⟨p₀⟩ := hfive₀.fiveWeightPresentation g y B₀
    have hcomplement₀ : Finset.univ \ B₀ = {b, z} := by
      rw [hB₀eq]
      simpa only [Bexchange] using
        complement_erase_insert_retained hb hxB hzB hxz hcomplement
    have hp₀x : p₀.x = b ∨ p₀.x = z := by
      have hxMem : p₀.x ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.x_not_mem⟩
      rw [hcomplement₀] at hxMem
      simpa using hxMem
    have hp₀z : p₀.z = b ∨ p₀.z = z := by
      have hzMem : p₀.z ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.z_not_mem⟩
      rw [hcomplement₀] at hzMem
      simpa using hzMem
    have hp₀primitive : addOrderOf (pi (g p₀.x - g p₀.z)) = 2 ^ t := by
      rcases hp₀x with hxb | hxz'
      · have hzz : p₀.z = z := hp₀z.resolve_left (by
          intro hzb
          exact p₀.x_ne_z (hxb.trans hzb.symm))
        simpa only [hxb, hzz, pi, H] using hprimitive
      · have hzb : p₀.z = b := hp₀z.resolve_right (by
          intro hzz
          exact p₀.x_ne_z (hxz'.trans hzz.symm))
        have hneg : g p₀.x - g p₀.z = -(g b - g z) := by
          rw [hxz', hzb]
          abel
        rw [hneg, map_neg, addOrderOf_neg]
        simpa only [pi, H] using hprimitive
    have hnormal := p₀.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
      ht g hg hunique hne y hyq hfullOdd B₀ hfive₀ hminimal
    have hhalfLt : 2 ^ (t - 1) < 2 ^ t :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hsolved :
        ∀ b₀ : ↥B₀, ∃ k : ℤ, p₀.weight b₀ = 2 * k ∧
          (pi (g (b₀ : Fin n) - g p₀.z) =
              -(k • pi (g p₀.x - g p₀.z)) ∨
            pi (g (b₀ : Fin n) - g p₀.z) =
              (2 ^ (t - 1) : ℕ) • pi (g p₀.x - g p₀.z) -
                k • pi (g p₀.x - g p₀.z)) := by
      rcases hnormal with hfirst | hhalf | hfull
      · have hpowOne : 2 ^ t = 1 := by
          exact hp₀primitive.symm.trans hfirst.2.1
        omega
      · have hpowHalf : 2 ^ t = 2 ^ (t - 1) := by
          exact hp₀primitive.symm.trans hhalf.1
        omega
      · simpa only [pi, H] using hfull.2
    have hstate₀ : PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
      refine ⟨hB₀min, hretained₀, hfive₀, p₀, ?_⟩
      simpa only [pi, H] using And.intro hp₀primitive hsolved
    rw [hB₀eq] at hstate₀
    simpa only [Bexchange] using hstate₀

/-- Every positive-stratum exact-two state reaches C2 or the uniform
full-order two-retained state.  The first-stratum trivial-difference case is
handled by the primitive owner furnished by minimality. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.positiveStratum_exchange_to_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hnormal := p.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
    ht g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with hfirst | hhalf | hfull
  · rcases hfirst with ⟨rfl, _htrivial, b, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · rcases hhalf.2 with ⟨b, _hbweight, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · right
    refine ⟨B, hmin, hrows.1, hrows, p, ?_⟩
    exact hfull

/-- Lossless fifth-stratum connection of the pure-pair quotient rejoin to
uniform exchange minimization.  Exchanging the primitive half-order owner
inserts the actual missing cycle leaf, so the equality arm retains a fully
deleted cycle.  The already-full arm retains its original one-missing-leaf
orientation and presentation. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_exchangeRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
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
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ ∧
          ((∀ i, leaf i ∈ B₀) ∨
            (B₀ = B ∧
              ∃ pres : TwoRetainedFiveWeightPresentation g y B,
                ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = -2) ∨
                  (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = 0)) ∧
                addOrderOf
                  ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                    (g pres.x - g pres.z)) = 32)) := by
  classical
  obtain ⟨pres, hpure, hnormal⟩ :=
    hrows.oneRetainedCycle_criticalFifthStratum_quotientRejoin
      hq g hg hcritical hunique hne y hyq hfullOdd hrTwo B hminimal leaf
        hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB hdouble hspan
  rcases hnormal with hhalf | hfull
  · rcases hhalf with
      ⟨_hindex, b, hbweight, hbprimitive, hbOutside⟩
    rcases hpure with hpureX | hpureZ
    · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.x_not_mem pres.z_not_mem
            pres.x_ne_z pres.complement_eq hbprimitive hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.x (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureX.1
          hbOutside
    · have hbprimitiveX :=
        pres.primitive_otherRetained_of_weight_eq_neg_one
          (t := 5) (q := q) g y B b hbweight hbprimitive
      have hcomplementReverse : Finset.univ \ B = {pres.z, pres.x} := by
        simpa only [pair_comm] using pres.complement_eq
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.z_not_mem pres.x_not_mem
            pres.x_ne_z.symm hcomplementReverse hbprimitiveX hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.z (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureZ.1
          hbOutside
  · right
    have hstate : PrimitiveTwoRetainedPositiveStratumRows g y B := by
      refine ⟨hmin, hrows.1, hrows, pres, ?_⟩
      simpa using hfull
    exact ⟨B, hstate, Or.inr ⟨rfl, pres, hpure, hfull.1⟩⟩

end MinModulus
