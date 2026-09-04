/-
# Exchanging a primitive deleted owner into the retained quotient

In the sixth-stratum index-two phase, a weight `-1` row supplies a deleted
owner whose difference from one retained coordinate is primitive in the
order-64 quotient.  Exchange that owner with the other retained coordinate.
The resulting set is still a cyclic-kernel support transversal: a witness
avoiding it would be supported on the primitive owner and the remaining
retained coordinate, forcing their difference into the kernel.

After minimizing the exchanged transversal, either at least three quotient
coordinates survive, or the exact-two branch has been reparametrized with a
primitive retained difference.  Thus the order-32 quotient phase is not an
independent terminal.
-/
import MinModulus.G1OddPrimaryFullCycleQuotientRejoin

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Exchange a deleted coordinate `b` with a retained coordinate `x` when
the other retained coordinate `z` has nonzero quotient difference from `b`.
The exchanged set still meets every nonzero cyclic-kernel witness. -/
theorem cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
    (g : Fin n → G) (y : G) {B : Finset (Fin n)}
    (hB : CyclicKernelSupportTransversal g y B)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hdiff : g b - g z ∉ AddSubgroup.zmultiples y) :
    CyclicKernelSupportTransversal g y (insert x (B.erase b)) := by
  classical
  intro scalar htarget c hc
  by_contra hmiss
  push Not at hmiss
  obtain ⟨i, hiB, hci⟩ := hB scalar htarget c hc
  have hib : i = b := by
    by_contra hine
    have hiExchange : i ∈ insert x (B.erase b) := by
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hine, hiB⟩)
    exact hci (hmiss i hiExchange)
  subst i
  have hcx : c x = 0 := hmiss x (Finset.mem_insert_self x _)
  let Bx : Finset (Fin n) := insert x B
  have hbBx : b ∈ Bx := Finset.mem_insert_of_mem hb
  have hzBx : z ∉ Bx := by
    simp only [Bx, Finset.mem_insert, not_or]
    exact ⟨Ne.symm hxz, hzB⟩
  have huniqueRetained : ∀ j : Fin n, j ∉ Bx → j = z := by
    intro j hjBx
    have hjB : j ∉ B := by
      intro hj
      exact hjBx (Finset.mem_insert_of_mem hj)
    have hjComplement : j ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjB⟩
    rw [hcomplement] at hjComplement
    have hjPair : j = x ∨ j = z := by simpa using hjComplement
    rcases hjPair with hjx | hjz
    · subst j
      exact (hjBx (Finset.mem_insert_self x B)).elim
    · exact hjz
  have hprivateBx : ∀ a ∈ Bx, a ≠ b → c a = 0 := by
    intro a haBx hab
    rcases Finset.mem_insert.mp haBx with rfl | haB
    · exact hcx
    · exact hmiss a (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hab, haB⟩))
  have hpairMem : g b - g z ∈ AddSubgroup.zmultiples y :=
    private_kernelWitness_pair_difference_mem_zmultiples
      g y hbBx hzBx huniqueRetained
        ⟨scalar, c, htarget, hc, hci, hprivateBx⟩
  exact hdiff hpairMem

/-- Exchanging one member for a genuinely retained coordinate preserves the
cardinality of the deletion set. -/
theorem card_erase_insert_retained_eq
    {B : Finset (Fin n)} {b x : Fin n} (hb : b ∈ B) (hxB : x ∉ B) :
    (insert x (B.erase b)).card = B.card := by
  classical
  have hxErase : x ∉ B.erase b :=
    fun hx ↦ hxB (Finset.mem_of_mem_erase hx)
  rw [Finset.card_insert_of_notMem hxErase,
    Finset.card_erase_add_one hb]

/-- The exchanged deletion set retains exactly the primitive owner and the
unchanged retained coordinate. -/
theorem complement_erase_insert_retained
    {B : Finset (Fin n)} {b x z : Fin n}
    (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    Finset.univ \ (insert x (B.erase b)) = {b, z} := by
  classical
  ext i
  constructor
  · intro hi
    have hiNotExchange := (Finset.mem_sdiff.mp hi).2
    by_cases hiB : i ∈ B
    · have hib : i = b := by
        by_contra hine
        exact hiNotExchange (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hine, hiB⟩))
      simp [hib]
    · have hiComplement : i ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiB⟩
      rw [hcomplement] at hiComplement
      have hiPair : i = x ∨ i = z := by simpa using hiComplement
      rcases hiPair with hix | hiz
      · subst i
        exact (hiNotExchange (Finset.mem_insert_self x _)).elim
      · simp [hiz]
  · intro hi
    have hiPair : i = b ∨ i = z := by simpa using hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hiPair with hib | hiz
    · subst i
      have hbx : b ≠ x := by
        intro h
        subst x
        exact hxB hb
      simp [hbx]
    · subst i
      simp [Ne.symm hxz, hzB]

/-- The sole remaining exact-two C1 state after transversal exchange: the
minimal quotient has a primitive retained difference and every normalized
row has its exact two-residue solution. -/
def PrimitiveTwoRetainedSixthStratumRows
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      addOrderOf deltaQ = 64 ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (32 : ℕ) • deltaQ - k • deltaQ)

/-- Minimize the exchanged transversal without forgetting its identity.  A
strict shrink retains at least three coordinates; equality makes the literal
set `insert x (B.erase b)` the new primitive exact-two transversal. -/
theorem exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g b - g z)) = 64)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedSixthStratumRows g y (insert x (B.erase b)) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have hquotientNe : pi (g b - g z) ≠ 0 := by
    intro hzero
    have horder : addOrderOf (pi (g b - g z)) = 64 := by
      simpa only [pi, H] using hprimitive
    rw [hzero] at horder
    norm_num at horder
  have hdiff : g b - g z ∉ AddSubgroup.zmultiples y := by
    intro hmem
    exact hquotientNe ((QuotientAddGroup.eq_zero_iff (g b - g z)).2 hmem)
  let Bexchange : Finset (Fin n) := insert x (B.erase b)
  have hBexchange : CyclicKernelSupportTransversal g y Bexchange := by
    simpa only [Bexchange] using
      cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
        g y hmin.1 hb hxB hzB hxz hcomplement hdiff
  obtain ⟨B₀, hB₀sub, hB₀min⟩ :=
    exists_minimalCyclicKernelSupportTransversal_subset
      g y hBexchange
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
    have hp₀primitive : addOrderOf (pi (g p₀.x - g p₀.z)) = 64 := by
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
    have hnormal := p₀.sixthStratum_quotientRowNormalForm
      g hg hunique hne y hyq hfullOdd B₀ hfive₀ hminimal
    have hsolved :
        ∀ b₀ : ↥B₀, ∃ k : ℤ, p₀.weight b₀ = 2 * k ∧
          (pi (g (b₀ : Fin n) - g p₀.z) =
              -(k • pi (g p₀.x - g p₀.z)) ∨
            pi (g (b₀ : Fin n) - g p₀.z) =
              (32 : ℕ) • pi (g p₀.x - g p₀.z) -
                k • pi (g p₀.x - g p₀.z)) := by
      rcases hnormal with ⟨hindex, _b, _hb, _hbp⟩ |
          ⟨_hprimitive, hrowsSolved⟩
      · have : (32 : ℕ) = 64 := hindex.symm.trans hp₀primitive
        omega
      · simpa only [pi, H] using hrowsSolved
    have hstate₀ : PrimitiveTwoRetainedSixthStratumRows g y B₀ := by
      refine ⟨hB₀min, hretained₀, hfive₀, p₀, ?_⟩
      simpa only [pi, H] using And.intro hp₀primitive hsolved
    rw [hB₀eq] at hstate₀
    simpa only [Bexchange] using hstate₀

/-- Compatibility wrapper for callers that do not need the identity of the
exact-two exchanged set. -/
theorem exists_minimalCyclicKernelTransversal_exchange_primitive_or_three
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g b - g z)) = 64)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedSixthStratumRows g y B₀ := by
  rcases exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
      g hg hh hne hunique hno y hyq hfullOdd hmin hretained hb hxB hzB hxz
        hcomplement hprimitive hminimal with hthree | hexact
  · exact Or.inl hthree
  · exact Or.inr ⟨insert x (B.erase b), hexact⟩

/-- Every sixth-stratum exact-two survivor can be placed directly in the
primitive retained-difference state, unless minimizing the primitive-owner
exchange moves it to the already separated three-or-more-retained branch.
In particular, quotient order `32` is no longer a live C1 terminal. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.sixthStratum_exchange_to_primitive_or_three
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedSixthStratumRows g y B₀ := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hnormal := p.sixthStratum_quotientRowNormalForm
    g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with ⟨_hindex, b, _hb, hbprimitive⟩ |
      ⟨hprimitive, hrowsSolved⟩
  · exact exists_minimalCyclicKernelTransversal_exchange_primitive_or_three
      g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
        b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
        hbprimitive hminimal
  · right
    refine ⟨B, hmin, hrows.1, hrows, p, ?_⟩
    exact ⟨hprimitive, hrowsSolved⟩

end MinModulus
