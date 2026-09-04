/-
# Nondegenerate mass charge for Mersenne residual matrices

A full residual matrix cannot have a singleton negative set.  If `|M|=1`,
its exact row-degree formula makes the selected residual support empty; the
off-leaf zero law then makes a purported nonzero witness identically zero.
Thus `|M|>=2`, and the exact mass `2|M|(|M|-1)` is at least four.  Selecting
that mass for each residual owner yields a uniform lower bound on the summed
matrix incidence over any owner fiber.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneExternalFiberCharge

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- The incidence fields of one concrete residual-matrix presentation that
are needed to prove nondegeneracy and charge its mass. -/
def AntipodalRepairResidualIncidenceData
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (_r : Fin n) (v : G) (b : ↥B)
    (s : ℕ) (A M : Finset (Fin d)) : Prop :=
  0 < s ∧ p.scalar b • y = s • v ∧ M.Nonempty ∧
    (∀ m, m ∈ M →
      let residual := normalizedPrivateRepairResidual g y B p f z A M m
      Witness g (-((a m.val + s) • v)) residual ∧
        -((a m.val + s) • v) ≠ 0 ∧
        ∀ j, j ∉ (Finset.univ : Finset (Fin d)).image f → residual j = 0) ∧
    (∀ m, m ∈ M →
      (normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m).card = 2 * (M.card - 1)) ∧
    (∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
      g y B p f z A M m).card) = M.card * (2 * (M.card - 1))

/-- A concrete incidence presentation has at least two negative indices. -/
theorem AntipodalRepairResidualIncidenceData.two_le_card_negativeSet
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G) (b : ↥B)
    (s : ℕ) (A M : Finset (Fin d))
    (hdata : AntipodalRepairResidualIncidenceData
      g y B p f z r v b s A M) :
    2 ≤ M.card := by
  classical
  rcases hdata with
    ⟨_hs0, _htarget, hMne, hresidual, hrowCard, _hmass⟩
  by_contra hnot
  have hMpos : 0 < M.card := Finset.card_pos.mpr hMne
  have hMcard : M.card = 1 := by omega
  obtain ⟨m, hmM⟩ := hMne
  have hsupportCard :
      (normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m).card = 0 := by
    simpa only [hMcard, Nat.reduceSub, mul_zero] using hrowCard m hmM
  have hsupportEmpty : normalizedPrivateRepairResidualLeafSupport
      g y B p f z A M m = ∅ := Finset.card_eq_zero.mp hsupportCard
  obtain ⟨hWitness, _htargetNe, hoff⟩ := hresidual m hmM
  apply hWitness.1
  funext j
  by_cases hj : j ∈ (Finset.univ : Finset (Fin d)).image f
  · obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
    rw [← hij]
    by_contra hne
    have hiSupport : i ∈ normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m := by
      simp only [normalizedPrivateRepairResidualLeafSupport,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne
    rw [hsupportEmpty] at hiSupport
    simp at hiSupport
  · exact hoff j hj

/-- A numerical mass together with the concrete residual incidence data from
which it is computed. -/
def AntipodalRepairResidualIncidenceMassWitness
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G) (b : ↥B)
    (mass : ℕ) : Prop :=
  ∃ s : ℕ, ∃ A M : Finset (Fin d),
    AntipodalRepairResidualIncidenceData g y B p f z r v b s A M ∧
      mass = ∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
        g y B p f z A M m).card

/-- Every full residual matrix supplies a genuine incidence mass of at least
four, computed from the same binary subsets and residual rows. -/
theorem AntipodalRepairResidualMatrix.exists_incidenceMass_ge_four
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G) (b : ↥B)
    (hmatrix : AntipodalRepairResidualMatrix g y B p f z r v b) :
    ∃ mass : ℕ,
      AntipodalRepairResidualIncidenceMassWitness
        g y B p f z r v b mass ∧ 4 ≤ mass := by
  rcases hmatrix with
    ⟨s, A, M, hs0, _hsq, htarget, _hdisjoint, hcard, hzA,
      _harithmetic, hresidual, _hsupport, hrowCard,
      _hnegative, _hpositive, hmass⟩
  have hMne : M.Nonempty := by
    apply Finset.card_pos.mp
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨z, hzA⟩
    omega
  have hdata : AntipodalRepairResidualIncidenceData
      g y B p f z r v b s A M := by
    refine ⟨hs0, htarget, hMne, ?_, hrowCard, hmass⟩
    intro m hmM
    have hm := hresidual m hmM
    dsimp only at hm ⊢
    exact ⟨hm.1, hm.2.1, hm.2.2.2.2⟩
  have htwo := hdata.two_le_card_negativeSet
    g y B p f z r v b s A M
  let mass := ∑ m ∈ M, (normalizedPrivateRepairResidualLeafSupport
    g y B p f z A M m).card
  have hfactor : 2 ≤ 2 * (M.card - 1) := by omega
  have hfourProduct : 4 ≤ M.card * (2 * (M.card - 1)) := by
    simpa only [show 4 = 2 * 2 by norm_num] using
      Nat.mul_le_mul htwo hfactor
  have hfour : 4 ≤ mass := by
    dsimp only [mass]
    rw [hmass]
    exact hfourProduct
  exact ⟨mass, ⟨s, A, M, hdata, rfl⟩, hfour⟩

/-- Canonically selected exact incidence mass of a residual owner, or zero
outside the residual-matrix predicate. -/
noncomputable def antipodalRepairResidualIncidenceMass
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G)
    (b : ↥B) : ℕ := by
  classical
  by_cases hmatrix : AntipodalRepairResidualMatrix g y B p f z r v b
  · exact Classical.choose
      (hmatrix.exists_incidenceMass_ge_four g y B p f z r v b)
  · exact 0

/-- The selected mass retains its concrete incidence presentation and is at
least four whenever the owner carries a residual matrix. -/
theorem antipodalRepairResidualIncidenceMass_spec
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G)
    (b : ↥B)
    (hmatrix : AntipodalRepairResidualMatrix g y B p f z r v b) :
    AntipodalRepairResidualIncidenceMassWitness g y B p f z r v b
        (antipodalRepairResidualIncidenceMass g y B p f z r v b) ∧
      4 ≤ antipodalRepairResidualIncidenceMass g y B p f z r v b := by
  classical
  rw [antipodalRepairResidualIncidenceMass, dif_pos hmatrix]
  exact Classical.choose_spec
    (hmatrix.exists_incidenceMass_ge_four g y B p f z r v b)

/-- Summed residual-matrix incidence dominates four times the number of
residual owners in any finite external fiber. -/
theorem four_mul_card_residualOwners_le_sum_incidenceMass
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (v : G)
    (E : Finset ↥B) :
    4 * (ownersSatisfying E (fun b ↦
      AntipodalRepairResidualMatrix g y B p f z r v b)).card ≤
      ∑ b ∈ ownersSatisfying E (fun b ↦
        AntipodalRepairResidualMatrix g y B p f z r v b),
          antipodalRepairResidualIncidenceMass g y B p f z r v b := by
  classical
  let R := ownersSatisfying E (fun b ↦
    AntipodalRepairResidualMatrix g y B p f z r v b)
  calc
    4 * R.card = ∑ _b ∈ R, 4 := by simp [Nat.mul_comm]
    _ ≤ ∑ b ∈ R,
        antipodalRepairResidualIncidenceMass g y B p f z r v b := by
      apply Finset.sum_le_sum
      intro b hbR
      have hbMatrix := (mem_ownersSatisfying_iff E
        (fun u ↦ AntipodalRepairResidualMatrix g y B p f z r v u) b).mp hbR
      exact (antipodalRepairResidualIncidenceMass_spec
        g y B p f z r v b hbMatrix.2).2

end MinModulus
