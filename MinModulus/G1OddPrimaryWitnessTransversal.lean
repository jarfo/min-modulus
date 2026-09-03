/-
# Witness transversals for an odd-primary cyclic quotient

For a valid tuple, a zero witness after quotienting by `zmultiples y` lifts
to a witness at a nonzero integer multiple of `y`; the zero multiple is ruled
out by original validity.  This gives an exact supported-witness criterion on
an embedded subtuple and a general transversal descent theorem.

For the pure-star torsion certificate, the quotient keeps the same two-adic
factor and strictly lowers the odd factor from `q` to `q / addOrderOf y`.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafOddPrimary
import MinModulus.G1SubtupleWitnessKernel

namespace MinModulus

open Finset

variable {n k : ℕ} {G : Type*} [AddCommGroup G]

/-- Exact witness kernel for quotienting by an arbitrary cyclic subgroup.
Original validity removes the zero lift, leaving precisely witnesses at
nonzero multiples of the generator. -/
theorem zeroWitness_quotient_zmultiples_iff_exists_nonzero_zsmulWitness
    (g : Fin n → G) (hg : ValidTuple g) (y : G) (c : Fin n → ℤ) :
    Witness (fun i ↦ QuotientAddGroup.mk'
      (AddSubgroup.zmultiples y) (g i)) 0 c ↔
      ∃ z : ℤ, z • y ≠ 0 ∧ Witness g (z • y) c := by
  constructor
  · intro hc
    have hmem : (∑ i, c i • g i) ∈
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)).ker := by
      rw [AddMonoidHom.mem_ker, map_sum]
      rw [Finset.sum_congr rfl fun i _ ↦
        map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (c i) (g i)]
      exact hc.2.2.2
    rw [QuotientAddGroup.ker_mk'] at hmem
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hzne : z • y ≠ 0 := by
      intro hzero
      exact (validTuple_iff_no_zero_witness g).mp hg c
        ⟨hc.1, hc.2.1, hc.2.2.1, by rw [← hz, hzero]⟩
    exact ⟨z, hzne, hc.1, hc.2.1, hc.2.2.1, hz.symm⟩
  · rintro ⟨z, _hzne, hc⟩
    have hmap := witness_map_addMonoidHom
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) g hc
    have hzker :
        QuotientAddGroup.mk' (AddSubgroup.zmultiples y) (z • y) = 0 := by
      rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, rfl⟩
    rw [hzker] at hmap
    exact hmap

/-- Embedded version: downstairs zero witnesses are exactly zero extensions
of original witnesses at a nonzero multiple of the quotient generator. -/
theorem embedded_zeroWitness_quotient_zmultiples_iff
    (e : Fin k ↪ Fin n) (g : Fin n → G) (hg : ValidTuple g)
    (y : G) (c : Fin k → ℤ) :
    Witness (fun i ↦ QuotientAddGroup.mk'
      (AddSubgroup.zmultiples y) (g (e i))) 0 c ↔
      ∃ z : ℤ, z • y ≠ 0 ∧
        Witness g (z • y) (Function.extend e c (fun _ ↦ 0)) := by
  rw [zeroWitness_quotient_zmultiples_iff_exists_nonzero_zsmulWitness
    (fun i ↦ g (e i)) (validTuple_embedding e g hg) y c]
  constructor
  · rintro ⟨z, hz, hc⟩
    exact ⟨z, hz, (witness_extend_embedding_iff e g c).2 hc⟩
  · rintro ⟨z, hz, hc⟩
    exact ⟨z, hz, (witness_extend_embedding_iff e g c).1 hc⟩

/-- Exact validity criterion for a retained subtuple in the cyclic quotient:
there must be no supported original witness at any nonzero kernel value. -/
theorem validTuple_quotient_zmultiples_iff_no_supported_nonzeroWitness
    (e : Fin k ↪ Fin n) (g : Fin n → G) (hg : ValidTuple g) (y : G) :
    ValidTuple (fun i ↦ QuotientAddGroup.mk'
      (AddSubgroup.zmultiples y) (g (e i))) ↔
      ∀ c : Fin k → ℤ, ∀ z : ℤ, z • y ≠ 0 →
        ¬ Witness g (z • y) (Function.extend e c (fun _ ↦ 0)) := by
  rw [validTuple_iff_no_zero_witness]
  constructor
  · intro hvalid c z hz hc
    exact hvalid c ((embedded_zeroWitness_quotient_zmultiples_iff
      e g hg y c).2 ⟨z, hz, hc⟩)
  · intro hno c hc
    obtain ⟨z, hz, hc'⟩ :=
      (embedded_zeroWitness_quotient_zmultiples_iff e g hg y c).1 hc
    exact hno c z hz hc'

/-- A deleted-coordinate transversal for every witness at every nonzero
element of the cyclic kernel. -/
def CyclicKernelWitnessTransversal
    (g : Fin n → G) (y : G) (e : Fin k ↪ Fin n) : Prop :=
  ∀ z : ℤ, z • y ≠ 0 → ∀ c : Fin n → ℤ,
    Witness g (z • y) c →
    ∃ j : Fin n, (∀ i : Fin k, e i ≠ j) ∧ c j ≠ 0

/-- Hitting every nonzero cyclic-kernel witness outside the retained image
makes the retained quotient tuple valid. -/
theorem quotient_valid_of_cyclicKernelWitnessTransversal
    (g : Fin n → G) (hg : ValidTuple g) (y : G)
    (e : Fin k ↪ Fin n)
    (hhit : CyclicKernelWitnessTransversal g y e) :
    ValidTuple (fun i ↦ QuotientAddGroup.mk'
      (AddSubgroup.zmultiples y) (g (e i))) := by
  rw [validTuple_quotient_zmultiples_iff_no_supported_nonzeroWitness
    e g hg y]
  intro c z hz hc
  obtain ⟨j, hjout, hjne⟩ := hhit z hz _ hc
  apply hjne
  exact Function.extend_apply' c (fun _ ↦ 0) j (by
    rintro ⟨i, hi⟩
    exact hjout i hi)

/-- Quotienting by `zmultiples y` divides the finite group order by the
additive order of `y`. -/
theorem nat_card_quotient_zmultiples_mul_addOrderOf
    [Finite G] (y : G) :
    Nat.card (G ⧸ AddSubgroup.zmultiples y) * addOrderOf y = Nat.card G := by
  rw [← Nat.card_zmultiples]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

/-- A quotient of `ZMod N` by the subgroup generated by `y` is explicitly
the cyclic group of order `N / addOrderOf y`. -/
noncomputable def quotZModZMultiplesEquivZModDivOrder
    {N : ℕ} [NeZero N] (y : ZMod N) :
    (ZMod N ⧸ AddSubgroup.zmultiples y) ≃+
      ZMod (N / addOrderOf y) := by
  letI : IsAddCyclic (ZMod N ⧸ AddSubgroup.zmultiples y) :=
    isAddCyclic_of_surjective
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
      (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples y))
  have hmul : Nat.card (ZMod N ⧸ AddSubgroup.zmultiples y) *
      addOrderOf y = N := by
    simpa only [Nat.card_zmod] using
      nat_card_quotient_zmultiples_mul_addOrderOf y
  have hcard : Nat.card (ZMod N ⧸ AddSubgroup.zmultiples y) =
      N / addOrderOf y := by
    exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos y) hmul.symm).symm
  exact (zmodAddEquivOfGenerator
    IsAddCyclic.exists_generator.choose_spec hcard).symm

/-- Operational cyclic descent at the exact quotient modulus. -/
theorem admitsValidTuple_div_addOrderOf_of_cyclicKernelTransversal
    {N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (y : ZMod N) (e : Fin k ↪ Fin n)
    (hhit : CyclicKernelWitnessTransversal g y e) :
    AdmitsValidTuple k (N / addOrderOf y) := by
  have hq := quotient_valid_of_cyclicKernelWitnessTransversal
    g hg y e hhit
  let equiv := quotZModZMultiplesEquivZModDivOrder y
  exact ⟨_, validTuple_comp hq equiv.toAddMonoidHom equiv.injective⟩

/-- The odd-primary subgroup quotient preserves the two-adic factor. -/
theorem MersenneTorsionPrimeCertificate.quotientModulus_eq
    {t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y) :
    (2 ^ t * q) / addOrderOf y =
      2 ^ t * (q / addOrderOf y) := by
  exact Nat.mul_div_assoc (2 ^ t) hcert.torsionOrder_dvd_oddFactor

/-- The actual nontrivial torsion subgroup strictly reduces the odd factor. -/
theorem MersenneTorsionPrimeCertificate.oddFactorQuotient_lt
    {t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y) :
    q / addOrderOf y < q := by
  have htwo := hcert.two_le_torsionOrder
  have hle := hcert.torsionOrder_le_oddFactor
  exact Nat.div_lt_self (by omega) (by omega)

/-- Once a cyclic-kernel witness transversal is supplied, the pure-star
odd-primary residual descends to a valid tuple with the same two-adic factor
and a strictly smaller odd factor. -/
theorem MersenneTorsionPrimeCertificate.admitsValidTuple_oddFactorQuotient
    {t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (e : Fin k ↪ Fin n)
    (hhit : CyclicKernelWitnessTransversal g y e) :
    AdmitsValidTuple k (2 ^ t * (q / addOrderOf y)) := by
  have hdesc := admitsValidTuple_div_addOrderOf_of_cyclicKernelTransversal
    g hg y e hhit
  rwa [hcert.quotientModulus_eq] at hdesc

end MinModulus
