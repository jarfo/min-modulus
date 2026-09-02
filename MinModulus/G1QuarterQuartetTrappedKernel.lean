/-
# Excluding a half witness trapped in an all-zero quarter-pair layer

One pair layer of the all-zero quarter quartet is supported away from an
original triangle edge.  A half witness trapped in that four-coordinate
support would share no omission with the pure half witness on the omitted
edge, so witness combination would identify them up to sign, immediately
contradicting the zero coefficients on that edge.
-/
import MinModulus.G1QuarterPairTrappedKernel

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- An all-zero triangle contains a balanced quarter-pair layer whose
four-coordinate support contains no half witness. -/
theorem exactTriangleAllZero_no_halfWitness_supportedOn_quarterPair
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hall : WitnessExactTriangleAllZero g h) :
    ∃ t : G, ∃ x d y z : Fin m,
      x ≠ d ∧ y ≠ z ∧
      x ≠ y ∧ x ≠ z ∧ d ≠ y ∧ d ≠ z ∧
      t + t = h ∧
      Witness g t (balancedPairCoeffs x d y z) ∧
      ∀ c : Fin m → ℤ, Witness g h c →
        (∀ i : Fin m, balancedPairCoeffs x d y z i = 0 → c i = 0) →
        False := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hAB0, hBD0, hDA0⟩ := hall
  obtain ⟨x, y, z, t, hx, hy, hz, hxy, hyz, hzx,
    _hABx, _hBDy, _hDAz, ht,
    _hc0, _h0, hc1, _h1, _hc2, _h2, _hc3, _h3,
    _hsumAB, _hsumBD, _hsumDA⟩ :=
    exists_light_quarterWitness_quartet_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hAB0 hBD0 hDA0
  refine ⟨t, x, d, y, z, hx.2.2, hyz, hxy, Ne.symm hzx,
    Ne.symm hy.2.1, Ne.symm hz.1, ht, hc1, ?_⟩
  intro c hc hsupp
  have hqa : balancedPairCoeffs x d y z a = 0 := by
    simp [balancedPairCoeffs, Ne.symm hx.1, Ne.symm hda,
      Ne.symm hy.2.2, Ne.symm hz.2.1]
  have hqb : balancedPairCoeffs x d y z b = 0 := by
    simp [balancedPairCoeffs, Ne.symm hx.2.1, hbd,
      Ne.symm hy.1, Ne.symm hz.2.2]
  have hca : c a = 0 := hsupp a hqa
  have hcb : c b = 0 := hsupp b hqb
  have hshare : ∀ i, ¬ (c i = -1 ∧ cAB i = -1) := by
    intro i hi
    rcases (hAB i).1 hi.2 with hia | hib
    · subst i
      omega
    · subst i
      omega
  have hneg := witness_combination g hg hh hc hcAB hshare
  have ha := congrFun hneg a
  have hcABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  simp only [Pi.neg_apply, hcABa, hca] at ha
  omega

/-- Cyclic consequence: the all-zero profile also always yields a valid
recursive four-coordinate tuple carrying a transported quarter-pair witness. -/
theorem exactTriangleAllZero_recursiveFourTuple
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hall : WitnessExactTriangleAllZero g (M : ZMod N)) :
    AdmitsValidTupleWithWitness 4 M (K : ZMod M) := by
  obtain ⟨t, x, d, y, z, hxd, hyz, hxy, hxz, hdy, hdz,
    ht, hq, hno⟩ :=
    exactTriangleAllZero_no_halfWitness_supportedOn_quarterPair
      g hg (half_add_half hN) hall
  rcases quarterWitness_recursive_or_halfWitness_supported
      hN hM hK g hg ht hq with hrec | hsupported
  · have hsupp : coefficientSupport (balancedPairCoeffs x d y z) =
        {x, d, y, z} :=
      coefficientSupport_balancedPairCoeffs x d y z
        hxd hyz hxy hxz hdy hdz
    have hcard : (coefficientSupport
        (balancedPairCoeffs x d y z)).card = 4 := by
      rw [hsupp]
      simp [hxd, hyz, hxy, hxz, hdy, hdz]
    simpa [hcard] using hrec
  · obtain ⟨c, hc, hsupp⟩ := hsupported
    exact False.elim (hno c hc hsupp)

end MinModulus
