/-
# Excluding a half witness trapped in a zero-zero-two quarter pair

For the `(0,0,2)` profile, a half witness supported inside the four
coordinates of the balanced quarter pair would have to omit both negative
quarter coordinates.  Then twice the quarter vector minus that half witness
is an admissible nonzero witness at zero, contradicting validity.
-/
import MinModulus.G1ProtectedQuarterDescent

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- If `q` is a witness at `t` and `c` a witness at `2t`, then `2q-c` is a
zero witness whenever its coefficient floor is admissible and it is nonzero. -/
theorem witness_twice_sub_at_zero
    (g : Fin m → G) {t : G} {q c : Fin m → ℤ}
    (hq : Witness g t q) (hc : Witness g (t + t) c)
    (hne : q + q - c ≠ 0)
    (hfloor : ∀ i, -1 ≤ (q + q - c) i) :
    Witness g 0 (q + q - c) := by
  refine ⟨hne, hfloor, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.add_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hq.2.2.1, hc.2.2.1]
    omega
  · have hterm : ∀ i, (q + q - c) i • g i =
        q i • g i + q i • g i - c i • g i := by
      intro i
      simp only [Pi.sub_apply, Pi.add_apply, add_smul, sub_smul]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hq.2.2.2, hc.2.2.2, sub_self]

/-- The support of a balanced pair with four distinct coordinates is exactly
those four coordinates. -/
theorem coefficientSupport_balancedPairCoeffs
    (x y a b : Fin m) (hxy : x ≠ y) (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    coefficientSupport (balancedPairCoeffs x y a b) = {x, y, a, b} := by
  ext i
  simp only [mem_coefficientSupport_iff, mem_insert, mem_singleton]
  simp only [balancedPairCoeffs]
  constructor
  · contrapose!
    rintro ⟨hix, hiy, hia, hib⟩
    simp [hix, hiy, hia, hib]
  · intro hi
    rcases hi with hix | hiy | hia | hib
    · subst i
      simp [hxy, hxa, hxb]
    · subst i
      simp [Ne.symm hxy, hya, hyb]
    · subst i
      simp [Ne.symm hxa, Ne.symm hya, hab]
    · subst i
      simp [Ne.symm hxb, Ne.symm hyb, Ne.symm hab]

/-- A `(0,0,2)` triangle exposes its heavy pure edge and a protected balanced
quarter pair on the same two endpoints.  Retaining this shared geometry is
essential when a later support transversal is compared with the pure edge. -/
theorem exactTriangleZeroZeroTwo_protectedPureEdge_quarterPair
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    ∃ t : G, ∃ x y a b d : Fin m, ∃ c : Fin m → ℤ,
      x ≠ y ∧ a ≠ b ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      d ≠ a ∧ d ≠ b ∧
      Witness g h c ∧
      (∀ i, c i = -1 ↔ i = a ∨ i = b) ∧ c d = 2 ∧
      c = pureEdgeCoeffs d a b ∧
      t + t = h ∧
      Witness g t (balancedPairCoeffs x y a b) ∧
      ∀ c : Fin m → ℤ, Witness g h c →
        (∀ i : Fin m, balancedPairCoeffs x y a b i = 0 → c i = 0) →
        False := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
  obtain ⟨x, hxb, hxd, hxa, hBDx, _hBDzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcBD hcDA b d a hbd hab hBD hDA hBDa
  obtain ⟨y, hyd, hya, hyb, hDAy, _hDAzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcDA hcAB d a b hda hbd hDA hAB hDAb
  have hxy : x ≠ y := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcBD hcDA b d a x y hbd hda hab hBD hDA
      hxb hxd hyd hya hBDx hDAy
  let t : G := g x + g y - g a - g b
  let q : Fin m → ℤ := balancedPairCoeffs x y a b
  have ht : t + t = h := by
    have hraw := double_balanced_center_sum_eq_target_of_pure_triangle
      g hh hcAB hcBD hcDA a b d d x y hab hbd hda hAB hBD hDA
        hda (Ne.symm hbd) hxb hxd hyd hya hABd hBDx hDAy
    calc
      t + t =
          (g d + g x + g y - g a - g b - g d) +
            (g d + g x + g y - g a - g b - g d) := by
              simp only [t]
              abel
      _ = h := hraw
  have hq : Witness g t q :=
    balancedPairCoeffs_witness g x y a b hxy hab hxa hxb hya hyb rfl
  have hcABpure : cAB = pureEdgeCoeffs d a b :=
    exactPair_coeff_two_eq_pureEdgeCoeffs
      g hcAB a b d hab hAB hda (Ne.symm hbd) hABd
  refine ⟨t, x, y, a, b, d, cAB,
    hxy, hab, hxa, hxb, hya, hyb, hda, Ne.symm hbd,
    hcAB, hAB, hABd, hcABpure, ht, hq, ?_⟩
  intro c hc hsupp
  have hqd : q d = 0 := by
    simp [q, balancedPairCoeffs, Ne.symm hxd, Ne.symm hyd, hda,
      Ne.symm hbd]
  have hcd : c d = 0 := hsupp d hqd
  have hcb : c b = -1 := by
    by_contra hcbne
    have hshare : ∀ i, ¬ (c i = -1 ∧ cBD i = -1) := by
      intro i hi
      rcases (hBD i).1 hi.2 with hib | hid
      · exact hcbne (hib ▸ hi.1)
      · subst i
        omega
    have hneg := witness_combination g hg hh hc hcBD hshare
    have hd := congrFun hneg d
    have hcBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
    simp only [Pi.neg_apply, hcBDd, hcd] at hd
    omega
  have hca : c a = -1 := by
    by_contra hcan
    have hshare : ∀ i, ¬ (c i = -1 ∧ cDA i = -1) := by
      intro i hi
      rcases (hDA i).1 hi.2 with hid | hia
      · subst i
        omega
      · exact hcan (hia ▸ hi.1)
    have hneg := witness_combination g hg hh hc hcDA hshare
    have hd := congrFun hneg d
    have hcDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
    simp only [Pi.neg_apply, hcDAd, hcd] at hd
    omega
  have hsparse : ∀ i : Fin m,
      i ≠ x → i ≠ y → i ≠ a → i ≠ b → c i = 0 := by
    intro i hix hiy hia hib
    apply hsupp i
    simp [balancedPairCoeffs, hix, hiy, hia, hib]
  have hsum4 : c x + c y + c a + c b = 0 := by
    have hsum_eq : (∑ i, c i) = c x + c y + c a + c b := by
      calc
        (∑ i, c i) = ∑ i ∈ ({x, y, a, b} : Finset (Fin m)), c i := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          apply hsparse i
          · intro hix
            exact hi (by simp [hix])
          · intro hiy
            exact hi (by simp [hiy])
          · intro hia
            exact hi (by simp [hia])
          · intro hib
            exact hi (by simp [hib])
        _ = c x + c y + c a + c b := by
          simp [hxy, hab, hxa, hxb, hya, hyb]
          ring
    rw [hc.2.2.1] at hsum_eq
    omega
  have hcxle : c x ≤ 3 := by
    have hcyge := hc.2.1 y
    omega
  have hcyle : c y ≤ 3 := by
    have hcxge := hc.2.1 x
    omega
  have hne : q + q - c ≠ 0 := by
    intro hz
    have hqa' : q a = -1 := by
      simp [q, balancedPairCoeffs, Ne.symm hxa, Ne.symm hya, hab]
    have ha := congrFun hz a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, hqa', hca] at ha
    omega
  have hfloor : ∀ i, -1 ≤ (q + q - c) i := by
    intro i
    by_cases hix : i = x
    · subst i
      simp [q, balancedPairCoeffs, hxy, hxa, hxb]
      omega
    by_cases hiy : i = y
    · subst i
      simp [q, balancedPairCoeffs, Ne.symm hxy, hya, hyb]
      omega
    by_cases hia : i = a
    · subst i
      simp [q, balancedPairCoeffs, Ne.symm hxa, Ne.symm hya, hab, hca]
    by_cases hib : i = b
    · subst i
      simp [q, balancedPairCoeffs, Ne.symm hxb, Ne.symm hyb,
        Ne.symm hab, hcb]
    have hci := hsparse i hix hiy hia hib
    simp [q, balancedPairCoeffs, hix, hiy, hia, hib, hci]
  have hc' : Witness g (t + t) c := by
    rwa [ht]
  exact (validTuple_iff_no_zero_witness g).mp hg (q + q - c)
    (witness_twice_sub_at_zero g hq hc' hne hfloor)

/-- Compatibility projection of the richer shared-geometry theorem: a half
witness cannot be supported entirely inside the protected quarter pair. -/
theorem exactTriangleZeroZeroTwo_no_halfWitness_supportedOn_quarterPair
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    ∃ t : G, ∃ x y a b : Fin m,
      x ≠ y ∧ a ≠ b ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      t + t = h ∧
      Witness g t (balancedPairCoeffs x y a b) ∧
      ∀ c : Fin m → ℤ, Witness g h c →
        (∀ i : Fin m, balancedPairCoeffs x y a b i = 0 → c i = 0) →
        False := by
  obtain ⟨t, x, y, a, b, _d, _c,
    hxy, hab, hxa, hxb, hya, hyb, _hda, _hdb,
    _hc, _homit, _hcd, _hpure, ht, hq, hkernel⟩ :=
    exactTriangleZeroZeroTwo_protectedPureEdge_quarterPair
      g hg hh hprofile
  exact ⟨t, x, y, a, b, hxy, hab, hxa, hxb, hya, hyb,
    ht, hq, hkernel⟩

/-- Cyclic consequence: the `(0,0,2)` profile always yields a valid recursive
four-coordinate tuple carrying the transported quarter pair as a half
witness. -/
theorem exactTriangleZeroZeroTwo_recursiveFourTuple
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g (M : ZMod N)) :
    AdmitsValidTupleWithWitness 4 M (K : ZMod M) := by
  obtain ⟨t, x, y, a, b, hxy, hab, hxa, hxb, hya, hyb,
    ht, hq, hno⟩ :=
    exactTriangleZeroZeroTwo_no_halfWitness_supportedOn_quarterPair
      g hg (half_add_half hN) hprofile
  rcases quarterWitness_recursive_or_halfWitness_supported
      hN hM hK g hg ht hq with hrec | hsupported
  · have hsupp : coefficientSupport (balancedPairCoeffs x y a b) =
        {x, y, a, b} :=
      coefficientSupport_balancedPairCoeffs x y a b
        hxy hab hxa hxb hya hyb
    have hcard : (coefficientSupport
        (balancedPairCoeffs x y a b)).card = 4 := by
      rw [hsupp]
      simp [hxy, hab, hxa, hxb, hya, hyb]
    simpa [hcard] using hrec
  · obtain ⟨c, hc, hsupp⟩ := hsupported
    exact False.elim (hno c hc hsupp)

end MinModulus
