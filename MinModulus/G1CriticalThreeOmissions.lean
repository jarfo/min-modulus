/-
# The critical even-step frontier is common touch or three omissions

Below `2^(m+1)`, subset-sum overlap supplies a half-witness light away from
any chosen anchor.  Under failure of common touch and absence of three
omissions, the complete pure-edge family is a triangle.  A pure triangle
forbids a globally light half-witness, so changing the anchor forces a pure
edge centered at each triangle vertex.  Same-pair center rigidity then
forces all three opposite coefficients to be two, an existing contradiction.

This is independent of G2 and applies in every dimension and even stratum.
Only the three-omission deletion obligation remains on this G1 route.
-/
import MinModulus.G1PureStarElimination
import MinModulus.G1SubtupleWitnessKernel

namespace MinModulus

open Finset

/-- Transport a witness back along a coordinate permutation. -/
theorem witness_reindex_perm
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (e : Equiv.Perm (Fin n))
    {h : G} {c : Fin n → ℤ} (hc : Witness (fun i ↦ g (e i)) h c) :
    Witness g h (fun i ↦ c (e.symm i)) := by
  refine ⟨?_, fun i ↦ hc.2.1 _, ?_, ?_⟩
  · intro hz
    apply hc.1
    funext i
    have := congrFun hz (e i)
    simpa using this
  · exact (Equiv.sum_comp e.symm c).trans hc.2.2.1
  · have heq := Equiv.sum_comp e.symm (fun i ↦ c i • g (e i))
    simpa using heq.trans hc.2.2.2

/-- The cube-overlap half-witness can be made light away from any anchor,
not only the distinguished coordinate zero. -/
theorem exists_half_witness_light_off_anchor_of_lt_two_pow
    {m N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2 ^ (m + 1)) (r : Fin (m + 1)) :
    ∃ c : Fin (m + 1) → ℤ, Witness g (M : ZMod N) c ∧
      ∀ i, i ≠ r → c i ≤ 1 := by
  let e := Equiv.swap (0 : Fin (m + 1)) r
  have hg' : ValidTuple (fun i ↦ g (e i)) :=
    validTuple_embedding e.toEmbedding g hg
  obtain ⟨c, hc, hlight⟩ := exists_light_half_witness_of_lt_two_pow
    hN hM (fun i ↦ g (e i)) hg' hsmall
  refine ⟨fun i ↦ c (e.symm i), witness_reindex_perm g e hc, ?_⟩
  intro i hir
  have hne : e.symm i ≠ 0 := by
    intro heq
    have := congrArg e heq
    apply hir
    simpa [e] using this
  exact Fin.cases (motive := fun j ↦ j ≠ 0 → c j ≤ 1)
    (fun hz ↦ False.elim (hz rfl))
    (fun j _ ↦ (hlight j).2) (e.symm i) hne

/-- A pure omission triangle forbids a globally light half-witness: both
the witness and its negative would have to alternate signs on an odd cycle. -/
theorem exists_heavy_coefficient_of_pure_triangle
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    {cAB cBD cDA c : Fin (m + 1) → ℤ}
    (hcAB : Witness g h cAB) (hcBD : Witness g h cBD)
    (hcDA : Witness g h cDA) (hc : Witness g h c)
    (a b d eAB eBD eDA : Fin (m + 1))
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (htAB : cAB eAB = 2) (htBD : cBD eBD = 2) (htDA : cDA eDA = 2) :
    ∃ e, 2 ≤ c e := by
  by_contra hnone
  have hlight : ∀ i, c i ≤ 1 := by
    intro i
    have := not_exists.mp hnone i
    omega
  have hcneg := witness_neg_of_le_one g hh hc hlight
  have hsign (p q e : Fin (m + 1)) (row : Fin (m + 1) → ℤ)
      (hrow : Witness g h row)
      (homit : ∀ i, row i = -1 ↔ i = p ∨ i = q) (htwo : row e = 2) :
      (c p = -1 ∨ c q = -1) ∧ (c p = 1 ∨ c q = 1) := by
    obtain ⟨x, hx, hcx, _⟩ := witness_exists_shared_pureEdge_endpoint
      g hg hh hc hrow p q e homit htwo
    obtain ⟨y, hy, hcy, _⟩ := witness_exists_shared_pureEdge_endpoint
      g hg hh hcneg hrow p q e homit htwo
    simp only [Pi.neg_apply] at hcy
    constructor
    · rcases hx with rfl | rfl <;> omega
    · rcases hy with rfl | rfl <;> omega
  have hab := hsign a b eAB cAB hcAB hAB htAB
  have hbd := hsign b d eBD cBD hcBD hBD htBD
  have hda := hsign d a eDA cDA hcDA hDA htDA
  omega

/-- Without common touch or three omissions, an exact-pair avoider forces
a heavy coefficient and hence makes the complete pure-edge family nonempty. -/
theorem pureEdgeFamily_nonempty_of_no_common_of_no_three
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h) :
    (witnessPureEdgeOmissionPairs g h).Nonempty := by
  classical
  let c := supportAvoidingWitnessAt g hno 0
  have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno 0
  obtain ⟨p, hcp⟩ : ∃ p, c p = -1 := by
    by_contra hn
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ c i := by
      intro i _
      have := hc.2.1 i
      have := not_exists.mp hn i
      omega
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hc.2.2.1
    exact hc.1 (funext fun i ↦ hz i (Finset.mem_univ i))
  obtain ⟨q, hcq, hpq⟩ : ∃ q, c q = -1 ∧ p ≠ q := by
    by_contra hn
    apply hno
    refine ⟨p, common_touched_of_unique_omission g hg hh hc p hcp ?_⟩
    intro i hi
    by_contra hip
    exact hn ⟨i, hi, Ne.symm hip⟩
  have hexact : ∀ i, c i = -1 ↔ i = p ∨ i = q := by
    rcases exactPairOmissions_or_threeDistinctOmissions g hc hpq hcp hcq with
      hexact | hbad
    · exact hexact
    · exact False.elim (hthree hbad)
  let f := supportAvoidingWitnessAt g hno q
  have hf : Witness g h f := supportAvoidingWitnessAt_isWitness g hno q
  have hfq : f q = 0 := supportAvoidingWitnessAt_eq_zero g hno q
  have hfp := omitted_other_of_zero_at_exact_pair g hg hh hc hf p q hexact hfq
  obtain ⟨e, he⟩ := exists_coeff_ge_two_of_omit_other_and_zero_at_exact_pair
    g hg hh hc hf p q hexact hfp hfq
  exact witnessPureEdgeOmissionPairs_nonempty_of_heavy_of_no_three g hthree hf he

/-- Every valid even-modulus tuple below the full cube threshold has common
touch or a three-omission half-witness.  No odd-stratum hypothesis is used. -/
theorem commonTouched_or_threeOmissions_of_lt_two_pow
    {m N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2 ^ (m + 1)) :
    (∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g (M : ZMod N) c → c z ≠ 0) ∨
      WitnessThreeDistinctOmissions g (M : ZMod N) := by
  classical
  by_cases hno : ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g (M : ZMod N) c → c z ≠ 0
  · exact Or.inl hno
  right
  by_contra hthree
  let h : ZMod N := M
  have hh : h + h = 0 := half_add_half hN
  have hne : h ≠ 0 := half_ne_zero hN hM
  have hunique : ∀ u : ZMod N, u + u = 0 → u = 0 ∨ u = h :=
    fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu
  let F := witnessPureEdgeOmissionPairs g h
  have hF : F.Nonempty := pureEdgeFamily_nonempty_of_no_common_of_no_three
    g hg hh hno hthree
  have hcard : ∀ P ∈ F, P.card = 2 := by
    intro P hP
    exact (mem_witnessPureEdgeOmissionPairs_iff g h P).1 hP |>.1
  have hinter : ∀ P ∈ F, ∀ Q ∈ F, (P ∩ Q).Nonempty := by
    intro P hP Q hQ
    exact witnessPureEdgeOmissionPairs_pairwise_inter g hg hh hP hQ
  rcases pairwiseInter_cardTwo_common_or_triangle F hF hcard hinter with
    ⟨r, hstar⟩ | ⟨a, b, d, hab, hbd, hda, hAB, hBD, hDA, hsubset⟩
  · exact hthree (globalPureEdgeStar_threeDistinctOmissions_of_no_common_touched
      g hg hh hno r hstar hF)
  obtain ⟨_, cAB, eAB, hcAB, hoAB, htAB⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h {a, b}).1 hAB
  obtain ⟨_, cBD, eBD, hcBD, hoBD, htBD⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h {b, d}).1 hBD
  obtain ⟨_, cDA, eDA, hcDA, hoDA, htDA⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h {d, a}).1 hDA
  have hoAB' : ∀ i, cAB i = -1 ↔ i = a ∨ i = b := fun i ↦ by simpa using hoAB i
  have hoBD' : ∀ i, cBD i = -1 ↔ i = b ∨ i = d := fun i ↦ by simpa using hoBD i
  have hoDA' : ∀ i, cDA i = -1 ↔ i = d ∨ i = a := fun i ↦ by simpa using hoDA i
  have hhead : ∀ r : Fin (m + 1), ∃ c : Fin (m + 1) → ℤ,
      Witness g h c ∧ c r = 2 := by
    intro r
    obtain ⟨c, hc, hlight⟩ :=
      exists_half_witness_light_off_anchor_of_lt_two_pow hN hM g hg hsmall r
    obtain ⟨e, he⟩ := exists_heavy_coefficient_of_pure_triangle g hg hh
      hcAB hcBD hcDA hc a b d eAB eBD eDA hoAB' hoBD' hoDA' htAB htBD htDA
    have her : e = r := by
      by_contra her
      have := hlight e her
      omega
    subst e
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates g hc
      (show c r ≠ -1 by omega)
    have hbound := card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
      g hthree c hc
    exact ⟨c, hc, by omega⟩
  have hopposite (p q r e : Fin (m + 1)) (row : Fin (m + 1) → ℤ)
      (hrow : Witness g h row) (hpq : p ≠ q)
      (homit : ∀ i, row i = -1 ↔ i = p ∨ i = q) (htwo : row e = 2)
      (honly : ∀ P ∈ F, r ∉ P → P = {p, q}) : row r = 2 := by
    obtain ⟨c, hc, hcr⟩ := hhead r
    have hbound := card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
      g hthree c hc
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates g hc
      (show c r ≠ -1 by omega)
    have hcardEq : (witnessOmissionCoordinates c).card = 2 := by omega
    have hmem : witnessOmissionCoordinates c ∈ F :=
      (mem_witnessPureEdgeOmissionPairs_iff g h _).2
        ⟨hcardEq, c, r, hc, witnessOmissionCoordinates_exact c, hcr⟩
    have hrnot : r ∉ witnessOmissionCoordinates c := by
      simp [witnessOmissionCoordinates, hcr]
    have hpair := honly _ hmem hrnot
    have homitC : ∀ i, c i = -1 ↔ i = p ∨ i = q := by
      intro i
      simpa [hpair] using witnessOmissionCoordinates_exact c i
    have hrp : r ≠ p := by intro heq; have := (homitC r).2 (Or.inl heq); omega
    have hrq : r ≠ q := by intro heq; have := (homitC r).2 (Or.inr heq); omega
    have hep : e ≠ p := by intro heq; have := (homit e).2 (Or.inl heq); omega
    have heq : e ≠ q := by intro heq; have := (homit e).2 (Or.inr heq); omega
    have hcenter := exactPair_coeffTwo_centers_eq_of_no_common_touched
      g hg hh hne hunique hno hc hrow p q r e hpq hrp hrq hep heq homitC homit hcr htwo
    simpa [hcenter] using htwo
  have hopAB : cAB d = 2 := hopposite a b d eAB cAB hcAB hab hoAB' htAB (by
    intro P hP hdP
    have := hsubset hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · rfl
    · exact False.elim (hdP (by simp))
    · exact False.elim (hdP (by simp)))
  have hopBD : cBD a = 2 := hopposite b d a eBD cBD hcBD hbd hoBD' htBD (by
    intro P hP haP
    have := hsubset hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact False.elim (haP (by simp))
    · rfl
    · exact False.elim (haP (by simp)))
  have hopDA : cDA b = 2 := hopposite d a b eDA cDA hcDA hda hoDA' htDA (by
    intro P hP hbP
    have := hsubset hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact False.elim (hbP (by simp))
    · exact False.elim (hbP (by simp))
    · rfl)
  exact not_triangle_all_opposites_two g hh hne hcAB hcBD hcDA
    a b d hab hbd hda hoAB' hoBD' hoDA' hopAB hopBD hopDA

/-- The sole remaining deletion obligation on the new critical G1 route.
This is a conjectural input, not a proved deletion theorem. -/
def CriticalThreeOmissionDeleteStep : Prop :=
  ∀ {n s q : ℕ}, Odd q →
    ∀ g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q),
      ValidTuple g →
      2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) →
      AdmitsValidTuple n (2 ^ s * q)

/-- Rejoin the common-touch/three-omission frontier to the existing
critical deletion interface, in all dimensions and strata. -/
theorem criticalRangeDeleteStep_of_threeOmissions
    (hthreeDelete : CriticalThreeOmissionDeleteStep) : CriticalRangeDeleteStep := by
  intro n s q hq hcritical hvalid
  obtain ⟨g, hg⟩ := hvalid
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1)) (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hsmall : 2 ^ (s + 1) * q < 2 ^ (n + 1) :=
    hcritical.trans_le (Nat.sub_le _ _)
  rcases commonTouched_or_threeOmissions_of_lt_two_pow hN hM g hg hsmall with
    ⟨j, hj⟩ | hthree
  · exact exists_validTuple_half_of_delete hN hM hg j hj
  · exact hthreeDelete hq g hg hcritical hthree

/-- Shortened sufficient route to Conjecture 1.  Three-omission deletion,
G2, and G3 remain explicit unproved inputs.  No separate crossing, profile,
kernel, or finite-dimensional base hypothesis is required. -/
theorem global_lower_bound_of_threeOmissionDeleteStep
    (hthreeDelete : CriticalThreeOmissionDeleteStep)
    (hG2 : OddStratumLowerBound) (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_deleteStep
    (criticalRangeDeleteStep_of_threeOmissions hthreeDelete) hG2 hG3 hn hN hv

end MinModulus
