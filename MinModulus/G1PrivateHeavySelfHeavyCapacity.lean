/-
# Self-heavy private owners force ambient capacity

After the external incidence chain has been closed, the only uncontrolled
family consists of owners whose private witness is heavy at the owner itself.
These witnesses have a rigid form when fewer than three coordinates lie
outside the minimal transversal.

Indeed, privacy puts every omission outside the transversal, while the heavy
owner coefficient forces at least two omissions.  Thus, outside
three-coordinate capacity, every self-heavy witness has the same exact pair
of omissions and all of its positive mass is the coefficient two at its
owner.  Two distinct such witnesses have equal doubled owner values.  In a
group with a unique nonzero involution this gives common touch, contradicting
the avoidance hypothesis of the private-heavy residual.
-/
import MinModulus.G1PrivateHeavyTailHeavyBound

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A self-heavy owner's private witness is coefficient-heavy at the owner. -/
theorem minimalSupportPrivateSelfHeavy_ownerHeavy
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val := by
  have hspec := minimalSupportPrivateHeavyCoordinate_spec g h hmin b
  have hself :=
    (mem_minimalSupportPrivateSelfHeavyVertices_iff g h hmin b).mp hb
  rw [hself] at hspec
  exact hspec

/-- Every omission of a self-heavy private witness lies outside the minimal
support transversal. -/
theorem minimalSupportPrivateSelfHeavy_omissions_subset_compl
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ⊆
      Finset.univ \ B := by
  intro i hi
  have hci : minimalSupportPrivateWitness g h hmin b.val i = -1 := by
    simpa [witnessOmissionCoordinates] using hi
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
  intro hiB
  by_cases hib : i = b.val
  · subst i
    have hheavy := minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hb
    omega
  · have hzero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b.val hiB hib
    omega

/-- A self-heavy private witness has at least two omission coordinates. -/
theorem two_le_card_minimalSupportPrivateSelfHeavy_omissions
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    2 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card := by
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  have hheavy : 2 ≤ c b.val := by
    exact minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hb
  have hnotomit : c b.val ≠ -1 := by omega
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates
    g (minimalSupportPrivateWitness_isWitness g h hmin b.val) hnotomit
  change c b.val ≤ (O.card : ℤ) at hupper
  exact_mod_cast hheavy.trans hupper

/-- If the ambient complement is one pair, a self-heavy private witness omits
exactly that pair and has owner coefficient exactly two. -/
theorem minimalSupportPrivateSelfHeavy_exactPair_of_compl_eq_pair
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {a d : Fin (m + 1)} (had : a ≠ d)
    (hcompl : Finset.univ \ B = {a, d})
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    (∀ i, minimalSupportPrivateWitness g h hmin b.val i = -1 ↔
        i = a ∨ i = d) ∧
      minimalSupportPrivateWitness g h hmin b.val b.val = 2 := by
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  let C : Finset (Fin (m + 1)) := Finset.univ \ B
  have hOsubset : O ⊆ C := by
    exact minimalSupportPrivateSelfHeavy_omissions_subset_compl
      g h hmin hb
  have hOge : 2 ≤ O.card := by
    exact two_le_card_minimalSupportPrivateSelfHeavy_omissions
      g h hmin hb
  have hCcard : C.card = 2 := by
    dsimp [C]
    rw [hcompl]
    simp [had]
  have hOcard : O.card = 2 := by
    have hOle := Finset.card_le_card hOsubset
    omega
  have hOC : O = C :=
    Finset.eq_of_subset_of_card_le hOsubset (by omega)
  constructor
  · intro i
    calc
      c i = -1 ↔ i ∈ O := witnessOmissionCoordinates_exact c i
      _ ↔ i ∈ C := by rw [hOC]
      _ ↔ i = a ∨ i = d := by simp [C, hcompl]
  · have hheavy : 2 ≤ c b.val := by
      exact minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hb
    have hnotomit : c b.val ≠ -1 := by omega
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates
      g (minimalSupportPrivateWitness_isWitness g h hmin b.val) hnotomit
    change c b.val ≤ (O.card : ℤ) at hupper
    rw [hOcard] at hupper
    norm_num at hupper
    exact le_antisymm hupper hheavy

/-- Two distinct self-heavy owners either expose three coordinates outside
the transversal or force the G1 common-touch conclusion. -/
theorem minimalSupportPrivateSelfHeavy_pair_commonTouched_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b u : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hu : u ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hbu : b ≠ u) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
        Witness g h c → c e ≠ 0) ∨
      B.card + 3 ≤ m + 1 := by
  classical
  by_cases hcapacity : B.card + 3 ≤ m + 1
  · exact Or.inr hcapacity
  · let C : Finset (Fin (m + 1)) := Finset.univ \ B
    have hCcardLe : C.card ≤ 2 := by
      dsimp [C]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ,
        Fintype.card_fin]
      have hBcard : B.card ≤ m + 1 := by
        simpa using Finset.card_le_univ B
      omega
    have hOsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
      g h hmin hb
    have hOge := two_le_card_minimalSupportPrivateSelfHeavy_omissions
      g h hmin hb
    have hCcardGe : 2 ≤ C.card := by
      exact hOge.trans (Finset.card_le_card hOsubset)
    have hCcard : C.card = 2 := by omega
    obtain ⟨a, d, had, hcompl⟩ := Finset.card_eq_two.mp hCcard
    have hbShape := minimalSupportPrivateSelfHeavy_exactPair_of_compl_eq_pair
      g h hmin had hcompl hb
    have huShape := minimalSupportPrivateSelfHeavy_exactPair_of_compl_eq_pair
      g h hmin had hcompl hu
    have haC : a ∈ C := by rw [hcompl]; simp
    have hdC : d ∈ C := by rw [hcompl]; simp
    have haB : a ∉ B := (Finset.mem_sdiff.mp haC).2
    have hdB : d ∉ B := (Finset.mem_sdiff.mp hdC).2
    have hba : (b.val : Fin (m + 1)) ≠ a := by
      intro hba
      subst a
      exact haB b.val.property
    have hbd : (b.val : Fin (m + 1)) ≠ d := by
      intro hbd
      subst d
      exact hdB b.val.property
    have hua : (u.val : Fin (m + 1)) ≠ a := by
      intro hua
      subst a
      exact haB u.val.property
    have hud : (u.val : Fin (m + 1)) ≠ d := by
      intro hud
      subst d
      exact hdB u.val.property
    have howners : (b.val : Fin (m + 1)) ≠ u.val := by
      intro howners
      apply hbu
      apply Subtype.ext
      exact Subtype.ext howners
    have hdoubles := two_smul_eq_of_same_exact_pair_coeff_two
      g
      (minimalSupportPrivateWitness_isWitness g h hmin b.val)
      (minimalSupportPrivateWitness_isWitness g h hmin u.val)
      a d b.val u.val had hba hbd hua hud
      hbShape.1 huShape.1 hbShape.2 huShape.2
    exact Or.inl
      (common_touched_of_two_smul_eq
        g hg hh hne hunique howners hdoubles)

/-- Under the no-common-touch hypothesis of the private-heavy residual, at
most one self-heavy owner survives unless three external coordinates fit. -/
theorem card_minimalSupportPrivateSelfHeavyVertices_le_one_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyVertices g h hmin).card ≤ 1 ∨
      B.card + 3 ≤ m + 1 := by
  classical
  by_cases hcapacity : B.card + 3 ≤ m + 1
  · exact Or.inr hcapacity
  · left
    by_contra hcard
    have htwo : 1 <
        (minimalSupportPrivateSelfHeavyVertices g h hmin).card := by
      omega
    obtain ⟨b, hb, u, hu, hbu⟩ := Finset.one_lt_card.mp htwo
    rcases minimalSupportPrivateSelfHeavy_pair_commonTouched_or_capacity
        g hg h hh hne hunique hmin hb hu hbu with hcommon | hcapacity'
    · exact hno hcommon
    · exact hcapacity hcapacity'

/-- Cyclic specialization for the half-modulus target. -/
theorem card_minimalSupportPrivateSelfHeavyVertices_le_one_or_capacity_zmod
    {N M : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyVertices
        g (M : ZMod N) hmin).card ≤ 1 ∨
      B.card + 3 ≤ m + 1 := by
  exact card_minimalSupportPrivateSelfHeavyVertices_le_one_or_capacity
    g hg (M : ZMod N) (half_add_half hN) (half_ne_zero hN hM)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN x hx)
      hmin hno

end MinModulus
