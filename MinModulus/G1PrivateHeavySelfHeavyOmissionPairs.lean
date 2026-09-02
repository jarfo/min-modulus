/-
# Exact-two omission pairs of self-heavy private witnesses

The self-heavy capacity theorem leaves a regime with at least three external
coordinates.  This file retains the first rigid layer in that regime: the
self-heavy witnesses having exactly two omissions.

Each such owner determines an external two-set.  Distinct private witnesses
have intersecting omission sets.  Moreover, under no common touch and a
unique nonzero involution, two owners cannot determine the same pair: exact
positive mass would concentrate coefficient two at both owners, forcing
equality of their doubled tuple values and hence common touch.
-/
import MinModulus.G1PrivateHeavySelfHeavyCapacity

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Self-heavy private owners whose canonical witness has exactly two
omissions. -/
noncomputable def minimalSupportPrivateSelfHeavyExactTwoVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyVertices g h hmin).filter (fun b ↦
    (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card = 2)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin ↔
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin ∧
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card = 2 := by
  classical
  simp [minimalSupportPrivateSelfHeavyExactTwoVertices]

/-- The omission pair attached to one member of the exact-two layer. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionPair
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)) :
    Finset (Fin (m + 1)) :=
  witnessOmissionCoordinates
    (minimalSupportPrivateWitness g h hmin b.val.val)

/-- The finite family of exact-two omission pairs. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionPairs
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset (Finset (Fin (m + 1))) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateSelfHeavyOmissionPair g h hmin)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (P : Finset (Fin (m + 1))) :
    P ∈ minimalSupportPrivateSelfHeavyOmissionPairs g h hmin ↔
      ∃ b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin),
        minimalSupportPrivateSelfHeavyOmissionPair g h hmin b = P := by
  classical
  simp [minimalSupportPrivateSelfHeavyOmissionPairs]

/-- A self-heavy witness with an explicitly identified two-element omission
set has all positive mass concentrated as coefficient two at its owner. -/
theorem minimalSupportPrivateSelfHeavy_exactPair_of_omissions_eq_pair
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {a d : Fin (m + 1)} (had : a ≠ d)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hpair : witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) = {a, d}) :
    (∀ i, minimalSupportPrivateWitness g h hmin b.val i = -1 ↔
        i = a ∨ i = d) ∧
      minimalSupportPrivateWitness g h hmin b.val b.val = 2 := by
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  have hOcard : O.card = 2 := by
    change (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card = 2
    rw [hpair]
    simp [had]
  constructor
  · intro i
    calc
      c i = -1 ↔ i ∈ O := witnessOmissionCoordinates_exact c i
      _ ↔ i ∈ ({a, d} : Finset (Fin (m + 1))) := by
        change i ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val) ↔ _
        rw [hpair]
      _ ↔ i = a ∨ i = d := by simp
  · have hheavy : 2 ≤ c b.val :=
      minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hb
    have hnotomit : c b.val ≠ -1 := by omega
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates
      g (minimalSupportPrivateWitness_isWitness g h hmin b.val) hnotomit
    change c b.val ≤ (O.card : ℤ) at hupper
    rw [hOcard] at hupper
    norm_num at hupper
    exact le_antisymm hupper hheavy

/-- Equal omission pairs at two distinct exact-two self-heavy owners force
common touch. -/
theorem minimalSupportPrivateSelfHeavy_commonTouched_of_equal_exactTwo_omissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b u : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)
    (hu : u ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin)
    (hbu : b ≠ u)
    (heq : witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) =
      witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin u.val)) :
    ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0 := by
  classical
  have hbSpec :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin b).mp hb
  have huSpec :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin u).mp hu
  obtain ⟨a, d, had, hbPair⟩ := Finset.card_eq_two.mp hbSpec.2
  have huPair : witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin u.val) = {a, d} :=
    heq.symm.trans hbPair
  have hbShape := minimalSupportPrivateSelfHeavy_exactPair_of_omissions_eq_pair
    g h hmin had hbSpec.1 hbPair
  have huShape := minimalSupportPrivateSelfHeavy_exactPair_of_omissions_eq_pair
    g h hmin had huSpec.1 huPair
  have hOsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
    g h hmin hbSpec.1
  have haO : a ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by rw [hbPair]; simp
  have hdO : d ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by rw [hbPair]; simp
  have haB : a ∉ B := (Finset.mem_sdiff.mp (hOsubset haO)).2
  have hdB : d ∉ B := (Finset.mem_sdiff.mp (hOsubset hdO)).2
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
  exact common_touched_of_two_smul_eq
    g hg hh hne hunique howners hdoubles

/-- Under no common touch, the owner-to-omission-pair map is injective. -/
theorem minimalSupportPrivateSelfHeavyOmissionPair_injective
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    Function.Injective
      (minimalSupportPrivateSelfHeavyOmissionPair g h hmin) := by
  intro b u heq
  by_contra hbu
  have hbu' : b.val ≠ u.val := by
    intro hval
    exact hbu (Subtype.ext hval)
  apply hno
  apply minimalSupportPrivateSelfHeavy_commonTouched_of_equal_exactTwo_omissions
    g hg h hh hne hunique hmin b.property u.property hbu'
  simpa [minimalSupportPrivateSelfHeavyOmissionPair] using heq

/-- The omission-pair family has exactly as many members as the exact-two
self-heavy owner layer under no common touch. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyOmissionPairs g h hmin).card =
      (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card := by
  classical
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  let f : ↥E → Finset (Fin (m + 1)) :=
    minimalSupportPrivateSelfHeavyOmissionPair g h hmin
  change ((Finset.univ : Finset ↥E).image f).card = E.card
  calc
    ((Finset.univ : Finset ↥E).image f).card =
        (Finset.univ : Finset ↥E).card :=
      Finset.card_image_of_injective _
        (minimalSupportPrivateSelfHeavyOmissionPair_injective
          g hg h hh hne hunique hmin hno)
    _ = E.card := by simp

/-- Every member of the exact-two omission-pair family is an external
two-element set. -/
theorem minimalSupportPrivateSelfHeavyOmissionPairs_card_eq_two_and_disjoint
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {P : Finset (Fin (m + 1))}
    (hP : P ∈ minimalSupportPrivateSelfHeavyOmissionPairs g h hmin) :
    P.card = 2 ∧ Disjoint P B := by
  classical
  obtain ⟨b, rfl⟩ :=
    (mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
      g h hmin P).mp hP
  have hb :=
    (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
      g h hmin b.val).mp b.property
  constructor
  · exact hb.2
  · exact Finset.disjoint_left.mpr (fun i hiO hiB ↦
      (Finset.mem_sdiff.mp
        (minimalSupportPrivateSelfHeavy_omissions_subset_compl
          g h hmin hb.1 hiO)).2 hiB)

/-- The exact-two omission pairs form a pairwise-intersecting family. -/
theorem minimalSupportPrivateSelfHeavyOmissionPairs_pairwise_inter
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {P Q : Finset (Fin (m + 1))}
    (hP : P ∈ minimalSupportPrivateSelfHeavyOmissionPairs g h hmin)
    (hQ : Q ∈ minimalSupportPrivateSelfHeavyOmissionPairs g h hmin) :
    (P ∩ Q).Nonempty := by
  classical
  obtain ⟨b, hbP⟩ :=
    (mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
      g h hmin P).mp hP
  obtain ⟨u, huQ⟩ :=
    (mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
      g h hmin Q).mp hQ
  by_cases hbu : b.val = u.val
  · have hbu' : b = u := Subtype.ext hbu
    subst u
    rw [← hbP, ← huQ]
    have hcard :=
      (mem_minimalSupportPrivateSelfHeavyExactTwoVertices_iff
        g h hmin b.val).mp b.property |>.2
    have hpaircard :
        (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).card = 2 := by
      simpa [minimalSupportPrivateSelfHeavyOmissionPair] using hcard
    have hnonempty :
        (minimalSupportPrivateSelfHeavyOmissionPair g h hmin b).Nonempty :=
      Finset.card_pos.mp (by rw [hpaircard]; decide)
    simpa using hnonempty
  · obtain ⟨z, _, hbz, huz⟩ :=
      exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
        g hg hh hmin b.val.val u.val.val (by
          intro howners
          apply hbu
          exact Subtype.ext howners)
    refine ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← hbP]
      simpa [minimalSupportPrivateSelfHeavyOmissionPair,
        witnessOmissionCoordinates] using hbz
    · rw [← huQ]
      simpa [minimalSupportPrivateSelfHeavyOmissionPair,
        witnessOmissionCoordinates] using huz

end MinModulus
