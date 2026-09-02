/-
# Affine fibers of the exact-three self-heavy layer

Split a triple-fixed exact-three owner family by its two rigid positive
profiles.  The pure profile satisfies one fixed multiplication-by-three
equation.  In the `2+1` profile the coefficient-one companion is unique,
external to the minimal transversal, and satisfies one fixed affine equation
with its owner.  Grouping owners by that companion loses no multiplicity and
gives an exact ambient-capacity/large-fiber alternative.
-/
import MinModulus.G1PrivateHeavySelfHeavyExactThreeProfiles

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Exact-three owners whose positive mass is concentrated with coefficient
three at the owner. -/
noncomputable def minimalSupportPrivateSelfHeavyTriplePureThreeOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
    g h hmin z w u).filter (fun b ↦
      minimalSupportPrivateWitness g h hmin b.val.val.val b.val.val.val.val = 3)

/-- Exact-three owners whose owner coefficient is two, leaving one unit for
a unique companion. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleTwoOneOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
    g h hmin z w u).filter (fun b ↦
      minimalSupportPrivateWitness g h hmin b.val.val.val b.val.val.val.val = 2)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w)) :
    b ∈ minimalSupportPrivateSelfHeavyTriplePureThreeOwners
        g h hmin z w u ↔
      b ∈ minimalSupportPrivateSelfHeavyTripleExactThreeFiber
          g h hmin z w u ∧
        minimalSupportPrivateWitness g h hmin b.val.val.val
          b.val.val.val.val = 3 := by
  classical
  simp [minimalSupportPrivateSelfHeavyTriplePureThreeOwners]

@[simp] theorem mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w)) :
    b ∈ minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u ↔
      b ∈ minimalSupportPrivateSelfHeavyTripleExactThreeFiber
          g h hmin z w u ∧
        minimalSupportPrivateWitness g h hmin b.val.val.val
          b.val.val.val.val = 2 := by
  classical
  simp [minimalSupportPrivateSelfHeavyTripleTwoOneOwners]

/-- The pure-three and two-plus-one owner layers exhaust the exact-three
triple fiber. -/
theorem minimalSupportPrivateSelfHeavyTriple_pureThree_union_twoOne
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    minimalSupportPrivateSelfHeavyTriplePureThreeOwners g h hmin z w u ∪
        minimalSupportPrivateSelfHeavyTripleTwoOneOwners g h hmin z w u =
      minimalSupportPrivateSelfHeavyTripleExactThreeFiber
        g h hmin z w u := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (mem_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_iff
        g h hmin z w u b).mp hb |>.1
    · exact (mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
        g h hmin z w u b).mp hb |>.1
  · intro hb
    have hshape :=
      minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape
        g h hmin z w u hb
    dsimp only at hshape
    rcases hshape with ⟨_homit, hthree | htwo⟩
    · exact Finset.mem_union_left _
        ((mem_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_iff
          g h hmin z w u b).mpr ⟨hb, hthree.1⟩)
    · exact Finset.mem_union_right _
        ((mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
          g h hmin z w u b).mpr ⟨hb, htwo.1⟩)

/-- The two exact-three positive-profile layers are disjoint. -/
theorem minimalSupportPrivateSelfHeavyTriple_pureThree_disjoint_twoOne
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    Disjoint
      (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
        g h hmin z w u)
      (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbThree hbTwo
  have hthree :=
    (mem_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_iff
      g h hmin z w u b).mp hbThree |>.2
  have htwo :=
    (mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
      g h hmin z w u b).mp hbTwo |>.2
  omega

/-- Exact cardinality decomposition of the exact-three terminal fiber. -/
theorem card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_eq_pureThree_add_twoOne
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
        g h hmin z w u).card =
      (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
        g h hmin z w u).card +
      (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card := by
  rw [← minimalSupportPrivateSelfHeavyTriple_pureThree_union_twoOne
    g h hmin z w u]
  exact Finset.card_union_of_disjoint
    (minimalSupportPrivateSelfHeavyTriple_pureThree_disjoint_twoOne
      g h hmin z w u)

/-- A lower bound for the exact-three fiber transfers, with factor two, to
one of its two positive-profile layers. -/
theorem le_two_mul_triplePureThree_or_le_two_mul_tripleTwoOne
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) (K : ℕ)
    (hK : K ≤ (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
      g h hmin z w u).card) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
      g h hmin z w u).card ∨
      K ≤ 2 * (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card := by
  rw [card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_eq_pureThree_add_twoOne
    g h hmin z w u] at hK
  omega

/-- Every pure-three owner lies in one fixed affine fiber. -/
theorem minimalSupportPrivateSelfHeavyTriplePureThreeOwner_affine
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    {b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyTriplePureThreeOwners
      g h hmin z w u) :
    (3 : ℤ) • g b.val.val.val.val = h + g z + g w + g u := by
  let c := minimalSupportPrivateWitness g h hmin b.val.val.val
  let e := b.val.val.val.val
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_iff
      g h hmin z w u b).mp hb
  have hshape :=
    minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape
      g h hmin z w u hb'.1
  dsimp only at hshape
  have homit := hshape.1
  have hce : c e = 3 := by simpa [c, e] using hb'.2
  have hbTriple := Finset.mem_filter.mp hb'.1 |>.1
  have htriple :=
    minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec
      g h hmin z w u hbTriple
  have hbDouble :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
      g h hmin z w b.val).mp b.property
  have hzw : z ≠ w := Ne.symm hbDouble.2.1
  have hwu : w ≠ u := Ne.symm htriple.2.1
  have huz : u ≠ z := htriple.1
  have hez : e ≠ z := by
    intro heq
    have hcneg : c e = -1 := by rw [heq]; exact (homit z).2 (Or.inl rfl)
    omega
  have hew : e ≠ w := by
    intro heq
    have hcneg : c e = -1 := by
      rw [heq]
      exact (homit w).2 (Or.inr (Or.inl rfl))
    omega
  have heu : e ≠ u := by
    intro heq
    have hcneg : c e = -1 := by
      rw [heq]
      exact (homit u).2 (Or.inr (Or.inr rfl))
    omega
  exact three_smul_eq_target_add_triple_of_exact_triple_coeff_three
    g (minimalSupportPrivateWitness_isWitness g h hmin b.val.val.val)
      z w u e hzw hwu huz homit hez hew heu hce

/-- A two-plus-one owner has a unique coefficient-one coordinate. -/
theorem existsUnique_minimalSupportPrivateSelfHeavyTripleTwoOne_companion
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u)) :
    ∃! f : Fin (m + 1),
      minimalSupportPrivateWitness g h hmin b.val.val.val.val f = 1 := by
  let c := minimalSupportPrivateWitness g h hmin b.val.val.val.val
  let e := b.val.val.val.val.val
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
      g h hmin z w u b.val).mp b.property
  have hshape :=
    minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape
      g h hmin z w u hb'.1
  dsimp only at hshape
  rcases hshape with ⟨homit, hthree | htwo⟩
  · have hce : c e = 2 := by simpa [c, e] using hb'.2
    omega
  · obtain ⟨hce, f, hfz, hfw, hfu, hfe, hcf, hzero⟩ := htwo
    have hce' : c e = 2 := by simpa [c, e] using hce
    refine ⟨f, by simpa [c] using hcf, ?_⟩
    intro j hcj
    have hcj' : c j = 1 := by simpa [c] using hcj
    by_cases hjz : j = z
    · subst j
      have := (homit z).2 (Or.inl rfl)
      omega
    by_cases hjw : j = w
    · subst j
      have := (homit w).2 (Or.inr (Or.inl rfl))
      omega
    by_cases hju : j = u
    · subst j
      have := (homit u).2 (Or.inr (Or.inr rfl))
      omega
    by_cases hje : j = e
    · subst j
      omega
    by_cases hjf : j = f
    · exact hjf
    have hcj0 := hzero j hjz hjw hju hje hjf
    omega

/-- The canonical coefficient-one companion of a two-plus-one exact-three
owner. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u)) : Fin (m + 1) :=
  Classical.choose
    (existsUnique_minimalSupportPrivateSelfHeavyTripleTwoOne_companion
      g h hmin z w u b)

theorem minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_coeff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u)) :
    minimalSupportPrivateWitness g h hmin b.val.val.val.val
        (minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
          g h hmin z w u b) = 1 :=
  (Classical.choose_spec
    (existsUnique_minimalSupportPrivateSelfHeavyTripleTwoOne_companion
      g h hmin z w u b)).1

theorem minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_unique
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u))
    {f : Fin (m + 1)}
    (hf : minimalSupportPrivateWitness g h hmin b.val.val.val.val f = 1) :
    f = minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u b :=
  (Classical.choose_spec
    (existsUnique_minimalSupportPrivateSelfHeavyTripleTwoOne_companion
      g h hmin z w u b)).2 f hf

/-- The selected companion is fresh relative to the transversal and fixed
omissions, and the owner/companion pair satisfies one fixed affine equation. -/
theorem minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u)) :
    let f := minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u b
    let e := b.val.val.val.val.val
    f ∉ B ∧ f ≠ z ∧ f ≠ w ∧ f ≠ u ∧ f ≠ e ∧
      minimalSupportPrivateWitness g h hmin b.val.val.val.val f = 1 ∧
      (2 : ℤ) • g e + g f = h + g z + g w + g u := by
  let c := minimalSupportPrivateWitness g h hmin b.val.val.val.val
  let e := b.val.val.val.val.val
  let f := minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
    g h hmin z w u b
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_iff
      g h hmin z w u b.val).mp b.property
  have hshape :=
    minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape
      g h hmin z w u hb'.1
  dsimp only at hshape
  rcases hshape with ⟨homit, hthree | htwo⟩
  · have hce : c e = 2 := by simpa [c, e] using hb'.2
    omega
  · obtain ⟨hce, f', hf'z, hf'w, hf'u, hf'e, hcf', _hzero⟩ := htwo
    have hce' : c e = 2 := by simpa [c, e] using hce
    have hf'eq : f' = f := by
      apply minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_unique
        g h hmin z w u b
      simpa [c] using hcf'
    subst f'
    have hcf :=
      minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_coeff
        g h hmin z w u b
    have hfB : f ∉ B := by
      intro hfB
      have hzero := minimalSupportPrivateWitness_eq_zero_of_ne
        g h hmin b.val.val.val.val hfB hf'e
      change c f = 0 at hzero
      change c f = 1 at hcf
      omega
    have hbTriple := Finset.mem_filter.mp hb'.1 |>.1
    have htriple :=
      minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec
        g h hmin z w u hbTriple
    have hbDouble :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
        g h hmin z w b.val.val).mp b.val.property
    have hzw : z ≠ w := Ne.symm hbDouble.2.1
    have hwu : w ≠ u := Ne.symm htriple.2.1
    have huz : u ≠ z := htriple.1
    have hez : e ≠ z := by
      intro heq
      have hcneg : c e = -1 := by rw [heq]; exact (homit z).2 (Or.inl rfl)
      omega
    have hew : e ≠ w := by
      intro heq
      have hcneg : c e = -1 := by
        rw [heq]
        exact (homit w).2 (Or.inr (Or.inl rfl))
      omega
    have heu : e ≠ u := by
      intro heq
      have hcneg : c e = -1 := by
        rw [heq]
        exact (homit u).2 (Or.inr (Or.inr rfl))
      omega
    have haffine :=
      two_smul_add_eq_target_add_triple_of_exact_triple_coeff_two_one
        g (minimalSupportPrivateWitness_isWitness
          g h hmin b.val.val.val.val)
        z w u e f hzw hwu huz homit hez hew heu
          hf'z hf'w hf'u hf'e hce' hcf
    exact ⟨hfB, hf'z, hf'w, hf'u, hf'e, hcf, haffine⟩

/-- External companion labels realized by the two-plus-one owner family. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u f : Fin (m + 1)) :
    f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u ↔
      ∃ b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
          g h hmin z w u),
        minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
          g h hmin z w u b = f := by
  classical
  change f ∈ Finset.univ.image
      (minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
        g h hmin z w u) ↔ _
  constructor
  · intro hf
    obtain ⟨b, _hb, hbf⟩ := Finset.mem_image.mp hf
    exact ⟨b, hbf⟩
  · rintro ⟨b, rfl⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩

/-- All realized companion labels are external to the minimal transversal. -/
theorem minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_disjoint
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    Disjoint
      (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u) B := by
  classical
  rw [Finset.disjoint_left]
  intro f hf hfB
  obtain ⟨b, rfl⟩ :=
    (mem_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_iff
      g h hmin z w u f).mp hf
  exact (minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_spec
    g h hmin z w u b).1 hfB

/-- Owners having one fixed selected companion. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u f : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u) := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u b = f)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u f : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
      g h hmin z w u)) :
    b ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
        g h hmin z w u f ↔
      minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
        g h hmin z w u b = f := by
  classical
  simp [minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber]

/-- Grouping by the selected companion is an exact partition of the owner
family: no owner multiplicity is lost. -/
theorem card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_eq_sum_companionFibers
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card =
      ∑ f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u,
        (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
          g h hmin z w u f).card := by
  classical
  let T := minimalSupportPrivateSelfHeavyTripleTwoOneOwners
    g h hmin z w u
  let label : ↥T → Fin (m + 1) :=
    minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u
  calc
    T.card = (Finset.univ : Finset ↥T).card := by simp
    _ = ∑ f ∈ (Finset.univ : Finset ↥T).image label,
          ((Finset.univ : Finset ↥T).filter (fun b ↦ label b = f)).card :=
      Finset.card_eq_sum_card_image label Finset.univ
    _ = ∑ f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
            g h hmin z w u,
          (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
            g h hmin z w u f).card := by rfl

/-- Exact label/fiber pigeonhole alternative for the two-plus-one layer. -/
theorem minimalSupportPrivateSelfHeavyTripleTwoOne_companionImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card) :
    L ≤ (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u).card ∨
      ∃ f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u,
        r < (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
          g h hmin z w u f).card := by
  classical
  let T := minimalSupportPrivateSelfHeavyTripleTwoOneOwners
    g h hmin z w u
  let label : ↥T → Fin (m + 1) :=
    minimalSupportPrivateSelfHeavyTripleTwoOneCompanion
      g h hmin z w u
  let labels := minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
    g h hmin z w u
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < (Finset.univ : Finset ↥T).card := by
      simp only [Finset.card_univ, Fintype.card_coe]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ b ∈ (Finset.univ : Finset ↥T), label b ∈ labels := by
      intro b _hb
      simp [label, labels,
        minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels]
    obtain ⟨f, hf, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨f, hf, ?_⟩
    simpa [label, T,
      minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber] using hfiber

/-- Many two-plus-one owners either consume ambient complement coordinates or
share one external companion. -/
theorem minimalSupportPrivateSelfHeavyTripleTwoOne_capacity_or_largeCompanionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card) :
    B.card + L ≤ m + 1 ∨
      ∃ f : Fin (m + 1), f ∉ B ∧
        r < (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
          g h hmin z w u f).card := by
  rcases
      minimalSupportPrivateSelfHeavyTripleTwoOne_companionImage_or_largeFiber
        g h hmin z w u L r hcount with hlabels | hfiber
  · left
    have hdisj :=
      minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_disjoint
        g h hmin z w u
    have hcap : B.card +
        (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u).card ≤ m + 1 := by
      rw [← Finset.card_union_of_disjoint hdisj.symm]
      simpa using Finset.card_le_univ
        (B ∪ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u)
    omega
  · right
    obtain ⟨f, hfLabel, hfLarge⟩ := hfiber
    have hfB : f ∉ B :=
      Finset.disjoint_left.mp
        (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_disjoint
          g h hmin z w u) hfLabel
    exact ⟨f, hfB, hfLarge⟩

/-- Quantitative exact-three endpoint: either many owners have the pure
multiplication-by-three profile, companion labels consume ambient capacity,
or many owners share one external companion and hence one fixed affine
right-hand side. -/
theorem minimalSupportPrivateSelfHeavyTripleExactThree_pureOrCapacityOrLargeCompanionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) (K L r : ℕ)
    (hK : K ≤ (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
      g h hmin z w u).card)
    (hcount : 2 * (L * r) < K) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
      g h hmin z w u).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ f : Fin (m + 1), f ∉ B ∧
        r < (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
          g h hmin z w u f).card := by
  rcases le_two_mul_triplePureThree_or_le_two_mul_tripleTwoOne
      g h hmin z w u K hK with hpure | htwo
  · exact Or.inl hpure
  · right
    have hinner : L * r <
        (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
          g h hmin z w u).card := by omega
    exact minimalSupportPrivateSelfHeavyTripleTwoOne_capacity_or_largeCompanionFiber
      g h hmin z w u L r hinner

end MinModulus
