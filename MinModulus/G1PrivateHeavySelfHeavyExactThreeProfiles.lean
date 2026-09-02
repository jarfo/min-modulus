/-
# Exact-three profiles versus the at-least-four layer

The at-least-three self-heavy family splits exactly into witnesses with three
omissions and witnesses with at least four.  The same split is retained in a
triple-fixed omission fiber.  In its exact-three arm the fixed coordinates
are the entire omission set, and the general exact-triple mass theorem gives
the two rigid positive profiles at the owner.
-/
import MinModulus.G1PrivateHeavySelfHeavyTripleOmissionFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Self-heavy private owners whose canonical witness has exactly three
omissions. -/
noncomputable def minimalSupportPrivateSelfHeavyExactThreeVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).filter
    (fun b ↦ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card = 3)

/-- Self-heavy private owners whose canonical witness has at least four
omissions. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastFourVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).filter
    (fun b ↦ 4 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyExactThreeVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyExactThreeVertices g h hmin ↔
      b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin ∧
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card = 3 := by
  classical
  simp [minimalSupportPrivateSelfHeavyExactThreeVertices]

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin ↔
      b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin ∧
        4 ≤ (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastFourVertices]

/-- Exact-three and at-least-four owners exhaust `H3`. -/
theorem minimalSupportPrivateSelfHeavy_exactThree_union_atLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    minimalSupportPrivateSelfHeavyExactThreeVertices g h hmin ∪
        minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin =
      minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (mem_minimalSupportPrivateSelfHeavyExactThreeVertices_iff
        g h hmin b).mp hb |>.1
    · exact (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
        g h hmin b).mp hb |>.1
  · intro hb
    have hthree :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
        g h hmin b).mp hb |>.2
    by_cases heq : (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card = 3
    · exact Finset.mem_union_left _
        ((mem_minimalSupportPrivateSelfHeavyExactThreeVertices_iff
          g h hmin b).mpr ⟨hb, heq⟩)
    · exact Finset.mem_union_right _
        ((mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
          g h hmin b).mpr ⟨hb, by omega⟩)

/-- The two higher-omission layers are disjoint. -/
theorem minimalSupportPrivateSelfHeavy_exactThree_disjoint_atLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Disjoint (minimalSupportPrivateSelfHeavyExactThreeVertices g h hmin)
      (minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbThree hbFour
  have hthree := (mem_minimalSupportPrivateSelfHeavyExactThreeVertices_iff
    g h hmin b).mp hbThree
  have hfour := (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
    g h hmin b).mp hbFour
  omega

/-- Exact cardinal partition of `H3`. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_eq_exactThree_add_atLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).card =
      (minimalSupportPrivateSelfHeavyExactThreeVertices g h hmin).card +
        (minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin).card := by
  rw [← minimalSupportPrivateSelfHeavy_exactThree_union_atLeastFour
    g h hmin]
  exact Finset.card_union_of_disjoint
    (minimalSupportPrivateSelfHeavy_exactThree_disjoint_atLeastFour
      g h hmin)

/-- Exact-three members of one triple-fixed fiber. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleExactThreeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
    g h hmin z w u).filter (fun b ↦
      (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val.val)).card = 3)

/-- At-least-four members of one triple-fixed fiber. -/
noncomputable def minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
    g h hmin z w u).filter (fun b ↦
      4 ≤ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val.val)).card)

/-- The two triple-fiber layers form an exact disjoint partition. -/
theorem card_tripleOmissionFiber_eq_exactThree_add_atLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
        g h hmin z w u).card =
      (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
        g h hmin z w u).card +
      (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
        g h hmin z w u).card := by
  classical
  let T := minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
    g h hmin z w u
  let E := minimalSupportPrivateSelfHeavyTripleExactThreeFiber
    g h hmin z w u
  let F := minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
    g h hmin z w u
  have hunion : E ∪ F = T := by
    ext b
    constructor
    · intro hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_filter.mp hb).1
      · exact (Finset.mem_filter.mp hb).1
    · intro hbT
      have hbH3 := b.val.property
      have hthree :=
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b.val.val).mp hbH3 |>.2
      by_cases heq : (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val)).card = 3
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hbT, heq⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hbT, by omega⟩)
  have hdisj : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro b hbE hbF
    have hbE' := Finset.mem_filter.mp hbE
    have hbF' := Finset.mem_filter.mp hbF
    omega
  change T.card = E.card + F.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- A lower bound for a triple-fixed fiber transfers, with factor two, to its
exact-three or at-least-four layer. -/
theorem le_two_mul_tripleExactThree_or_le_two_mul_tripleAtLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) (K : ℕ)
    (hK : K ≤ (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
      g h hmin z w u).card) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
      g h hmin z w u).card ∨
      K ≤ 2 * (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
        g h hmin z w u).card := by
  rw [card_tripleOmissionFiber_eq_exactThree_add_atLeastFour
    g h hmin z w u] at hK
  omega

/-- A member of the exact-three triple fiber has exactly the fixed omission
set and one of the two rigid heavy-owner positive profiles. -/
theorem minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    {b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyTripleExactThreeFiber
      g h hmin z w u) :
    let c := minimalSupportPrivateWitness g h hmin b.val.val.val
    let e := b.val.val.val.val
    (∀ i, c i = -1 ↔ i = z ∨ i = w ∨ i = u) ∧
      ((c e = 3 ∧
          ∀ j, j ≠ z → j ≠ w → j ≠ u → j ≠ e → c j = 0) ∨
        (c e = 2 ∧ ∃ f,
          f ≠ z ∧ f ≠ w ∧ f ≠ u ∧ f ≠ e ∧ c f = 1 ∧
            ∀ j, j ≠ z → j ≠ w → j ≠ u → j ≠ e → j ≠ f →
              c j = 0)) := by
  let c := minimalSupportPrivateWitness g h hmin b.val.val.val
  let e := b.val.val.val.val
  let O := witnessOmissionCoordinates c
  have hb' := Finset.mem_filter.mp hb
  have htriple :=
    minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec
      g h hmin z w u hb'.1
  have hbDouble :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
      g h hmin z w b.val).mp b.property
  have hwz : w ≠ z := hbDouble.2.1
  have hsetCard : ({z, w, u} : Finset (Fin (m + 1))).card = 3 := by
    have hzw : z ≠ w := Ne.symm hwz
    have hzu : z ≠ u := Ne.symm htriple.1
    have hwu : w ≠ u := Ne.symm htriple.2.1
    simp [hzw, hzu, hwu]
  have hsetSubset : ({z, w, u} : Finset (Fin (m + 1))) ⊆ O := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact htriple.2.2.1
    · exact htriple.2.2.2.1
    · exact htriple.2.2.2.2
  have hOcard : O.card = 3 := by
    exact hb'.2
  have hOeq : O = {z, w, u} := by
    symm
    exact Finset.eq_of_subset_of_card_le hsetSubset (by
      rw [hOcard, hsetCard])
  have homit : ∀ i, c i = -1 ↔ i = z ∨ i = w ∨ i = u := by
    intro i
    calc
      c i = -1 ↔ i ∈ O := witnessOmissionCoordinates_exact c i
      _ ↔ i ∈ ({z, w, u} : Finset (Fin (m + 1))) := by rw [hOeq]
      _ ↔ i = z ∨ i = w ∨ i = u := by simp
  have hbH3 := b.val.property
  have hbSelf :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin b.val.val).mp hbH3 |>.1
  have hheavy : 2 ≤ c e := by
    exact minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hbSelf
  have hcz : c z = -1 := (homit z).2 (Or.inl rfl)
  have hcw : c w = -1 := (homit w).2 (Or.inr (Or.inl rfl))
  have hcu : c u = -1 := (homit u).2 (Or.inr (Or.inr rfl))
  have hez : e ≠ z := by intro heq; rw [heq, hcz] at hheavy; omega
  have hew : e ≠ w := by intro heq; rw [heq, hcw] at hheavy; omega
  have heu : e ≠ u := by intro heq; rw [heq, hcu] at hheavy; omega
  refine ⟨homit, ?_⟩
  exact exact_triple_heavy_shape g
    (minimalSupportPrivateWitness_isWitness g h hmin b.val.val.val)
    z w u e (Ne.symm hwz) (Ne.symm htriple.2.1) htriple.1
    homit hez hew heu hheavy

/-- The terminal triple-fixed output of 2hg splits quantitatively into its
rigid exact-three layer or the recurrent at-least-four layer. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_tripleExactThree_or_tripleAtLeastFour
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' L'' r'' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1))
    (hthird : L'' * r'' < r' + 1) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      B.card + 2 + L'' ≤ m + 1 ∨
      ∃ z w u : Fin (m + 1),
        z ∉ B ∧ w ∉ B ∧ u ∉ B ∧
        w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
        ((r'' + 1 ≤ 2 *
            (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
              g h hmin z w u).card) ∨
          r'' + 1 ≤ 2 *
            (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
              g h hmin z w u).card) := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_tripleFiber
        g h hmin K L r L' r' L'' r'' hself hfirst hsecond hthird with
    htwo | hcapacity | hcapacity' | hcapacity'' |
      ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, htriple⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcapacity'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcapacity'')))
  · have hK : r'' + 1 ≤
        (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
          g h hmin z w u).card := by omega
    have hsplit := le_two_mul_tripleExactThree_or_le_two_mul_tripleAtLeastFour
      g h hmin z w u (r'' + 1) hK
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, hsplit⟩)))

end MinModulus
