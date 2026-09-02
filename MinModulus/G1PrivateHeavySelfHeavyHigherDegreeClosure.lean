/-
# Well-founded closure of the private self-heavy omission recurrence

At a terminal state with `q` fixed omissions, split the owner family into
degree exactly `q` and degree at least `q+1`.  The exact layer is bounded by
the cyclic weak-composition theorem.  Every member of the higher layer has a
fresh omitted coordinate; fixing it decreases the number of external
coordinates not yet fixed by one.  This yields a terminating recurrence,
uniformly through all later omission degrees.
-/
import MinModulus.G1PrivateHeavySelfHeavyExactDegreeCyclicBounds

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The numerical closure of the exact-layer estimate.  `D` is the number
of external coordinates not yet fixed and `q` is the current omission
degree. -/
def minimalSupportPrivateSelfHeavyHigherDegreeBound : ℕ → ℕ → ℕ
  | 0, q => q * (q - 2).choose (q - 2)
  | D + 1, q =>
      q * (D + 1 + (q - 2)).choose (q - 2) +
        (D + 1) * minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1)

@[simp] theorem minimalSupportPrivateSelfHeavyHigherDegreeBound_zero
    (q : ℕ) :
    minimalSupportPrivateSelfHeavyHigherDegreeBound 0 q =
      q * (q - 2).choose (q - 2) := rfl

@[simp] theorem minimalSupportPrivateSelfHeavyHigherDegreeBound_succ
    (D q : ℕ) :
    minimalSupportPrivateSelfHeavyHigherDegreeBound (D + 1) q =
      q * (D + 1 + (q - 2)).choose (q - 2) +
        (D + 1) *
          minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1) := rfl

/-- Fixing one previously free external coordinate erases exactly that
coordinate from the free-coordinate set. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_insert_eq_erase
    (B R : Finset (Fin (m + 1))) (z : Fin (m + 1))
    (hz : z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) :
    minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B (insert z R) =
      (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).erase z := by
  classical
  ext i
  simp only [minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates,
    Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  simp only [minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates,
    Finset.mem_compl, Finset.mem_union] at hz
  aesop

/-- Consequently, a one-label extension strictly decreases the free
coordinate measure used by the recursion. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_insert_lt
    (B R : Finset (Fin (m + 1))) (z : Fin (m + 1))
    (hz : z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) :
    (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
        B (insert z R)).card <
      (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).card := by
  rw [minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_insert_eq_erase
    B R z hz]
  exact Finset.card_erase_lt_of_mem hz

/-- Residual incidences can be summed exactly over all free coordinate
labels, with each label fiber flattened back to the ambient owner type. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_eq_sum_freeOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1)))
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R).card =
      ∑ z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R,
        (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
          g h hmin S R z).card := by
  classical
  let I := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    g h hmin S R
  let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
  let label := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
    g h hmin S R
  have hmaps : (I : Set (Σ _b : ↥S, Fin (m + 1))).MapsTo label C := by
    intro p hp
    have hspec :=
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel_spec
        g h hmin S R hself p hp
    change label p ∈ (B ∪ R)ᶜ
    apply Finset.mem_compl.mpr
    intro hpUnion
    rcases Finset.mem_union.mp hpUnion with hpB | hpR
    · exact hspec.1 hpB
    · exact hspec.2 hpR
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    #({x ∈ I | label x = z}) =
        (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
          g h hmin S R z).card := by
      simpa [I, label,
        minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber]
        using
          card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber_eq
            g h hmin S R z
    _ = (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
          g h hmin S R z).card :=
      card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber_eq_owners
        g h hmin S R z

/-- Summed form of the fresh-omission recurrence.  Unlike the threshold
dichotomy, this form is directly composable under induction. -/
theorem sub_mul_card_minimalSupportPrivateSelfHeavy_le_sum_extensionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    (q - R.card) * S.card ≤
      ∑ z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R,
        (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
          g h hmin S R z).card := by
  rw [←
    card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_eq_sum_freeOwners
      g h hmin S R hself]
  exact
    card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
      g h hmin S R q hdegree hfixed

/-- Membership in the free-coordinate set means being outside both the
transversal and the already fixed omissions. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_spec
    (B R : Finset (Fin (m + 1))) {z : Fin (m + 1)}
    (hz : z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) :
    z ∉ B ∧ z ∉ R := by
  have hzUnion : z ∉ B ∪ R := Finset.mem_compl.mp hz
  exact ⟨fun hzB ↦ hzUnion (Finset.mem_union_left R hzB),
    fun hzR ↦ hzUnion (Finset.mem_union_right B hzR)⟩

/-- A fresh-label owner subfamily inherits self-heaviness. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_self
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1))
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    ∀ b ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
        g h hmin S R z,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
  intro b hb
  exact hself b
    ((mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
      g h hmin S R z b).mp hb).1

/-- A fresh-label owner subfamily inherits any omission-degree lower bound. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_degree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) (q : ℕ)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card) :
    ∀ b ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
        g h hmin S R z,
      q ≤ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card := by
  intro b hb
  exact hdegree b
    ((mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
      g h hmin S R z b).mp hb).1

/-- The extension owner family has the enlarged fixed omission set
`insert z R`. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_fixed_insert
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1))
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    ∀ b ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
        g h hmin S R z,
      insert z R ⊆ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
  intro b hb i hi
  have hmem :=
    (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
      g h hmin S R z b).mp hb
  rcases Finset.mem_insert.mp hi with rfl | hiR
  · exact hmem.2.2
  · exact hfixed b hmem.1 hiR

/-- Adding a free coordinate to the fixed set preserves disjointness from
the transversal. -/
theorem disjoint_insert_of_mem_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
    (B R : Finset (Fin (m + 1))) {z : Fin (m + 1)}
    (hRB : Disjoint R B)
    (hz : z ∈ minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) :
    Disjoint (insert z R) B := by
  have hzSpec :=
    minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_spec B R hz
  rw [Finset.disjoint_left]
  intro i hi hiB
  rcases Finset.mem_insert.mp hi with rfl | hiR
  · exact hzSpec.1 hiB
  · exact Finset.disjoint_left.mp hRB hiR hiB

/-- Uniform closure of all higher omission degrees.  Once the current fixed
set has cardinality `q`, the entire degree-at-least-`q` family is bounded by
the terminating numerical recurrence above. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastDegree_le_higherDegreeBound
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hq : 2 ≤ q)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (hRB : Disjoint R B) :
    S.card ≤ minimalSupportPrivateSelfHeavyHigherDegreeBound
      (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).card q := by
  classical
  generalize hD :
    (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).card = D
  induction D using Nat.strong_induction_on generalizing S R q with
  | h D ih =>
    let E := minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q
    let H := minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
      g h hmin S q
    let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
    have hsplit : S.card = E.card + H.card :=
      card_minimalSupportPrivateSelfHeavy_eq_exactDegree_add_atLeastSuccDegree
        g h hmin S q hdegree
    have hE : E.card ≤ q * (D + (q - 2)).choose (q - 2) := by
      have hbound :=
        card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le_free
          g hg hmin S R q hself hRcard hfixed
      simpa [E, hD] using hbound
    have hHself : ∀ b ∈ H,
        b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
      intro b hb
      have hb' :=
        (mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
          g h hmin S q b).mp hb
      exact hself b hb'.1
    have hHdegree : ∀ b ∈ H, q + 1 ≤
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card := by
      intro b hb
      exact
        (mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
          g h hmin S q b).mp hb |>.2
    have hHfixed : ∀ b ∈ H, R ⊆ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
      intro b hb
      have hbS :=
        (mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
          g h hmin S q b).mp hb |>.1
      exact hfixed b hbS
    have hHsum : H.card ≤
        ∑ z ∈ C,
          (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
            g h hmin H R z).card := by
      have hrec :=
        sub_mul_card_minimalSupportPrivateSelfHeavy_le_sum_extensionOwners
          g h hmin H R (q + 1) hHself hHdegree hHfixed
      rw [hRcard] at hrec
      simpa [C] using hrec
    cases D with
    | zero =>
        have hCempty : C = ∅ := Finset.card_eq_zero.mp (by simpa [C] using hD)
        have hHzero : H.card = 0 := by
          have : H.card ≤ 0 := by simpa [hCempty] using hHsum
          omega
        rw [hsplit, hHzero, Nat.add_zero]
        simpa [minimalSupportPrivateSelfHeavyHigherDegreeBound] using hE
    | succ D =>
        have hEach : ∀ z ∈ C,
            (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
              g h hmin H R z).card ≤
              minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1) := by
          intro z hz
          let T := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
            g h hmin H R z
          let R' := insert z R
          have hzSpec :=
            minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_spec
              B R hz
          have hR'card : R'.card = q + 1 := by
            rw [show R' = insert z R by rfl,
              Finset.card_insert_of_notMem hzSpec.2, hRcard]
          have hTself : ∀ b ∈ T,
              b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin :=
            minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_self
              g h hmin H R z hHself
          have hTdegree : ∀ b ∈ T, q + 1 ≤
              (witnessOmissionCoordinates
                (minimalSupportPrivateWitness g h hmin b.val)).card :=
            minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_degree
              g h hmin H R z (q + 1) hHdegree
          have hTfixed : ∀ b ∈ T, R' ⊆ witnessOmissionCoordinates
              (minimalSupportPrivateWitness g h hmin b.val) :=
            minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_fixed_insert
              g h hmin H R z hHfixed
          have hR'B : Disjoint R' B :=
            disjoint_insert_of_mem_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
              B R hRB hz
          have hfreeEq :
              (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
                B R').card = D := by
            change
              (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
                B (insert z R)).card = D
            rw [
              minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates_insert_eq_erase
                B R z hz]
            have herase := Finset.card_erase_add_one hz
            change C.card = D + 1 at hD
            change (C.erase z).card = D
            omega
          have hbound := ih D (Nat.lt_succ_self D) T R' (q + 1) (by omega)
            hTself hTdegree hR'card hTfixed hR'B hfreeEq
          simpa [T] using hbound
        have hHbound : H.card ≤
            (D + 1) *
              minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1) := by
          have hCcard : C.card = D + 1 := by simpa [C] using hD
          calc
            H.card ≤ ∑ z ∈ C,
                (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
                  g h hmin H R z).card := hHsum
            _ ≤ ∑ _z ∈ C,
                minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1) := by
              exact Finset.sum_le_sum fun z hz ↦ hEach z hz
            _ = (D + 1) *
                minimalSupportPrivateSelfHeavyHigherDegreeBound D (q + 1) := by
              simp [hCcard]
        rw [hsplit]
        rw [minimalSupportPrivateSelfHeavyHigherDegreeBound_succ]
        omega

/-- The whole four-fixed family, including every degree above four, is
bounded by the closed terminating recurrence. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_le_higherDegreeBound
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B) (hvB : v ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (hvz : v ≠ z) (hvw : v ≠ w) (hvu : v ≠ u) :
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v).card ≤
      minimalSupportPrivateSelfHeavyHigherDegreeBound
        (m + 1 - (B.card + 4)) 4 := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  let R : Finset (Fin (m + 1)) := {z, w, u, v}
  have hset := quadrupleOmissionSet_disjoint_and_card
    hzB hwB huB hvB hwz huz huw hvz hvw hvu
  have hself : ∀ b ∈ Q,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
    intro b hb
    exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
      g h hmin z w u v hb).1
  have hdegree : ∀ b ∈ Q, 4 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card := by
    intro b hb
    exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
      g h hmin z w u v hb).2.1
  have hfixed : ∀ b ∈ Q, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by
    intro b hb i hi
    have hspec :=
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
        g h hmin z w u v hb
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hspec.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.2
  have hbound :=
    card_minimalSupportPrivateSelfHeavyAtLeastDegree_le_higherDegreeBound
      g hg hmin Q R 4 (by omega) hself hdegree hset.2 hfixed hset.1
  rw [card_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
    B R hset.1, hset.2] at hbound
  simpa [Q, R] using hbound

/-- The four-stage global omission endpoint is now fully numerical: no
unbounded exact-four or higher-degree family remains. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_boundedHigherDegree
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' L'' r'' L''' r''' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1))
    (hthird : L'' * r'' < r' + 1)
    (hfourth : 2 * (L''' * r''') < r'' + 1) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      B.card + 2 + L'' ≤ m + 1 ∨
      r'' + 1 ≤ 2 * (3 + 2 * (m + 1 - B.card)) ∨
      B.card + 3 + L''' ≤ m + 1 ∨
      r''' + 1 ≤ minimalSupportPrivateSelfHeavyHigherDegreeBound
        (m + 1 - (B.card + 4)) 4 := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleFiber
        g hg hmin K L r L' r' L'' r'' L''' r'''
          hself hfirst hsecond hthird hfourth with
    htwo | hcap | hcap' | hcap'' | hexact | hcap''' |
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw,
        hvz, hvw, hvu, hquad⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr (Or.inl hcap'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap'')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcap''')))))
  · have hflat :=
      card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber_eq_owners
        g h hmin z w u v
    have hlarge : r''' + 1 ≤
        (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
          g h hmin z w u v).card := by
      omega
    have hbound :=
      card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_le_higherDegreeBound
        g hg hmin z w u v hzB hwB huB hvB hwz huz huw hvz hvw hvu
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hlarge.trans hbound))))))

end MinModulus
