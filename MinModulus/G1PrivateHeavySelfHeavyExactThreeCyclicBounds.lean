/-
# Cyclic bounds for the exact-three affine fibers

In a finite cyclic group, a fiber of multiplication by `d` has at most
`gcd(|G|,d)` elements.  Apply this once to the pure owner-`3` profile and
once to every fixed-companion owner-`2` profile.  Validity makes the tuple
entries injective, so the exact-three terminal family obtains a uniform
linear bound in the number of coordinates outside the minimal transversal.
-/
import MinModulus.G1PrivateHeavySelfHeavyExactThreeAffineFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- An injectively labelled finite family on which multiplication by `d` is
constant has cardinality at most the kernel size `gcd(|G|,d)` in a finite
cyclic additive group. -/
theorem card_le_gcd_of_injective_nsmul_eq_const
    [Finite G] [IsAddCyclic G]
    {ι : Type*} (S : Finset ι) (v : ι → G) (hv : Function.Injective v)
    (d : ℕ) (t : G) (hconst : ∀ i ∈ S, d • v i = t) :
    S.card ≤ (Nat.card G).gcd d := by
  classical
  by_cases hS : S.Nonempty
  · let a : ↥S := ⟨hS.choose, hS.choose_spec⟩
    let toKer : ↥S → ↥(nsmulAddMonoidHom d : G →+ G).ker := fun i ↦
      ⟨v i - v a, by
        change d • (v i - v a) = 0
        rw [nsmul_sub, hconst i i.property, hconst a a.property, sub_self]⟩
    have hinj : Function.Injective toKer := by
      intro i j hij
      apply Subtype.ext
      apply hv
      have hsub : v i - v a = v j - v a := congrArg Subtype.val hij
      exact sub_left_injective hsub
    calc
      S.card = Nat.card ↥S := by
        rw [Nat.card_eq_fintype_card]
        simp
      _ ≤ Nat.card ↥(nsmulAddMonoidHom d : G →+ G).ker :=
        Nat.card_le_card_of_injective toKer hinj
      _ = (Nat.card G).gcd d :=
        IsAddCyclic.card_nsmulAddMonoidHom_ker G d
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

/-- Tuple values of distinct ambient members of the pure-three owner type
remain distinct. -/
theorem minimalSupportPrivateSelfHeavyTriplePureThree_ownerValue_injective
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :
    Function.Injective (fun b :
        ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
          g h hmin z w) ↦ g b.val.val.val.val) := by
  intro b₁ b₂ hval
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact validTuple_injective g hg hval

/-- The pure owner-`3` layer is a multiplication-by-three fiber. -/
theorem card_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_le_gcd
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
      g h hmin z w u).card ≤ N.gcd 3 := by
  let P := minimalSupportPrivateSelfHeavyTriplePureThreeOwners
    g h hmin z w u
  let value : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w) → ZMod N := fun b ↦ g b.val.val.val.val
  have hinj : Function.Injective value :=
    minimalSupportPrivateSelfHeavyTriplePureThree_ownerValue_injective
      g hg hmin z w
  have hconst : ∀ b ∈ P,
      (3 : ℕ) • value b = h + g z + g w + g u := by
    intro b hb
    have haffine :=
      minimalSupportPrivateSelfHeavyTriplePureThreeOwner_affine
        g h hmin z w u hb
    change ((3 : ℕ) : ℤ) • value b = h + g z + g w + g u at haffine
    simpa only [natCast_zsmul] using haffine
  have hcard := card_le_gcd_of_injective_nsmul_eq_const
    P value hinj 3 (h + g z + g w + g u) hconst
  simpa [Nat.card_zmod] using hcard

/-- Coarsened pure-three bound, uniform in the modulus. -/
theorem card_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_le_three
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTriplePureThreeOwners
      g h hmin z w u).card ≤ 3 :=
  (card_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_le_gcd
    g hg hmin z w u).trans (Nat.gcd_le_right N (by omega))

/-- Tuple values of distinct members of the two-plus-one owner subtype remain
distinct. -/
theorem minimalSupportPrivateSelfHeavyTripleTwoOne_ownerValue_injective
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    Function.Injective (fun b :
        ↥(minimalSupportPrivateSelfHeavyTripleTwoOneOwners
          g h hmin z w u) ↦ g b.val.val.val.val.val) := by
  intro b₁ b₂ hval
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact validTuple_injective g hg hval

/-- At one fixed companion, the owner-`2` layer is a multiplication-by-two
fiber. -/
theorem card_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_le_gcd
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u f : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
      g h hmin z w u f).card ≤ N.gcd 2 := by
  let T := minimalSupportPrivateSelfHeavyTripleTwoOneOwners
    g h hmin z w u
  let F := minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
    g h hmin z w u f
  let value : ↥T → ZMod N := fun b ↦ g b.val.val.val.val.val
  have hinj : Function.Injective value :=
    minimalSupportPrivateSelfHeavyTripleTwoOne_ownerValue_injective
      g hg hmin z w u
  have hconst : ∀ b ∈ F,
      (2 : ℕ) • value b = h + g z + g w + g u - g f := by
    intro b hb
    have hcomp :=
      (mem_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_iff
        g h hmin z w u f b).mp hb
    have hspec :=
      minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_spec
        g h hmin z w u b
    dsimp only at hspec
    have haffine := hspec.2.2.2.2.2.2
    rw [hcomp] at haffine
    have htwo : (2 : ℤ) • value b = h + g z + g w + g u - g f := by
      change (2 : ℤ) • g b.val.val.val.val.val =
        h + g z + g w + g u - g f
      calc
        (2 : ℤ) • g b.val.val.val.val.val =
            ((2 : ℤ) • g b.val.val.val.val.val + g f) - g f := by abel
        _ = h + g z + g w + g u - g f := by rw [haffine]
    change ((2 : ℕ) : ℤ) • value b =
      h + g z + g w + g u - g f at htwo
    simpa only [natCast_zsmul] using htwo
  have hcard := card_le_gcd_of_injective_nsmul_eq_const
    F value hinj 2 (h + g z + g w + g u - g f) hconst
  simpa [Nat.card_zmod] using hcard

/-- Coarsened fixed-companion bound, uniform in the modulus. -/
theorem card_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_le_two
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u f : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
      g h hmin z w u f).card ≤ 2 :=
  (card_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_le_gcd
    g hg hmin z w u f).trans (Nat.gcd_le_right N (by omega))

/-- Exact summation plus the doubling-kernel bound controls the whole
two-plus-one layer by twice the number of external companion labels. -/
theorem card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_le_two_mul_companionLabels
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleTwoOneOwners
        g h hmin z w u).card ≤
      2 * (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u).card := by
  rw [card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_eq_sum_companionFibers]
  calc
    (∑ f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u,
        (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber
          g h hmin z w u f).card) ≤
        ∑ _f ∈ minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
          g h hmin z w u, 2 := by
      apply Finset.sum_le_sum
      intro f _hf
      exact card_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_le_two
        g hg hmin z w u f
    _ = 2 * (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u).card := by simp [Nat.mul_comm]

/-- Companion labels and the minimal transversal fit disjointly in the
ambient coordinate set. -/
theorem card_minimalSupport_add_tripleTwoOneCompanionLabels_le
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    B.card +
      (minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
        g h hmin z w u).card ≤ m + 1 := by
  classical
  let F := minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels
    g h hmin z w u
  have hdisj : Disjoint F B :=
    minimalSupportPrivateSelfHeavyTripleTwoOneCompanionLabels_disjoint
      g h hmin z w u
  rw [← Finset.card_union_of_disjoint hdisj.symm]
  simpa using Finset.card_le_univ (B ∪ F)

/-- Uniform cyclic bound for every triple-fixed exact-three owner family. -/
theorem card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_le
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleExactThreeFiber
        g h hmin z w u).card ≤
      3 + 2 * (m + 1 - B.card) := by
  have hsplit :=
    card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_eq_pureThree_add_twoOne
      g h hmin z w u
  have hpure :=
    card_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_le_three
      g hg hmin z w u
  have htwo :=
    card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_le_two_mul_companionLabels
      g hg hmin z w u
  have hcapacity := card_minimalSupport_add_tripleTwoOneCompanionLabels_le
    g hmin z w u
  omega

/-- Substitute the cyclic exact-three bound into the global three-stage
omission endpoint.  The only unbounded terminal omission branch left is the
at-least-four layer. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_tripleAtLeastFour
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
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
      r'' + 1 ≤ 2 * (3 + 2 * (m + 1 - B.card)) ∨
      ∃ z w u : Fin (m + 1),
        z ∉ B ∧ w ∉ B ∧ u ∉ B ∧
        w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
        r'' + 1 ≤ 2 *
          (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
            g h hmin z w u).card := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_tripleExactThree_or_tripleAtLeastFour
        g h hmin K L r L' r' L'' r'' hself hfirst hsecond hthird with
    htwo | hcap | hcap' | hcap'' |
      ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, hexact | hfour⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr (Or.inl hcap'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap'')))
  · have hbound :=
      card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_le
        g hg hmin z w u
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hexact.trans
      (Nat.mul_le_mul_left 2 hbound))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, hfour⟩))))

end MinModulus
