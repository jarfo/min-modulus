/-
# A two-coordinate pivot for the all-zero quarter quartet

For an all-zero exact triangle, deleting any triangle edge kills all three
local half-edge witnesses.  The quarter layer opposite that edge has zero
coefficients on both deleted vertices and therefore survives.  Globally this
gives a clean dichotomy: either that edge hits every half-witness support and
produces a two-coordinate halving descent, or a new half witness avoids both
pivot coordinates.
-/
import MinModulus.G1AvoidanceQuarterPairPivot

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Local all-zero support geometry for one chosen triangle edge: all three
half witnesses meet the edge, while one quarter witness vanishes on it. -/
def WitnessAllZeroQuarterTwoPivotPackage
    (g : Fin m → G) (h : G) : Prop :=
  ∃ t : G, ∃ a b : Fin m, ∃ q cAB cBD cDA : Fin m → ℤ,
    a ≠ b ∧ t + t = h ∧
    Witness g t q ∧ q a = 0 ∧ q b = 0 ∧
    Witness g h cAB ∧ (cAB a ≠ 0 ∨ cAB b ≠ 0) ∧
    Witness g h cBD ∧ (cBD a ≠ 0 ∨ cBD b ≠ 0) ∧
    Witness g h cDA ∧ (cDA a ≠ 0 ∨ cDA b ≠ 0)

/-- An all-zero exact triangle supplies a two-pivot package. -/
theorem exactTriangleAllZero_quarterTwoPivot
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hall : WitnessExactTriangleAllZero g h) :
    WitnessAllZeroQuarterTwoPivotPackage g h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hAB0, hBD0, hDA0⟩ := hall
  obtain ⟨x, y, z, t, hx, hy, hz, hxy, hyz, hzx,
    _hABx, _hBDy, _hDAz, ht,
    _hc0, _h0, hc1, _h1, _hc2, _h2, _hc3, _h3,
    _hsumAB, _hsumBD, _hsumDA⟩ :=
    exists_light_quarterWitness_quartet_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hAB0 hBD0 hDA0
  let q : Fin m → ℤ := balancedPairCoeffs x d y z
  have hqa : q a = 0 := by
    simp [q, balancedPairCoeffs, Ne.symm hx.1, Ne.symm hda,
      Ne.symm hy.2.2, Ne.symm hz.2.1]
  have hqb : q b = 0 := by
    simp [q, balancedPairCoeffs, Ne.symm hx.2.1, hbd,
      Ne.symm hy.1, Ne.symm hz.2.2]
  have hcABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hcBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hcDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  exact ⟨t, a, b, q, cAB, cBD, cDA, hab, ht,
    hc1, hqa, hqb,
    hcAB, Or.inl (by omega),
    hcBD, Or.inr (by omega),
    hcDA, Or.inl (by omega)⟩

/-- Cyclic all-zero dichotomy.  The chosen edge either hits every half-
witness support, giving a two-coordinate valid descent modulo `M`, or there
is an explicit half witness vanishing at both edge vertices. -/
theorem exactTriangleAllZero_twoDelete_or_pairAvoider
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hall : WitnessExactTriangleAllZero g (M : ZMod N)) :
    WitnessAllZeroQuarterTwoPivotPackage g (M : ZMod N) ∧
      (AdmitsValidTuple (m - 2) M ∨
        ∃ a b : Fin m, a ≠ b ∧
          ∃ r : Fin m → ℤ,
            Witness g (M : ZMod N) r ∧ r a = 0 ∧ r b = 0) := by
  classical
  have hpkg := exactTriangleAllZero_quarterTwoPivot
    g hg (half_add_half hN) hall
  obtain ⟨t, a, b, q, cAB, cBD, cDA, hab, ht,
    hq, hqa, hqb, hcAB, hABhit, hcBD, hBDhit, hcDA, hDAhit⟩ := hpkg
  refine ⟨⟨t, a, b, q, cAB, cBD, cDA, hab, ht,
    hq, hqa, hqb, hcAB, hABhit, hcBD, hBDhit, hcDA, hDAhit⟩, ?_⟩
  by_cases havoid : ∃ r : Fin m → ℤ,
      Witness g (M : ZMod N) r ∧ r a = 0 ∧ r b = 0
  · exact Or.inr ⟨a, b, hab, havoid⟩
  · left
    let B : Finset (Fin m) := {a, b}
    let R : Finset (Fin m) := Finset.univ \ B
    let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
    have hhit : ∀ c : Fin m → ℤ, Witness g (M : ZMod N) c →
        ∃ j : Fin m, (∀ i : Fin R.card, e i ≠ j) ∧ c j ≠ 0 := by
      intro c hc
      have hor : c a ≠ 0 ∨ c b ≠ 0 := by
        by_contra hne
        push Not at hne
        exact havoid ⟨c, hc, hne.1, hne.2⟩
      rcases hor with ha | hb
      · refine ⟨a, ?_, ha⟩
        intro i hei
        have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
        have hiaB : e i ∉ B := (Finset.mem_sdiff.mp heiR).2
        exact hiaB (by simp [B, hei])
      · refine ⟨b, ?_, hb⟩
        intro i hei
        have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
        have hibB : e i ∉ B := (Finset.mem_sdiff.mp heiR).2
        exact hibB (by simp [B, hei])
    have hvalid : AdmitsValidTuple R.card M :=
      exists_validTuple_half_of_witness_transversal hN hM hg e hhit
    have hRcard : R.card = m - 2 := by
      have hBcard : B.card = 2 := by simp [B, hab]
      calc
        R.card = Finset.univ.card - B.card := by
          exact Finset.card_sdiff_of_subset (Finset.subset_univ B)
        _ = m - 2 := by simp [hBcard]
    simpa [hRcard] using hvalid

end MinModulus
