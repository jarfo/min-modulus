/-
# Complete exact-triangle profiles under no common touch

The exact cycle triangle has opposite coefficients in `{0,1,2}`.  A `2`
forces the other two opposites to be zero.  With no `2`, two adjacent `1`s
force common touch, while a single `1` expands to a three-omission witness.
Thus the only exact profiles which remain under no common touch are
`(0,0,0)`, `(0,0,2)` up to rotation, or a three-omission escape.
-/
import MinModulus.G1AvoidanceExactTriangleZero

namespace MinModulus

variable {m : ℕ}

/-- An exact omission triangle with all three opposite coefficients zero. -/
def WitnessExactTriangleAllZero
    {G : Type*} [AddCommGroup G] (g : Fin m → G) (h : G) : Prop :=
  ∃ cAB cBD cDA : Fin m → ℤ, ∃ a b d : Fin m,
    Witness g h cAB ∧ Witness g h cBD ∧ Witness g h cDA ∧
    a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
    (∀ i, cAB i = -1 ↔ i = a ∨ i = b) ∧
    (∀ i, cBD i = -1 ↔ i = b ∨ i = d) ∧
    (∀ i, cDA i = -1 ↔ i = d ∨ i = a) ∧
    cAB d = 0 ∧ cBD a = 0 ∧ cDA b = 0

/-- An exact omission triangle with profile `(2,0,0)`, oriented so the first
edge carries the heavy opposite. -/
def WitnessExactTriangleZeroZeroTwo
    {G : Type*} [AddCommGroup G] (g : Fin m → G) (h : G) : Prop :=
  ∃ cAB cBD cDA : Fin m → ℤ, ∃ a b d : Fin m,
    Witness g h cAB ∧ Witness g h cBD ∧ Witness g h cDA ∧
    a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
    (∀ i, cAB i = -1 ↔ i = a ∨ i = b) ∧
    (∀ i, cBD i = -1 ↔ i = b ∨ i = d) ∧
    (∀ i, cDA i = -1 ↔ i = d ∨ i = a) ∧
    cAB d = 2 ∧ cBD a = 0 ∧ cDA b = 0

/-- Under no common touch, the light profile of an exact triangle always
expands to three distinct omissions. -/
theorem threeDistinctOmissions_of_lightTriangle_of_noCommonTouch
    {G : Type*} [AddCommGroup G]
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {cAB cBD cDA : Fin m → ℤ}
    (hcAB : Witness g h cAB) (hcBD : Witness g h cBD)
    (hcDA : Witness g h cDA)
    (a b d : Fin m) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hDAb : cDA b = 1) : WitnessThreeDistinctOmissions g h := by
  rcases common_touched_or_exists_three_omission_witness_of_light_triangle
      g hg hh hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA hDAb with
    htouch | hthree
  · exact False.elim (hno htouch)
  · obtain ⟨c, i, j, k, hc, hij, hjk, hki, hci, hcj, hck⟩ := hthree
    exact ⟨c, i, j, k, hc, hij, hki.symm, hjk, hci, hcj, hck⟩

/-- Complete exact-triangle classification under no common touch at an even
cyclic modulus. -/
theorem exactOmissionTriangle_profiles_of_noCommonTouch_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0)
    (htriangle : WitnessExactOmissionTriangle g (M : ZMod N)) :
    WitnessExactTriangleAllZero g (M : ZMod N) ∨
      WitnessExactTriangleZeroZeroTwo g (M : ZMod N) ∨
      WitnessThreeDistinctOmissions g (M : ZMod N) := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA⟩ := htriangle
  have hclass := triangle_opposite_coefficients_zero_one_or_two
    g hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA
  by_cases hAB2 : cAB d = 2
  · have hzero := triangle_other_opposites_zero_of_opposite_eq_two
      g hg (half_add_half hN) hcAB hcBD hcDA
        a b d hab hbd hda hAB hBD hDA hAB2
    exact Or.inr (Or.inl ⟨cAB, cBD, cDA, a, b, d,
      hcAB, hcBD, hcDA, hab, hbd, hda, hAB, hBD, hDA,
      hAB2, hzero.1, hzero.2⟩)
  by_cases hBD2 : cBD a = 2
  · have hzero := triangle_other_opposites_zero_of_opposite_eq_two
      g hg (half_add_half hN) hcBD hcDA hcAB
        b d a hbd hda hab hBD hDA hAB hBD2
    exact Or.inr (Or.inl ⟨cBD, cDA, cAB, b, d, a,
      hcBD, hcDA, hcAB, hbd, hda, hab, hBD, hDA, hAB,
      hBD2, hzero.1, hzero.2⟩)
  by_cases hDA2 : cDA b = 2
  · have hzero := triangle_other_opposites_zero_of_opposite_eq_two
      g hg (half_add_half hN) hcDA hcAB hcBD
        d a b hda hab hbd hDA hAB hBD hDA2
    exact Or.inr (Or.inl ⟨cDA, cAB, cBD, d, a, b,
      hcDA, hcAB, hcBD, hda, hab, hbd, hDA, hAB, hBD,
      hDA2, hzero.1, hzero.2⟩)
  have hAB01 : cAB d = 0 ∨ cAB d = 1 := by
    rcases hclass.1 with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr h1
    · exact False.elim (hAB2 h2)
  have hBD01 : cBD a = 0 ∨ cBD a = 1 := by
    rcases hclass.2.1 with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr h1
    · exact False.elim (hBD2 h2)
  have hDA01 : cDA b = 0 ∨ cDA b = 1 := by
    rcases hclass.2.2 with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr h1
    · exact False.elim (hDA2 h2)
  rcases hAB01 with hAB0 | hAB1
  · rcases hBD01 with hBD0 | hBD1
    · rcases hDA01 with hDA0 | hDA1
      · exact Or.inl ⟨cAB, cBD, cDA, a, b, d,
          hcAB, hcBD, hcDA, hab, hbd, hda, hAB, hBD, hDA,
          hAB0, hBD0, hDA0⟩
      · exact Or.inr (Or.inr
          (threeDistinctOmissions_of_lightTriangle_of_noCommonTouch
            g hg (half_add_half hN) hno hcAB hcBD hcDA
              a b d hab hbd hda hAB hBD hDA hDA1))
    · rcases hDA01 with hDA0 | hDA1
      · exact Or.inr (Or.inr
          (threeDistinctOmissions_of_lightTriangle_of_noCommonTouch
            g hg (half_add_half hN) hno hcDA hcAB hcBD
              d a b hda hab hbd hDA hAB hBD hBD1))
      · exact False.elim (hno
          (common_touched_of_two_adjacent_light_opposites_zmod
            hN hM g hg hcBD hcDA b d a hbd hda hab
              hBD hDA hBD1 hDA1))
  · rcases hBD01 with hBD0 | hBD1
    · rcases hDA01 with hDA0 | hDA1
      · exact Or.inr (Or.inr
          (threeDistinctOmissions_of_lightTriangle_of_noCommonTouch
            g hg (half_add_half hN) hno hcBD hcDA hcAB
              b d a hbd hda hab hBD hDA hAB hAB1))
      · exact False.elim (hno
          (common_touched_of_two_adjacent_light_opposites_zmod
            hN hM g hg hcDA hcAB d a b hda hab hbd
              hDA hAB hDA1 hAB1))
    · exact False.elim (hno
        (common_touched_of_two_adjacent_light_opposites_zmod
          hN hM g hg hcAB hcBD a b d hab hbd hda
            hAB hBD hAB1 hBD1))

/-- Vertex-cycle branch after the complete exact-triangle profile split. -/
def WitnessAvoidanceVertexCycleProfilePackage
    {G : Type*} [AddCommGroup G]
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessExactTriangleAllZero g h ∨
      WitnessExactTriangleZeroZeroTwo g h ∨
      WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with the source-simple cycle reduced to the two
divisibility profiles `(0,0,0)`, `(0,0,2)`, or a three-omission escape. -/
theorem criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleProfilePackage g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  letI : NeZero (2 ^ (s + 1) * q) := ⟨Nat.ne_of_gt
    (mul_pos (pow_pos (by norm_num) (s + 1)) (Odd.pos hq))⟩
  obtain ⟨hno, p, d, hmin, hcycle | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_vertexCycleTriangleFrontier
      hq g hg hescape
  · rcases hcycle.2 with htriangle | hthree
    · have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
        rw [pow_succ]
        ring
      have hM : 0 < 2 ^ s * q :=
        mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
      have hprofiles := exactOmissionTriangle_profiles_of_noCommonTouch_zmod
        hN hM g hg hno htriangle
      exact ⟨hno, p, d, hmin, Or.inl ⟨hcycle.1, hprofiles⟩⟩
    · exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inr hthree)⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
