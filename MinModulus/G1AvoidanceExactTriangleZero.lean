/-
# Zero-opposite structure of the exact cycle triangle

At any even cyclic modulus, an exact omission triangle whose three opposite
coefficients are positive forces common touch.  Under the retained failure of
common touch, at least one opposite coefficient is therefore zero.  The
existing triangle algebra then makes that edge pure: its two positive units
are concentrated as a coefficient `2` at one coordinate outside the triangle.
-/
import MinModulus.G1AvoidancePeriodThreeTriangle

namespace MinModulus

variable {m : ℕ}

/-- One pure zero-opposite edge extracted from an exact omission triangle. -/
def WitnessPureZeroTriangleEdge
    {G : Type*} [AddCommGroup G] (g : Fin m → G) (h : G) : Prop :=
  ∃ c : Fin m → ℤ, ∃ p q r e : Fin m,
    Witness g h c ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
    (∀ i, c i = -1 ↔ i = p ∨ i = q) ∧
    c r = 0 ∧ e ≠ p ∧ e ≠ q ∧ e ≠ r ∧ c e = 2 ∧
    ∀ j : Fin m, j ≠ p → j ≠ q → j ≠ r → j ≠ e → c j = 0

/-- Under failure of common touch, an exact triangle over an even cyclic
group has a zero opposite coefficient. -/
theorem exactOmissionTriangle_zeroOpposite_of_noCommonTouch_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0)
    (htriangle : WitnessExactOmissionTriangle g (M : ZMod N)) :
    ∃ cAB cBD cDA : Fin m → ℤ, ∃ a b d : Fin m,
      Witness g (M : ZMod N) cAB ∧ Witness g (M : ZMod N) cBD ∧
      Witness g (M : ZMod N) cDA ∧
      a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
      (∀ i, cAB i = -1 ↔ i = a ∨ i = b) ∧
      (∀ i, cBD i = -1 ↔ i = b ∨ i = d) ∧
      (∀ i, cDA i = -1 ↔ i = d ∨ i = a) ∧
      (cAB d = 0 ∨ cBD a = 0 ∨ cDA b = 0) := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA⟩ := htriangle
  have hclass := triangle_opposite_coefficients_zero_one_or_two
    g hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA
  by_cases hAB0 : cAB d = 0
  · exact ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
      hab, hbd, hda, hAB, hBD, hDA, Or.inl hAB0⟩
  by_cases hBD0 : cBD a = 0
  · exact ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
      hab, hbd, hda, hAB, hBD, hDA, Or.inr (Or.inl hBD0)⟩
  by_cases hDA0 : cDA b = 0
  · exact ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
      hab, hbd, hda, hAB, hBD, hDA, Or.inr (Or.inr hDA0)⟩
  have hABpos : 1 ≤ cAB d := by
    rcases hclass.1 with h0 | h1 | h2 <;> omega
  have hBDpos : 1 ≤ cBD a := by
    rcases hclass.2.1 with h0 | h1 | h2 <;> omega
  have hDApos : 1 ≤ cDA b := by
    rcases hclass.2.2 with h0 | h1 | h2 <;> omega
  exact False.elim (hno (common_touched_of_triangle_positive_zmod
    hN hM g hg hcAB hcBD hcDA a b d hab hbd hda
      hAB hBD hDA hABpos hBDpos hDApos))

/-- The zero edge supplied by the exact triangle is pure, with one external
coefficient `2`. -/
theorem exactOmissionTriangle_pureZeroEdge_of_noCommonTouch_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0)
    (htriangle : WitnessExactOmissionTriangle g (M : ZMod N)) :
    WitnessPureZeroTriangleEdge g (M : ZMod N) := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hAB0 | hBD0 | hDA0⟩ :=
    exactOmissionTriangle_zeroOpposite_of_noCommonTouch_zmod
      hN hM g hg hno htriangle
  · obtain ⟨e, hea, heb, hed, hce, hrest⟩ :=
      exists_pure_companion_two_of_triangle_zero_opposite
        g hg (half_add_half hN) hcAB hcBD a b d hab hda hAB hBD hAB0
    exact ⟨cAB, a, b, d, e, hcAB, hab, hbd, hda,
      hAB, hAB0, hea, heb, hed, hce, hrest⟩
  · obtain ⟨e, heb, hed, hea, hce, hrest⟩ :=
      exists_pure_companion_two_of_triangle_zero_opposite
        g hg (half_add_half hN) hcBD hcDA b d a hbd hab hBD hDA hBD0
    exact ⟨cBD, b, d, a, e, hcBD, hbd, hda, hab,
      hBD, hBD0, heb, hed, hea, hce, hrest⟩
  · obtain ⟨e, hed, hea, heb, hce, hrest⟩ :=
      exists_pure_companion_two_of_triangle_zero_opposite
        g hg (half_add_half hN) hcDA hcAB d a b hda hbd hDA hAB hDA0
    exact ⟨cDA, d, a, b, e, hcDA, hda, hab, hbd,
      hDA, hDA0, hed, hea, heb, hce, hrest⟩

/-- Vertex-cycle branch after exploiting the exact triangle's forced pure
zero edge. -/
def WitnessAvoidanceVertexCyclePureTrianglePackage
    {G : Type*} [AddCommGroup G]
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessPureZeroTriangleEdge g h ∨ WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with the exact cycle triangle converted to a pure
zero edge at every two-adic depth. -/
theorem criticalGenuineHeavyTwoStepEscape_pureTriangleFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCyclePureTrianglePackage g hg
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
      have hpure := exactOmissionTriangle_pureZeroEdge_of_noCommonTouch_zmod
        hN hM g hg hno htriangle
      exact ⟨hno, p, d, hmin, Or.inl ⟨hcycle.1, Or.inl hpure⟩⟩
    · exact ⟨hno, p, d, hmin, Or.inl ⟨hcycle.1, Or.inr hthree⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
