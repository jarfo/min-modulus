/-
# The zero-zero-two profile has a quarter witness

The `(0,0,2)` triangle profile does not merely certify a point whose double
is the old half target.  Its two zero-opposite edges have distinct pure
centers.  Those centers and the endpoints of the heavy edge form a balanced
four-coordinate witness at the quarter target.  This witness, including its
exact omission pair, survives reduction to the next half target.
-/
import MinModulus.G1AvoidanceQuarterTransport

namespace MinModulus

variable {m : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- A balanced pair witness at a specified target, with all four coordinates
distinct across the positive and negative pairs. -/
def WitnessBalancedPairLayerAt (g : Fin m → G) (t : G) : Prop :=
  ∃ x y a b : Fin m,
    x ≠ y ∧ a ≠ b ∧
    x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
    Witness g t (balancedPairCoeffs x y a b) ∧
    ExactOmissions (balancedPairCoeffs x y a b) {a, b}

/-- A balanced pair layer one doubling below `h`. -/
def WitnessQuarterPairLayer (g : Fin m → G) (h : G) : Prop :=
  ∃ t : G, t + t = h ∧ WitnessBalancedPairLayerAt g t

/-- The three pure half-edge vectors in a `(0,0,2)` triangle add to twice
the balanced quarter-pair vector. -/
theorem pureEdges_sum_eq_two_balancedPair
    (x y a b d : Fin m) :
    pureEdgeCoeffs d a b + pureEdgeCoeffs x b d +
        pureEdgeCoeffs y d a =
      balancedPairCoeffs x y a b + balancedPairCoeffs x y a b := by
  funext i
  simp only [pureEdgeCoeffs, balancedPairCoeffs, Pi.add_apply]
  ring_nf
  split_ifs <;> omega

/-- The `(0,0,2)` exact triangle contains an actual balanced quarter witness.
The positive coordinates are the distinct pure centers of its two
zero-opposite edges; the negative coordinates are the heavy edge. -/
theorem exactTriangleZeroZeroTwo_quarterPairLayer
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    WitnessQuarterPairLayer g h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
  obtain ⟨x, hxb, hxd, hxa, hBDx, _hBDzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcBD hcDA b d a hbd hab hBD hDA hBDa
  obtain ⟨y, hyd, hya, hyb, hDAy, _hDAzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcDA hcAB d a b hda hbd hDA hAB hDAb
  have hxy : x ≠ y := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcBD hcDA b d a x y hbd hda hab hBD hDA
      hxb hxd hyd hya hBDx hDAy
  let t : G := g x + g y - g a - g b
  have ht : t + t = h := by
    have hraw := double_balanced_center_sum_eq_target_of_pure_triangle
      g hh hcAB hcBD hcDA a b d d x y hab hbd hda hAB hBD hDA
        hda (Ne.symm hbd) hxb hxd hyd hya hABd hBDx hDAy
    calc
      t + t =
          (g d + g x + g y - g a - g b - g d) +
            (g d + g x + g y - g a - g b - g d) := by
              simp only [t]
              abel
      _ = h := hraw
  have hw : Witness g t (balancedPairCoeffs x y a b) :=
    balancedPairCoeffs_witness g x y a b hxy hab hxa hxb hya hyb rfl
  have homit : ExactOmissions (balancedPairCoeffs x y a b) {a, b} :=
    balancedPairCoeffs_exactOmissions x y a b hab hxa hxb hya hyb
  exact ⟨t, ht, x, y, a, b, hxy, hab, hxa, hxb, hya, hyb, hw, homit⟩

/-- Balanced pair layers transport under additive homomorphisms without
changing their coordinates or exact omission pair. -/
theorem balancedPairLayer_map_addMonoidHom
    (f : G →+ H) (g : Fin m → G) {t : G}
    (hlayer : WitnessBalancedPairLayerAt g t) :
    WitnessBalancedPairLayerAt (fun i ↦ f (g i)) (f t) := by
  obtain ⟨x, y, a, b, hxy, hab, hxa, hxb, hya, hyb, hw, homit⟩ :=
    hlayer
  have hw' := witness_map_addMonoidHom f g hw
  exact ⟨x, y, a, b, hxy, hab, hxa, hxb, hya, hyb, hw', homit⟩

/-- When `N=2M=4K`, a quarter pair layer maps to a balanced pair witness at
the half target `K` of the reduced tuple modulo `M`. -/
theorem quarterPairLayer_castsToHalf
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N)
    (hlayer : WitnessQuarterPairLayer g (M : ZMod N)) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    WitnessBalancedPairLayerAt (fun i ↦ f (g i)) (K : ZMod M) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  dsimp only
  obtain ⟨t, ht, hpair⟩ := hlayer
  have hpair' := balancedPairLayer_map_addMonoidHom f.toAddMonoidHom g hpair
  change WitnessBalancedPairLayerAt (fun i ↦ f (g i)) (f t) at hpair'
  rw [quarterCenter_cast_eq_half hN hM hK t ht] at hpair'
  exact hpair'

/-- Vertex-cycle branch with both divisibility profiles upgraded to actual
quarter-target witness layers. -/
def WitnessAvoidanceVertexCycleQuarterWitnessPackage
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessQuarterOmissionQuartet g h ∨ WitnessQuarterPairLayer g h ∨
      WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier in which neither residual triangle profile is a
bare coefficient or point obstruction: both carry quarter witnesses. -/
theorem criticalGenuineHeavyTwoStepEscape_triangleQuarterWitnessFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleQuarterWitnessPackage g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hcycle | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier
      hq g hg hescape
  · rcases hcycle.2 with hall | hzeroTwo | hthree
    · have hquartet := exactTriangleAllZero_quarterOmissionQuartet
        g hg (half_add_half (by rw [pow_succ]; ring)) hall
      exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inl hquartet⟩⟩
    · have hpair := exactTriangleZeroZeroTwo_quarterPairLayer
        g hg (half_add_half (by rw [pow_succ]; ring)) hzeroTwo
      exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inl hpair)⟩⟩
    · exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inr hthree)⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
