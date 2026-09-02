/-
# Global shift-source profiles on the minimal transversal

The selected transversal shift is fixed-point-free, but it need not be
injective.  Consequently one periodic component can be much smaller than the
minimal support transversal and cycle-only counting need not see `B.card`.

This file keeps every source vertex instead.  The sources split exactly
according to whether their selected target has a tail-heavy or tail-light
private witness.  Outside the established large-crossing branch there is at
most one light target, so all exceptional sources form one explicit target
fiber.  Independently, occurrences of one avoiding-witness profile have
distinct source coordinates where that profile vanishes.  Thus the earlier
cycle padding estimate globalizes without any injectivity assumption on the
shift map itself.
-/
import MinModulus.G1PrivateHeavyDominantExternalFiberCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- All transversal sources sent to one selected shift target. -/
noncomputable def minimalSupportTransversalShiftTargetFiber
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (u : ↥B) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportTransversalShiftTarget g hno hmin b = u)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportTransversalShiftTargetFiber_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (u b : ↥B) :
    b ∈ minimalSupportTransversalShiftTargetFiber g hno hmin u ↔
      minimalSupportTransversalShiftTarget g hno hmin b = u := by
  classical
  simp [minimalSupportTransversalShiftTargetFiber]

/-- Sources whose selected shift target has a tail-heavy private witness. -/
noncomputable def minimalSupportTransversalShiftHeavyTargetSources
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportTransversalShiftTarget g hno hmin b ∈
      minimalSupportPrivateTailHeavyVertices g h hmin)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportTransversalShiftHeavyTargetSources_iff
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (b : ↥B) :
    b ∈ minimalSupportTransversalShiftHeavyTargetSources g h hno hmin ↔
      minimalSupportTransversalShiftTarget g hno hmin b ∈
        minimalSupportPrivateTailHeavyVertices g h hmin := by
  classical
  simp [minimalSupportTransversalShiftHeavyTargetSources]

/-- Sources whose selected shift target has a tail-light private witness. -/
noncomputable def minimalSupportTransversalShiftLightTargetSources
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportTransversalShiftTarget g hno hmin b ∈
      minimalSupportPrivateTailLightVertices g h hmin)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportTransversalShiftLightTargetSources_iff
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (b : ↥B) :
    b ∈ minimalSupportTransversalShiftLightTargetSources g h hno hmin ↔
      minimalSupportTransversalShiftTarget g hno hmin b ∈
        minimalSupportPrivateTailLightVertices g h hmin := by
  classical
  simp [minimalSupportTransversalShiftLightTargetSources]

omit [DecidableEq G] in
/-- The heavy-target and light-target sources are an exact partition of all
sources, whether or not the selected shift map is injective. -/
theorem card_minimalSupportTransversalShiftHeavyTargetSources_add_light
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportTransversalShiftHeavyTargetSources g h hno hmin).card +
      (minimalSupportTransversalShiftLightTargetSources g h hno hmin).card =
        B.card := by
  classical
  let H := minimalSupportTransversalShiftHeavyTargetSources g h hno hmin
  let L := minimalSupportTransversalShiftLightTargetSources g h hno hmin
  have hdisj : Disjoint H L := by
    rw [Finset.disjoint_left]
    intro b hbH hbL
    have hbHeavy :=
      (mem_minimalSupportTransversalShiftHeavyTargetSources_iff
        g h hno hmin b).mp hbH
    have hbLight :=
      (mem_minimalSupportTransversalShiftLightTargetSources_iff
        g h hno hmin b).mp hbL
    obtain ⟨k, hk⟩ :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff
        g h hmin _).mp hbHeavy
    have hk' :=
      (mem_minimalSupportPrivateTailLightVertices_iff
        g h hmin _).mp hbLight k
    omega
  have hunion : H ∪ L = Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hbLight : ∀ k : Fin m,
        minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) k.succ ≤ 1
    · exact Or.inr
        ((mem_minimalSupportTransversalShiftLightTargetSources_iff
          g h hno hmin b).mpr
            ((mem_minimalSupportPrivateTailLightVertices_iff
              g h hmin _).mpr hbLight))
    · left
      push Not at hbLight
      obtain ⟨k, hk⟩ := hbLight
      exact (mem_minimalSupportTransversalShiftHeavyTargetSources_iff
        g h hno hmin b).mpr
          ((mem_minimalSupportPrivateTailHeavyVertices_iff
            g h hmin _).mpr ⟨k, by omega⟩)
  change H.card + L.card = B.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

omit [DecidableEq G] in
/-- If there is at most one light private owner, all sources with a light
target are either absent or constitute the complete fiber over that owner. -/
theorem shiftLightTargetSources_eq_empty_or_singleTargetFiber
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hlight :
      (minimalSupportPrivateTailLightVertices g h hmin).card ≤ 1) :
    minimalSupportTransversalShiftLightTargetSources g h hno hmin = ∅ ∨
      ∃ u : ↥B,
        u ∈ minimalSupportPrivateTailLightVertices g h hmin ∧
        minimalSupportTransversalShiftLightTargetSources g h hno hmin =
          minimalSupportTransversalShiftTargetFiber g hno hmin u := by
  classical
  let S := minimalSupportTransversalShiftLightTargetSources g h hno hmin
  by_cases hS : S = ∅
  · exact Or.inl hS
  · right
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    let u := minimalSupportTransversalShiftTarget g hno hmin b
    have huLight : u ∈ minimalSupportPrivateTailLightVertices g h hmin :=
      (mem_minimalSupportTransversalShiftLightTargetSources_iff
        g h hno hmin b).mp hb
    refine ⟨u, huLight, ?_⟩
    ext c
    constructor
    · intro hc
      have hcLight :=
        (mem_minimalSupportTransversalShiftLightTargetSources_iff
          g h hno hmin c).mp hc
      have htarget :
          minimalSupportTransversalShiftTarget g hno hmin c = u :=
        (Finset.card_le_one.mp hlight) _ hcLight _ huLight
      exact (mem_minimalSupportTransversalShiftTargetFiber_iff
        g hno hmin u c).mpr htarget
    · intro hc
      have htarget :=
        (mem_minimalSupportTransversalShiftTargetFiber_iff
          g hno hmin u c).mp hc
      apply (mem_minimalSupportTransversalShiftLightTargetSources_iff
        g h hno hmin c).mpr
      rwa [htarget]

/-- In the critical-depth regime, global source counting reduces the failure
of an all-heavy-target statement to one explicit high-indegree light target. -/
theorem critical_largeCross_or_shiftLightTargetSources_empty_or_singleFiber
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      minimalSupportTransversalShiftLightTargetSources g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin = ∅ ∨
      ∃ u : ↥B,
        u ∈ minimalSupportPrivateTailLightVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
        minimalSupportTransversalShiftLightTargetSources g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin =
          minimalSupportTransversalShiftTargetFiber g hno hmin u := by
  rcases critical_largeCross_or_privateTailLightVertices_card_le_one
      hq g hg hmin hB with hlarge | hlight
  · exact Or.inl hlarge
  · exact Or.inr
      (shiftLightTargetSources_eq_empty_or_singleTargetFiber
        g _ hno hmin hlight)

/-- Cardinal form of the global source split.  Outside large crossing, either
every one of the `B.card` sources has a heavy target, or the exact deficit is
the indegree of the unique light target. -/
theorem critical_largeCross_or_allShiftTargetsHeavy_or_singleLightTargetFiber
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      (minimalSupportTransversalShiftLightTargetSources g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin = ∅ ∧
        (minimalSupportTransversalShiftHeavyTargetSources g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin).card =
            B.card) ∨
      ∃ u : ↥B,
        u ∈ minimalSupportPrivateTailLightVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
        minimalSupportTransversalShiftLightTargetSources g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin =
          minimalSupportTransversalShiftTargetFiber g hno hmin u ∧
        (minimalSupportTransversalShiftHeavyTargetSources g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hno hmin).card +
          (minimalSupportTransversalShiftTargetFiber g hno hmin u).card =
            B.card := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hpartition :=
    card_minimalSupportTransversalShiftHeavyTargetSources_add_light
      g h hno hmin
  rcases critical_largeCross_or_shiftLightTargetSources_empty_or_singleFiber
      hq g hg hno hmin hB with hlarge | hempty | ⟨u, hu, hfiber⟩
  · exact Or.inl hlarge
  · right
    left
    refine ⟨hempty, ?_⟩
    rw [hempty] at hpartition
    simpa [h] using hpartition
  · right
    right
    refine ⟨u, hu, hfiber, ?_⟩
    rw [hfiber] at hpartition
    simpa [h] using hpartition

/-- All sources carrying one complete avoiding-witness profile. -/
noncomputable def minimalSupportTransversalAvoidingWitnessFiber
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (r : Fin (m + 1) → ℤ) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportAvoidingWitness g hno b = r)

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportTransversalAvoidingWitnessFiber_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (r : Fin (m + 1) → ℤ) (b : ↥B) :
    b ∈ minimalSupportTransversalAvoidingWitnessFiber g hno r ↔
      minimalSupportAvoidingWitness g hno b = r := by
  classical
  simp [minimalSupportTransversalAvoidingWitnessFiber]

omit [DecidableEq G] in
/-- Global source-zero padding: reuse of one avoiding profile over all
transversal sources consumes distinct coordinates, independently of any
collision among their selected targets. -/
theorem card_transversalAvoidingWitnessFiber_sub_one_le_paddingDepth
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (r : Fin (m + 1) → ℤ) (hr : Witness g h r)
    (hrLight : ∀ k : Fin m, r k.succ ≤ 1) :
    (minimalSupportTransversalAvoidingWitnessFiber
      (B := B) g hno r).card - 1 ≤
      m - ((reducedCollisionOfTailLightWitness g hr hrLight).val.1 ∪
        (reducedCollisionOfTailLightWitness g hr hrLight).val.2).card := by
  classical
  let F := minimalSupportTransversalAvoidingWitnessFiber (B := B) g hno r
  let source : ↥B → Fin (m + 1) := fun b ↦ b
  let S := F.image source
  let T := (reducedCollisionOfTailLightWitness g hr hrLight).val.1 ∪
    (reducedCollisionOfTailLightWitness g hr hrLight).val.2
  let TS := T.image Fin.succ
  let U := (Finset.univ : Finset (Fin (m + 1))).erase 0
  have hsourceInjective : Function.Injective source := by
    intro b c hbc
    exact Subtype.ext hbc
  have hScard : S.card = F.card := by
    exact Finset.card_image_of_injective F hsourceInjective
  have hsourceZero : ∀ x ∈ S, r x = 0 := by
    intro x hx
    obtain ⟨b, hbF, rfl⟩ := Finset.mem_image.mp hx
    have hbProfile :=
      (mem_minimalSupportTransversalAvoidingWitnessFiber_iff
        g hno r b).mp hbF
    rw [← hbProfile]
    simpa [source] using minimalSupportAvoidingWitness_eq_zero g hno b
  have hdisjoint : Disjoint (S.erase 0) TS := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    have hxZero := hsourceZero x (Finset.mem_of_mem_erase hxS)
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_image.mp hxT
    change j ∈ witnessPositiveTail r ∪ witnessNegativeTail r at hjT
    rcases Finset.mem_union.mp hjT with hjPos | hjNeg
    · simp [witnessPositiveTail] at hjPos
      omega
    · simp [witnessNegativeTail] at hjNeg
      omega
  have hSsubset : S.erase 0 ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
  have hTSsubset : TS ⊆ U := by
    intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩
  have hTScard : TS.card = T.card := by
    exact Finset.card_image_of_injective T (Fin.succ_injective m)
  have hcapacity : (S.erase 0).card + T.card ≤ m := by
    have hcard := Finset.card_le_card
      (Finset.union_subset hSsubset hTSsubset)
    rw [Finset.card_union_of_disjoint hdisjoint, hTScard] at hcard
    simpa [U] using hcard
  have hsourceCard : F.card - 1 ≤ (S.erase 0).card := by
    by_cases h0 : 0 ∈ S
    · have herase := Finset.card_erase_add_one h0
      omega
    · rw [(Finset.erase_eq_self.mpr h0), hScard]
      exact Nat.sub_le _ _
  change F.card - 1 ≤ m - T.card
  omega

/-- Exponential canonical collision weight forced by reuse of one avoiding
profile across the full transversal. -/
theorem pow_card_transversalAvoidingWitnessFiber_sub_one_le_canonicalWeight
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (r : Fin (m + 1) → ℤ) (hr : Witness g h r)
    (hrLight : ∀ k : Fin m, r k.succ ≤ 1) :
    2 ^ ((minimalSupportTransversalAvoidingWitnessFiber
      (B := B) g hno r).card - 1) ≤
      reducedCollisionWeight (m := m)
        (canonicalCollisionOfTailLightWitness g hh r hr hrLight) := by
  let raw := reducedCollisionOfTailLightWitness g hr hrLight
  have hdepth :=
    card_transversalAvoidingWitnessFiber_sub_one_le_paddingDepth
      (B := B) g hno r hr hrLight
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdepth
  calc
    2 ^ ((minimalSupportTransversalAvoidingWitnessFiber
          (B := B) g hno r).card - 1) ≤
        2 ^ (m - (raw.val.1 ∪ raw.val.2).card) := by
      simpa [raw] using hpow
    _ = reducedCollisionWeight (m := m) raw := by
      rfl
    _ = reducedCollisionWeight (m := m)
        (canonicalCollisionOfTailLightWitness g hh r hr hrLight) := by
      simpa [canonicalCollisionOfTailLightWitness, raw] using
        (canonicalizeReducedCollision_weight hh raw).symm

end MinModulus
