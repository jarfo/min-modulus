/-
# Eliminating the all-zero canonical singleton triangle

The all-zero triangle theory produces three pairwise-distinct pure centers,
each carrying coefficient `2` in one of the three edge witnesses.  In a
canonical subset-collision witness every successor coefficient is at most
one.  Therefore each pure center would have to be the unique anchor `0`, an
immediate contradiction.
-/
import MinModulus.G1QuarterLayerCount

namespace MinModulus

open Finset

/-- A coefficient at least two in a subset-collision vector can only occur at
the anchor coordinate. -/
theorem subsetCollisionCoeffs_heavy_coordinate_eq_anchor
    {m : ℕ} (S T : Finset (Fin m)) (e : Fin (m + 1))
    (he : 2 ≤ subsetCollisionCoeffs S T e) : e = 0 := by
  cases e using Fin.cases with
  | zero => rfl
  | succ j =>
      have hle := (subsetCollisionCoeffs_tail_bounds S T j).2
      omega

/-- Three canonical light collision witnesses cannot form an all-zero exact
omission triangle.  The three pure centers forced by validity would be
pairwise distinct, but tail lightness forces every one of them to be the
single anchor. -/
theorem canonical_exactTriangle_two_zero_not_allZero_zmod
    {N M m : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g (M : ZMod N))
    (hr : r ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hq : q ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hu : u ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    {j k z : Fin m} (hjk : j ≠ k) (hzj : z ≠ j) (hzk : z ≠ k)
    (hrB : r.val.2 = {j, k})
    (hqB : q.val.2 = {k, z})
    (huB : u.val.2 = {z, j})
    (hrzero : subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 0)
    (hqzero : subsetCollisionCoeffs q.val.1 q.val.2 j.succ = 0)
    (huzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0) : False := by
  let cr := subsetCollisionCoeffs r.val.1 r.val.2
  let cq := subsetCollisionCoeffs q.val.1 q.val.2
  let cu := subsetCollisionCoeffs u.val.1 u.val.2
  have hrcard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp hr)
  have hqcard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp hq)
  have hucard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp hu)
  have hcr : Witness g (M : ZMod N) cr :=
    witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
      hrcard r.property.2
  have hcq : Witness g (M : ZMod N) cq :=
    witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
      hqcard q.property.2
  have hcu : Witness g (M : ZMod N) cu :=
    witness_of_subsetSum_eq_add g (half_ne_zero hN hM)
      hucard u.property.2
  have hR := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) r hr hrB
  have hQ := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) q hq hqB
  have hU := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) u hu huB
  obtain ⟨x, y, v, _hx, _hy, _hv, hxy, _hyv, _hvx,
      hcrx, hcqy, hcuv⟩ :=
    exists_six_distinct_pure_centers_of_triangle_all_zero
      g hg (half_add_half hN) hcr hcq hcu j.succ k.succ z.succ
        ((Fin.succ_injective _).ne hjk)
        ((Fin.succ_injective _).ne (Ne.symm hzk))
        ((Fin.succ_injective _).ne hzj)
        (by simpa [cr] using hR)
        (by simpa [cq] using hQ)
        (by simpa [cu] using hU)
        (by simpa [cr] using hrzero)
        (by simpa [cq] using hqzero)
        (by simpa [cu] using huzero)
  have hx0 : x = 0 := subsetCollisionCoeffs_heavy_coordinate_eq_anchor
    r.val.1 r.val.2 x (by simp [cr, hcrx])
  have hy0 : y = 0 := subsetCollisionCoeffs_heavy_coordinate_eq_anchor
    q.val.1 q.val.2 y (by simp [cq, hcqy])
  exact hxy (hx0.trans hy0.symm)

/-- The genuine two-singleton residual has only two live exits.  Either the
triangle expansion produces a three-omission half-witness heavy at the
anchor, or one of the two selected target tails grows to cardinality at least
three.  The all-zero quarter branch is impossible for canonical light
collisions. -/
theorem genuineDominant_two_tail_anchorHeavy_or_growth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    (∃ c : Fin (n + 1) → ℤ, ∃ a b d : Fin (n + 1),
        Witness g ((2 ^ s * q : ℕ) :
          ZMod (2 ^ (s + 1) * q)) c ∧
        a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
        c a = -1 ∧ c b = -1 ∧ c d = -1 ∧ 2 ≤ c 0) ∨
      ∃ v : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        v ∈ canonicalSupportEscapeTargets hh r ∧ 3 ≤ v.val.2.card := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨j, k, v, u, z, hjk, hrB, hv, hu, _hvu,
      hjvAvoid, hkuAvoid, _hkv, _hju, _hzv, _hzu, hzr, hshape⟩ :=
    genuineDominant_two_tail_zeroOppositeTriangle_or_growth
      hqodd g hg r hr hres hBcard
  rcases hshape with hexact | hvgrow | hugrow
  · rcases hexact.2 with hallzero | hheavy
    · have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
        rcases mem_canonicalSupportEscapeTargets_iff.mp hv with ⟨x, hx⟩
        exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
      have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
        rcases mem_canonicalSupportEscapeTargets_iff.mp hu with ⟨x, hx⟩
        exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
      have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
        simpa [hh, criticalCanonicalReducedCollisions] using hr
      have hzj : z ≠ j := by
        intro hzj
        subst z
        exact hzr (by rw [hrB]; simp)
      have hzk : z ≠ k := by
        intro hzk
        subst z
        exact hzr (by rw [hrB]; simp)
      have hvjzero : subsetCollisionCoeffs v.val.1 v.val.2 j.succ = 0 := by
        have hjA : j ∉ v.val.1 := fun hjA ↦
          hjvAvoid (Finset.mem_union_left _ hjA)
        have hjB : j ∉ v.val.2 := fun hjB ↦
          hjvAvoid (Finset.mem_union_right _ hjB)
        simp [subsetCollisionCoeffs, hjA, hjB]
      have hukzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0 := by
        have hkA : k ∉ u.val.1 := fun hkA ↦
          hkuAvoid (Finset.mem_union_left _ hkA)
        have hkB : k ∉ u.val.2 := fun hkB ↦
          hkuAvoid (Finset.mem_union_right _ hkB)
        simp [subsetCollisionCoeffs, hkA, hkB]
      exact False.elim (canonical_exactTriangle_two_zero_not_allZero_zmod
        hN hM g hg r v u hr' hvcanonical hucanonical hjk hzj hzk
          hrB hexact.1.1 (by simpa [pair_comm] using hexact.1.2)
          hallzero.1 hvjzero hukzero)
    · exact Or.inl hheavy
  · exact Or.inr ⟨v, hv, hvgrow⟩
  · exact Or.inr ⟨u, hu, hugrow⟩

end MinModulus
