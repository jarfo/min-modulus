/-
# The exact singleton-target fan enters the triangle theory

The two-singleton coupling produces either tail growth or the exact omission
triangle with edges `{j,k}`, `{k,z}`, `{z,j}`.  Canonical reduced collisions
already carry the corresponding light subset-collision witnesses.  This file
bridges their negative tails to `ExactOmissions` and invokes the general
positive-triangle theorem.

Thus an exact fan either closes common touch or has a zero opposite
coefficient.  In the genuine critical residual common touch is excluded, so
the surviving two-coordinate root tail yields a zero-opposite exact triangle
or strict growth in one selected target tail.
-/
import MinModulus.G1TwoSingletonCoupling

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A canonical reduced collision whose negative tail is a pair gives a
subset-collision witness with exactly the corresponding two successor
omissions. -/
theorem canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    {j k : Fin m} (hB : r.val.2 = {j, k}) :
    ∀ i : Fin (m + 1),
      subsetCollisionCoeffs r.val.1 r.val.2 i = -1 ↔
        i = j.succ ∨ i = k.succ := by
  classical
  have hcard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp hr)
  have hexact := subsetCollisionCoeffs_exactOmissions
    r.val.1 r.val.2 hcard
  have hsdiff : r.val.2 \ r.val.1 = r.val.2 :=
    Finset.sdiff_eq_self_of_disjoint r.property.1.symm
  intro i
  rw [hexact i, subsetCollisionOmissions, hsdiff, hB]
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, hxi⟩
    have hxjk : x = j ∨ x = k := by simpa using hx
    rcases hxjk with rfl | rfl
    · exact Or.inl hxi.symm
    · exact Or.inr hxi.symm
  · intro hi
    rcases hi with rfl | rfl
    · exact Finset.mem_image.mpr ⟨j, by simp, rfl⟩
    · exact Finset.mem_image.mpr ⟨k, by simp, rfl⟩

section CyclicExactTriangle

/-- An exact triangle of canonical reduced half-collisions either has a
common touched coordinate or one of its three opposite tail coefficients is
zero.  This holds at every even cyclic modulus, not only the first-even
stratum. -/
theorem canonical_exactTriangle_commonTouched_or_zero_opposite_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g (M : ZMod N))
    (hr : r ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hq : q ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hu : u ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    {j k z : Fin m} (hjk : j ≠ k) (hzj : z ≠ j) (hzk : z ≠ k)
    (hrB : r.val.2 = {j, k})
    (hqB : q.val.2 = {k, z})
    (huB : u.val.2 = {z, j}) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0) ∨
    subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 0 ∨
    subsetCollisionCoeffs q.val.1 q.val.2 j.succ = 0 ∨
    subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0 := by
  classical
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
  have hUraw :=
    canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
      (half_add_half hN) u hu huB
  have hU : ∀ i : Fin (m + 1), cu i = -1 ↔
      i = z.succ ∨ i = j.succ := by
    intro i
    simpa [cu] using hUraw i
  have hclass := triangle_opposite_coefficients_zero_one_or_two
    g hcr hcq hcu j.succ k.succ z.succ
      (by exact (Fin.succ_injective _).ne hjk)
      (by exact (Fin.succ_injective _).ne (Ne.symm hzk))
      (by exact (Fin.succ_injective _).ne hzj)
      (by simpa [cr] using hR)
      (by simpa [cq] using hQ)
      hU
  by_cases hrzero : cr z.succ = 0
  · exact Or.inr (Or.inl (by simpa [cr] using hrzero))
  by_cases hqzero : cq j.succ = 0
  · exact Or.inr (Or.inr (Or.inl (by simpa [cq] using hqzero)))
  by_cases huzero : cu k.succ = 0
  · exact Or.inr (Or.inr (Or.inr (by simpa [cu] using huzero)))
  have hrpos : 1 ≤ cr z.succ := by
    rcases hclass.1 with h0 | h1 | h2 <;> omega
  have hqpos : 1 ≤ cq j.succ := by
    rcases hclass.2.1 with h0 | h1 | h2 <;> omega
  have hupos : 1 ≤ cu k.succ := by
    rcases hclass.2.2 with h0 | h1 | h2 <;> omega
  exact Or.inl (common_touched_of_triangle_positive_zmod
    hN hM g hg hcr hcq hcu j.succ k.succ z.succ
      ((Fin.succ_injective _).ne hjk)
      ((Fin.succ_injective _).ne (Ne.symm hzk))
      ((Fin.succ_injective _).ne hzj)
      (by simpa [cr] using hR)
      (by simpa [cq] using hQ)
      hU hrpos hqpos hupos)

/-- If the two selected-target opposite coefficients are already zero, the
remaining root opposite is either zero—forcing the all-zero divisibility
obstruction—or it is one, and the light-triangle theorem gives common touch
or a new three-omission witness with a coefficient at least two. -/
theorem canonical_exactTriangle_two_zero_allZero_or_commonTouched_or_heavyThree_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M) (hM : 0 < M)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g (M : ZMod N))
    (hr : r ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hq : q ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    (hu : u ∈ canonicalReducedCollisions (g := g) (half_add_half hN))
    {j k z : Fin m} (hjk : j ≠ k) (hzj : z ≠ j) (hzk : z ≠ k)
    (hrB : r.val.2 = {j, k})
    (hqB : q.val.2 = {k, z})
    (huB : u.val.2 = {z, j})
    (hqzero : subsetCollisionCoeffs q.val.1 q.val.2 j.succ = 0)
    (huzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0) :
    (subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 0 ∧ 4 ∣ N) ∨
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0) ∨
    ∃ c : Fin (m + 1) → ℤ, ∃ a b d e : Fin (m + 1),
      Witness g (M : ZMod N) c ∧
      a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
      c a = -1 ∧ c b = -1 ∧ c d = -1 ∧ 2 ≤ c e := by
  classical
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
  by_cases hrzero : cr z.succ = 0
  · apply Or.inl
    refine ⟨by simpa [cr] using hrzero, ?_⟩
    exact four_dvd_of_triangle_all_zero_zmod
      hN g hg hcr hcq hcu j.succ k.succ z.succ
        ((Fin.succ_injective _).ne hjk)
        ((Fin.succ_injective _).ne (Ne.symm hzk))
        ((Fin.succ_injective _).ne hzj)
        (by simpa [cr] using hR)
        (by simpa [cq] using hQ)
        (by simpa [cu] using hU)
        hrzero (by simpa [cq] using hqzero)
        (by simpa [cu] using huzero)
  · have hclass := triangle_opposite_coefficients_zero_one_or_two
      g hcr hcq hcu j.succ k.succ z.succ
        ((Fin.succ_injective _).ne hjk)
        ((Fin.succ_injective _).ne (Ne.symm hzk))
        ((Fin.succ_injective _).ne hzj)
        (by simpa [cr] using hR)
        (by simpa [cq] using hQ)
        (by simpa [cu] using hU)
    have hrle : cr z.succ ≤ 1 :=
      (subsetCollisionCoeffs_tail_bounds r.val.1 r.val.2 z).2
    have hrone : cr z.succ = 1 := by
      rcases hclass.1 with h0 | h1 | h2
      · exact False.elim (hrzero h0)
      · exact h1
      · omega
    have hlight :=
      common_touched_or_exists_three_omission_heavy_witness_of_light_triangle
        g hg (half_add_half hN) hcq hcu hcr
          k.succ z.succ j.succ
          ((Fin.succ_injective _).ne (Ne.symm hzk))
          ((Fin.succ_injective _).ne hzj)
          ((Fin.succ_injective _).ne hjk)
          (by simpa [cq] using hQ)
          (by simpa [cu] using hU)
          (by simpa [cr] using hR)
          hrone
    rcases hlight with htouch | hheavy
    · exact Or.inr (Or.inl htouch)
    · exact Or.inr (Or.inr hheavy)

end CyclicExactTriangle

section CriticalTriangleOrGrowth

/-- With an odd cofactor, divisibility of the critical modulus by four forces
positive two-adic depth. -/
theorem one_le_criticalIndex_of_four_dvd
    {s q : ℕ} (hqodd : Odd q) (hfour : 4 ∣ 2 ^ (s + 1) * q) : 1 ≤ s := by
  by_contra hs
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
  subst s
  rcases hqodd with ⟨t, ht⟩
  rcases hfour with ⟨d, hd⟩
  norm_num at hd
  omega

/-- The two-coordinate genuine critical residual is no longer an abstract
one-root profile.  Its selected targets produce strict negative-tail growth,
or an exact two-zero triangle which is either all-zero (and forces `4 ∣ N`)
or sprouts a heavy three-omission witness. -/
theorem genuineDominant_two_tail_zeroOppositeTriangle_or_growth
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
    ∃ j k : Fin n,
      ∃ v u : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      ∃ z : Fin n,
        j ≠ k ∧ r.val.2 = {j, k} ∧
        v ∈ canonicalSupportEscapeTargets hh r ∧
        u ∈ canonicalSupportEscapeTargets hh r ∧ v ≠ u ∧
        j ∉ reducedCollisionSupport v ∧
        k ∉ reducedCollisionSupport u ∧
        k ∈ v.val.2 ∧ j ∈ u.val.2 ∧
        z ∈ v.val.2 ∧ z ∈ u.val.2 ∧ z ∉ r.val.2 ∧
        (((v.val.2 = {k, z} ∧ u.val.2 = {j, z}) ∧
            ((subsetCollisionCoeffs r.val.1 r.val.2 z.succ = 0 ∧
                4 ∣ 2 ^ (s + 1) * q ∧ 1 ≤ s) ∨
              ∃ c : Fin (n + 1) → ℤ,
                ∃ a b d e : Fin (n + 1),
                Witness g ((2 ^ s * q : ℕ) :
                  ZMod (2 ^ (s + 1) * q)) c ∧
                a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
                c a = -1 ∧ c b = -1 ∧ c d = -1 ∧ 2 ≤ c e)) ∨
          3 ≤ v.val.2.card ∨ 3 ≤ u.val.2.card) := by
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
  obtain ⟨j, k, v, u, z, hjk, hrB, hv, hu, hvu,
      hjvAvoid, hkuAvoid, hkv, hju, hzv, hzu, hzr, hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  have hv' : v ∈ canonicalSupportEscapeTargets hh r := by
    simpa only [hh] using hv
  have hu' : u ∈ canonicalSupportEscapeTargets hh r := by
    simpa only [hh] using hu
  refine ⟨j, k, v, u, z, hjk, hrB, hv', hu', hvu,
    hjvAvoid, hkuAvoid, hkv, hju, hzv, hzu, hzr, ?_⟩
  rcases hshape with hexact | hvgrow | hugrow
  · have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      rcases mem_canonicalSupportEscapeTargets_iff.mp hv' with ⟨x, hx⟩
      exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
    have hucanonical : u ∈ canonicalReducedCollisions (g := g) hh := by
      rcases mem_canonicalSupportEscapeTargets_iff.mp hu' with ⟨x, hx⟩
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
    have htri :=
      canonical_exactTriangle_two_zero_allZero_or_commonTouched_or_heavyThree_zmod
        hN hM g hg r v u hr' hvcanonical hucanonical
          hjk hzj hzk hrB hexact.1
          (by simpa [pair_comm] using hexact.2) hvjzero hukzero
    rcases htri with hallzero | htouch | hheavy
    · exact Or.inl ⟨hexact, Or.inl
        ⟨hallzero.1, hallzero.2,
          one_le_criticalIndex_of_four_dvd hqodd hallzero.2⟩⟩
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact Or.inl ⟨hexact, Or.inr hheavy⟩
  · exact Or.inr (Or.inl hvgrow)
  · exact Or.inr (Or.inr hugrow)

end CriticalTriangleOrGrowth

end MinModulus
