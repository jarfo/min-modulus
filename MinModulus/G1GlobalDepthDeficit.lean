/-
# Global depth-deficit budget

The summed escape-depth tax says that source-tail coverage and support growth
must fit inside the external-support complement of the dominant root.  After
the global depth normalization, the unused ambient depth of a non-root target
is exactly the exponent of its padding weight.  The elementary inequality
`e + 1 <= 2^e` therefore converts the unweighted external-support tax into a
weighted lower bound for the whole non-root star:

`|B_r| + (# non-root canonical collisions) <= sum_{v != r} w_v`.

Quarter-star concentration then pays four times both terms from the root
weight.  Since the surviving root has at least three negative coordinates and
there are at least two non-root targets, its padding exponent is at least five;
equivalently its support leaves at least five ambient coordinates and its
weight is divisible by 32.
-/
import MinModulus.G1TwoTwoRootClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- One plus an exponent is bounded by the corresponding power of two. -/
theorem add_one_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      rw [pow_succ]
      omega

omit [DecidableEq G] in
/-- For a support-growing collision, ambient root depth plus one is paid by
its exact support depth together with its padding weight. -/
theorem ambientDepth_add_one_le_supportDepth_add_weight
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card) :
    m - (reducedCollisionSupport r).card + 1 ≤
      reducedCollisionSupportDepth r v +
        reducedCollisionWeight (m := m) v := by
  have hvle : (reducedCollisionSupport v).card ≤ m := by
    have := Finset.card_le_univ (reducedCollisionSupport v)
    simpa using this
  have hremainder :
      m - (reducedCollisionSupport v).card =
        (m - (reducedCollisionSupport r).card) -
          reducedCollisionSupportDepth r v := by
    simp only [reducedCollisionSupportDepth]
    omega
  have hdepthle : reducedCollisionSupportDepth r v ≤
      m - (reducedCollisionSupport r).card := by
    simp only [reducedCollisionSupportDepth]
    omega
  have hpow := add_one_le_two_pow
    ((m - (reducedCollisionSupport r).card) -
      reducedCollisionSupportDepth r v)
  change m - (reducedCollisionSupport r).card + 1 ≤
    reducedCollisionSupportDepth r v +
      2 ^ (m - (reducedCollisionSupport v).card)
  rw [hremainder]
  omega

section CriticalGlobalDepthDeficit

/-- The non-root canonical family has at least two members in every genuine
residual. -/
theorem genuineDominant_two_le_nonrootCard
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    2 ≤ canonicalCrossStarCard hh r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  change 2 ≤ ((canonicalReducedCollisions (g := g) hh).erase r).card
  obtain ⟨v, hv, hvr, _⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r r hr hres
  obtain ⟨u, hu, hur, huv⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r v hr hres
  have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hu' : u ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hu
  exact Finset.one_lt_card.mpr ⟨v, Finset.mem_erase.mpr ⟨hvr, hv'⟩,
    u, Finset.mem_erase.mpr ⟨hur, hu'⟩, Ne.symm huv⟩

omit [DecidableEq G] in
/-- External support has at most the ambient padding depth of the root. -/
theorem externalSupport_card_le_ambientDepth
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h) :
    (reducedCollisionExternalSupport r v).card ≤
      m - (reducedCollisionSupport r).card := by
  have hsubset : reducedCollisionExternalSupport r v ⊆
      Finset.univ \ reducedCollisionSupport r := by
    intro j hj
    have hj' := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj'.2⟩
  have hcard := Finset.card_le_card hsubset
  calc
    (reducedCollisionExternalSupport r v).card ≤
        (Finset.univ \ reducedCollisionSupport r).card := hcard
    _ = m - (reducedCollisionSupport r).card := by
      rw [Finset.card_sdiff]
      simp

/-- The summed escape-depth tax fits in the ambient complement of the
non-root family. -/
theorem genuineDominant_negativeTail_add_sumDepth_le_ambientDepth_mul_nonrootCard
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    r.val.2.card + (canonicalOtherReducedCollisions hh r).sum
        (reducedCollisionSupportDepth r) ≤
      (n - (reducedCollisionSupport r).card) *
        canonicalCrossStarCard hh r := by
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
  let C := canonicalReducedCollisions (g := g) hh
  let E := canonicalOtherReducedCollisions hh r
  let depth := reducedCollisionSupportDepth r
  let external : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) → ℕ :=
    fun v ↦ (reducedCollisionExternalSupport r v).card
  let d := n - (reducedCollisionSupport r).card
  change r.val.2.card + E.sum (reducedCollisionSupportDepth r) ≤
    (n - (reducedCollisionSupport r).card) * E.card
  have hr' : r ∈ C := by
    simpa [C, hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ v ∈ C, (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by
    simpa [C, hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hrminRaw : ∀ v ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
    simpa [criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hmajor : C.sum (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [C, hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hcover : r.val.2.card ≤
      (canonicalSupportEscapeIncidences hh r).card := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg hh (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrminRaw) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [CriticalHeavyHalfWitness] using hheavy))
    · exact hcover.2
  have htax :=
    card_add_sum_supportDepth_le_sum_externalSupport_of_strictMajority
      hh r hr' hmajor hcover
  have hdepthSum : C.sum depth = E.sum depth := by
    have herase := Finset.sum_erase_add C depth hr'
    simpa [E, C, canonicalOtherReducedCollisions, depth,
      reducedCollisionSupportDepth] using herase.symm
  have hexternalSum : C.sum external = E.sum external := by
    have herase := Finset.sum_erase_add C external hr'
    simpa [E, C, canonicalOtherReducedCollisions, external,
      reducedCollisionExternalSupport] using herase.symm
  have hexternalUpper : E.sum external ≤ d * E.card := by
    calc
      E.sum external ≤ E.sum (fun _ ↦ d) := by
        apply Finset.sum_le_sum
        intro v hv
        exact externalSupport_card_le_ambientDepth r v
      _ = d * E.card := by simp [Nat.mul_comm]
  change r.val.2.card + C.sum depth ≤ C.sum external at htax
  change r.val.2.card + E.sum depth ≤ d * E.card
  rw [hdepthSum, hexternalSum] at htax
  exact htax.trans hexternalUpper

/-- The negative source tail and one unit for every non-root collision are
paid by the non-root padding-weight star. -/
theorem genuineDominant_negativeTail_add_nonrootCard_le_crossStarWeight
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    r.val.2.card + canonicalCrossStarCard hh r ≤
      canonicalCrossStarWeight hh r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let C := canonicalReducedCollisions (g := g) hh
  let E := canonicalOtherReducedCollisions hh r
  let depth := reducedCollisionSupportDepth r
  let weight : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) → ℕ :=
    reducedCollisionWeight (m := n)
  let d := n - (reducedCollisionSupport r).card
  change r.val.2.card + E.card ≤ canonicalCrossStarWeight hh r
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ v ∈ C, (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by
    simpa [C, hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hbudget :=
    genuineDominant_negativeTail_add_sumDepth_le_ambientDepth_mul_nonrootCard
      hqodd g hg r hr hres
  change r.val.2.card + E.sum depth ≤ d * E.card at hbudget
  have hpoint : ∀ v ∈ E, d + 1 ≤ depth v + weight v := by
    intro v hv
    have hvC : v ∈ C := by
      apply Finset.mem_of_mem_erase
      simpa [E, C, canonicalOtherReducedCollisions] using hv
    exact ambientDepth_add_one_le_supportDepth_add_weight
      r v (hrmin v hvC)
  have hpointSum : d * E.card + E.card ≤
      E.sum depth + E.sum weight := by
    calc
      d * E.card + E.card = E.sum (fun _ ↦ d + 1) := by
        simp [Nat.mul_comm, Nat.mul_add]
      _ ≤ E.sum (fun v ↦ depth v + weight v) :=
        Finset.sum_le_sum hpoint
      _ = E.sum depth + E.sum weight := Finset.sum_add_distrib
  have hweightSum : E.sum weight = canonicalCrossStarWeight hh r := by
    simp [E, weight, canonicalOtherReducedCollisions,
      canonicalCrossStarWeight]
  rw [← hweightSum]
  omega

/-- Quarter concentration converts the depth-deficit lower bound into a root
weight budget. -/
theorem genuineDominant_four_mul_negativeTail_add_nonrootCard_le_rootWeight
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    4 * (r.val.2.card + canonicalCrossStarCard hh r) ≤
      reducedCollisionWeight (m := n) r := by
  have hlower := genuineDominant_negativeTail_add_nonrootCard_le_crossStarWeight
    hqodd g hg r hr hres
  have hupper := genuineDominant_four_mul_crossStarWeight_le_rootWeight_global
    hn hqodd g hg r hr hres
  omega

/-- The root leaves at least five ambient padding coordinates in every
genuine residual. -/
theorem genuineDominant_rootSupport_add_five_le
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    (reducedCollisionSupport r).card + 5 ≤ n := by
  classical
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hB := genuineDominant_three_le_negativeTailCard
    hn hqodd g hg r hr hres
  have hcard := genuineDominant_two_le_nonrootCard
    hqodd g hg r hr hres
  change 2 ≤ ((canonicalReducedCollisions (g := g) hh).erase r).card at hcard
  have hbudget :=
    genuineDominant_four_mul_negativeTail_add_nonrootCard_le_rootWeight
      hn hqodd g hg r hr hres
  change 4 * (r.val.2.card +
      ((canonicalReducedCollisions (g := g) hh).erase r).card) ≤
    reducedCollisionWeight (m := n) r at hbudget
  have hweight : reducedCollisionWeight (m := n) r =
      2 ^ (n - (reducedCollisionSupport r).card) := by rfl
  have htwenty : 20 ≤ reducedCollisionWeight (m := n) r := by omega
  have hdepth : 5 ≤ n - (reducedCollisionSupport r).card := by
    by_contra hnot
    have hle : n - (reducedCollisionSupport r).card ≤ 4 := by omega
    have hpowle : 2 ^ (n - (reducedCollisionSupport r).card) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) hle
    rw [hweight] at htwenty
    norm_num at hpowle
    omega
  have hrle : (reducedCollisionSupport r).card ≤ n := by
    have := Finset.card_le_univ (reducedCollisionSupport r)
    simpa using this
  omega

/-- Equivalently, every genuine root padding weight is divisible by 32. -/
theorem genuineDominant_thirtyTwo_dvd_rootWeight
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    32 ∣ reducedCollisionWeight (m := n) r := by
  have hsupport := genuineDominant_rootSupport_add_five_le
    hn hqodd g hg r hr hres
  change 32 ∣ 2 ^ (n - (reducedCollisionSupport r).card)
  have hdepth : 5 ≤ n - (reducedCollisionSupport r).card := by omega
  refine ⟨2 ^ ((n - (reducedCollisionSupport r).card) - 5), ?_⟩
  rw [show n - (reducedCollisionSupport r).card =
      5 + ((n - (reducedCollisionSupport r).card) - 5) by omega,
    pow_add]
  norm_num

/-- The depth-deficit constraints retained by the final genuine branch. -/
def IsCriticalGlobalDepthDeficit
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  (reducedCollisionSupport r).card + 5 ≤ n ∧
  32 ∣ reducedCollisionWeight (m := n) r ∧
  let hh := half_add_half
    (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
      rw [pow_succ]
      ring)
  2 ≤ canonicalCrossStarCard hh r ∧
  4 * (r.val.2.card + canonicalCrossStarCard hh r) ≤
    reducedCollisionWeight (m := n) r

/-- Every genuine residual satisfies the global depth-deficit package. -/
theorem genuineDominant_globalDepthDeficit
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    IsCriticalGlobalDepthDeficit g r := by
  exact ⟨
    genuineDominant_rootSupport_add_five_le
      hn hqodd g hg r hr hres,
    genuineDominant_thirtyTwo_dvd_rootWeight
      hn hqodd g hg r hr hres,
    genuineDominant_two_le_nonrootCard hqodd g hg r hr hres,
    genuineDominant_four_mul_negativeTail_add_nonrootCard_le_rootWeight
      hn hqodd g hg r hr hres⟩

/-- Global critical localization retaining the sole large-negative-tail
profile, one-eighth support-star concentration, and the depth-deficit root
budget. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_globalDepthDeficit
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
        3 ≤ r.val.2.card ∧
        IsCriticalGlobalSupportConcentrated g r ∧
        IsCriticalGlobalDepthDeficit g r := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_threeNegative_globalSupportConcentrated
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, hB, hconcentrated⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres, hB,
      hconcentrated,
      genuineDominant_globalDepthDeficit
        hn hqodd g hg r hr hres⟩))

end CriticalGlobalDepthDeficit

end MinModulus
