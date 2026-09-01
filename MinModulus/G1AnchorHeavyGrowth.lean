/-
# Converting anchor-heavy escape into canonical tail growth

In the genuine residual, a surviving heavy half-witness can only be heavy at
the anchor; all successor coefficients remain light.  Its positive/negative
tail reconstruction is therefore cardinality oriented, with anchor value
equal to the cardinality imbalance.  Three distinct omissions force a
canonical reduced collision with imbalance at least two and negative tail at
least three.  This unifies the heavy and explicit tail-growth exits.
-/
import MinModulus.G1TwoSingletonAllZero

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An anchor-heavy, tail-light witness with three distinct omissions
reconstructs as a strictly unbalanced canonical collision.  Its imbalance is
the anchor coefficient, and its negative tail contains all three omissions. -/
theorem exists_canonicalReducedCollision_of_anchorHeavy_three_omissions
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1)
    (a b d : Fin (m + 1))
    (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hca : c a = -1) (hcb : c b = -1) (hcd : c d = -1)
    (hc0 : 2 ≤ c 0) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
      subsetCollisionCoeffs r.val.1 r.val.2 = c ∧
      2 ≤ reducedCollisionImbalance r ∧ 3 ≤ r.val.2.card := by
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    omega
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    omega
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    omega
  obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha0
  obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb0
  obtain ⟨d', rfl⟩ := Fin.eq_succ_of_ne_zero hd0
  obtain ⟨r, hcard, hcoeff⟩ :=
    exists_reducedCollision_coeff_eq_of_tail_light_of_anchor_nonneg
      g hc hceil (by omega)
  have hanchor := congrFun hcoeff 0
  change ((r.val.2.card : ℤ) - (r.val.1.card : ℤ)) = c 0 at hanchor
  have hlt : r.val.1.card < r.val.2.card := by
    omega
  have hcanon : r ∈ canonicalReducedCollisions (g := g) hh := by
    rw [mem_canonicalReducedCollisions_iff]
    exact Or.inl hlt
  have himbalance : 2 ≤ reducedCollisionImbalance r := by
    rw [reducedCollisionImbalance]
    omega
  have haB : a' ∈ r.val.2 := by
    have haCoeff : subsetCollisionCoeffs r.val.1 r.val.2 a'.succ = -1 := by
      rw [hcoeff]
      exact hca
    exact (Finset.mem_sdiff.mp
      ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 a').mp haCoeff)).1
  have hbB : b' ∈ r.val.2 := by
    have hbCoeff : subsetCollisionCoeffs r.val.1 r.val.2 b'.succ = -1 := by
      rw [hcoeff]
      exact hcb
    exact (Finset.mem_sdiff.mp
      ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 b').mp hbCoeff)).1
  have hdB : d' ∈ r.val.2 := by
    have hdCoeff : subsetCollisionCoeffs r.val.1 r.val.2 d'.succ = -1 := by
      rw [hcoeff]
      exact hcd
    exact (Finset.mem_sdiff.mp
      ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 d').mp hdCoeff)).1
  have hab' : a' ≠ b' := by
    intro hab'
    subst b'
    exact hab rfl
  have hbd' : b' ≠ d' := by
    intro hbd'
    subst d'
    exact hbd rfl
  have hda' : d' ≠ a' := by
    intro hda'
    subst d'
    exact hda rfl
  have hthree : 3 ≤ r.val.2.card := by
    have hsubset : ({a', b', d'} : Finset (Fin m)) ⊆ r.val.2 := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact haB
      · exact hbB
      · exact hdB
    have hcardThree : ({a', b', d'} : Finset (Fin m)).card = 3 := by
      have haNot : a' ∉ ({b', d'} : Finset (Fin m)) := by
        simp [hab', Ne.symm hda']
      have hbNot : b' ∉ ({d'} : Finset (Fin m)) := by
        simp [hbd']
      rw [Finset.card_insert_of_notMem haNot,
        Finset.card_insert_of_notMem hbNot, Finset.card_singleton]
    rw [← hcardThree]
    exact Finset.card_le_card hsubset
  exact ⟨r, hcanon, hcoeff, himbalance, hthree⟩

/-- Both live exits of the genuine two-singleton residual yield a canonical
half-collision with negative tail at least three.  In the anchor-heavy branch
the new collision additionally has imbalance at least two. -/
theorem genuineDominant_two_tail_exists_canonical_tail_growth
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
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalReducedCollisions (g := g) hh ∧
      v ≠ r ∧ 3 ≤ v.val.2.card ∧
      (2 ≤ reducedCollisionImbalance v ∨
        v ∈ canonicalSupportEscapeTargets hh r) := by
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
  rcases genuineDominant_two_tail_anchorHeavy_or_growth
      hqodd g hg r hr hres hBcard with hheavy | hgrow
  · obtain ⟨c, a, b, d, hc, hab, hbd, hda, hca, hcb, hcd, hc0⟩ := hheavy
    have hceil : ∀ j : Fin n, c j.succ ≤ 1 := by
      intro j
      by_contra hj
      have hj2 : 2 ≤ c j.succ := by omega
      exact hres.2.2 ⟨c, hc, j, hj2⟩
    obtain ⟨v, hv, _hcoeff, himbalance, hvB⟩ :=
      exists_canonicalReducedCollision_of_anchorHeavy_three_omissions
        g (half_add_half hN) hc hceil a b d hab hbd hda
          hca hcb hcd hc0
    have hvr : v ≠ r := by
      intro hvr
      subst v
      omega
    exact ⟨v, by simpa [hh] using hv, hvr, hvB, Or.inl himbalance⟩
  · obtain ⟨v, hv, hvB⟩ := hgrow
    have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      rcases mem_canonicalSupportEscapeTargets_iff.mp hv with ⟨x, hx⟩
      exact (mem_canonicalSupportEscapeIncidences_iff.mp hx).2.1
    have hvr : v ≠ r := by
      intro hvr
      subst v
      omega
    exact ⟨v, hvcanonical, hvr, hvB, Or.inr hv⟩

end MinModulus
