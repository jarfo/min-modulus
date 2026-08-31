/-
# Tail-light witnesses reduce to canonical collisions

A half-witness whose non-anchor coefficients all lie in `{-1,0,1}` is not a
new higher-mass object.  Its `+1` and `-1` tail sets reconstruct its full
coefficient vector, including the anchor through the zero-sum identity.  Up
to negation, it is therefore a cardinality-oriented reduced subset collision,
and at a nonzero involution it has a canonical swap representative.

Consequently every canonical attachment is either genuinely heavy on a tail
coordinate (some coefficient is at least two), or transitions to another
canonical reduced collision.  In the latter case the new shape avoids the
coordinate where the attachment vanishes, while its side incidence at the
shared omitted coordinate is explicit.
-/
import MinModulus.G1AttachmentDeficit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Tail coordinates where a witness has coefficient `+1`. -/
def witnessPositiveTail (c : Fin (m + 1) → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun j ↦ c j.succ = 1)

/-- Tail coordinates where a witness has coefficient `-1`. -/
def witnessNegativeTail (c : Fin (m + 1) → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun j ↦ c j.succ = -1)

theorem witnessTails_disjoint (c : Fin (m + 1) → ℤ) :
    Disjoint (witnessPositiveTail c) (witnessNegativeTail c) := by
  rw [Finset.disjoint_left]
  intro j hjp hjn
  simp [witnessPositiveTail] at hjp
  simp [witnessNegativeTail] at hjn
  omega

theorem subsetCollisionCoeffs_witnessTails_succ
    (c : Fin (m + 1) → ℤ)
    (hfloor : ∀ j : Fin m, -1 ≤ c j.succ)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1)
    (j : Fin m) :
    subsetCollisionCoeffs (witnessPositiveTail c) (witnessNegativeTail c)
      j.succ = c j.succ := by
  have htri : c j.succ = -1 ∨ c j.succ = 0 ∨ c j.succ = 1 := by
    have hlo := hfloor j
    have hhi := hceil j
    omega
  rcases htri with hj | hj | hj <;>
    simp [subsetCollisionCoeffs, witnessPositiveTail, witnessNegativeTail, hj]

/-- The tail sets and total coefficient sum reconstruct the entire vector. -/
theorem subsetCollisionCoeffs_witnessTails
    (c : Fin (m + 1) → ℤ) (hsum : (∑ i, c i) = 0)
    (hfloor : ∀ j : Fin m, -1 ≤ c j.succ)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    subsetCollisionCoeffs (witnessPositiveTail c) (witnessNegativeTail c) = c := by
  funext i
  refine Fin.cases ?_ ?_ i
  · have hd := subsetCollisionCoeffs_sum
      (witnessPositiveTail c) (witnessNegativeTail c)
    rw [Fin.sum_univ_succ] at hd hsum
    have htail :
        (∑ j : Fin m, subsetCollisionCoeffs
          (witnessPositiveTail c) (witnessNegativeTail c) j.succ) =
          ∑ j : Fin m, c j.succ := by
      apply Finset.sum_congr rfl
      intro j _
      exact subsetCollisionCoeffs_witnessTails_succ c hfloor hceil j
    omega
  · intro j
    exact subsetCollisionCoeffs_witnessTails_succ c hfloor hceil j

omit [DecidableEq G] in
theorem witnessTails_value
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    ssum g (witnessPositiveTail c) =
      ssum g (witnessNegativeTail c) + h := by
  have heq := subsetCollisionCoeffs_witnessTails c hc.2.2.1
    (fun j ↦ hc.2.1 j.succ) hceil
  have hval := subsetCollisionCoeffs_weighted_sum g
    (witnessPositiveTail c) (witnessNegativeTail c)
  rw [heq, hc.2.2.2] at hval
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hval.symm)

theorem witnessTails_card_le_of_anchor_nonneg
    {c : Fin (m + 1) → ℤ} (hsum : (∑ i, c i) = 0)
    (hfloor : ∀ j : Fin m, -1 ≤ c j.succ)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1)
    (hanchor : 0 ≤ c 0) :
    (witnessPositiveTail c).card ≤ (witnessNegativeTail c).card := by
  have heq0 := congrFun
    (subsetCollisionCoeffs_witnessTails c hsum hfloor hceil) 0
  simp only [subsetCollisionCoeffs, Fin.cons_zero] at heq0
  have hint : ((witnessPositiveTail c).card : ℤ) ≤
      ((witnessNegativeTail c).card : ℤ) := by omega
  exact_mod_cast hint

omit [DecidableEq G] in
/-- A tail-light witness with nonnegative anchor is exactly the coefficient
vector of a cardinality-oriented reduced subset collision. -/
theorem exists_reducedCollision_coeff_eq_of_tail_light_of_anchor_nonneg
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (hceil : ∀ j : Fin m, c j.succ ≤ 1)
    (hanchor : 0 ≤ c 0) :
    ∃ r : ReducedSubsetSumCollision g h,
      r.val.1.card ≤ r.val.2.card ∧
        subsetCollisionCoeffs r.val.1 r.val.2 = c := by
  let A := witnessPositiveTail c
  let B := witnessNegativeTail c
  have hfloor : ∀ j : Fin m, -1 ≤ c j.succ := fun j ↦ hc.2.1 j.succ
  have hcard := witnessTails_card_le_of_anchor_nonneg
    hc.2.2.1 hfloor hceil hanchor
  have hcoeff := subsetCollisionCoeffs_witnessTails c hc.2.2.1 hfloor hceil
  refine ⟨⟨(A, B), witnessTails_disjoint c, ?_⟩, hcard, hcoeff⟩
  exact witnessTails_value g hc hceil

omit [DecidableEq G] in
/-- Every tail-light half-witness is, up to sign, the explicit coefficient
vector of a cardinality-oriented reduced collision. -/
theorem exists_reducedCollision_coeff_eq_or_neg_of_tail_light
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    ∃ r : ReducedSubsetSumCollision g h,
      r.val.1.card ≤ r.val.2.card ∧
        (subsetCollisionCoeffs r.val.1 r.val.2 = c ∨
          subsetCollisionCoeffs r.val.1 r.val.2 = -c) := by
  by_cases hanchor : 0 ≤ c 0
  · rcases exists_reducedCollision_coeff_eq_of_tail_light_of_anchor_nonneg
      g hc hceil hanchor with ⟨r, hcard, hcoeff⟩
    exact ⟨r, hcard, Or.inl hcoeff⟩
  · have hc0 : c 0 = -1 := by
      have hfloor := hc.2.1 0
      omega
    have hfullceil : ∀ i, c i ≤ 1 := by
      intro i
      refine Fin.cases ?_ hceil i
      omega
    have hcneg := witness_neg_of_le_one g hh hc hfullceil
    have hnegceil : ∀ j : Fin m, (-c) j.succ ≤ 1 := by
      intro j
      simp only [Pi.neg_apply]
      have hfloor := hc.2.1 j.succ
      omega
    have hneganchor : 0 ≤ (-c) 0 := by
      simp only [Pi.neg_apply, hc0]
      omega
    rcases exists_reducedCollision_coeff_eq_of_tail_light_of_anchor_nonneg
      g hcneg hnegceil hneganchor with ⟨r, hcard, hcoeff⟩
    exact ⟨r, hcard, Or.inr hcoeff⟩

theorem subsetCollisionCoeffs_swap (A B : Finset (Fin m)) :
    subsetCollisionCoeffs B A = -subsetCollisionCoeffs A B := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [subsetCollisionCoeffs]
  · intro j
    by_cases hA : j ∈ A <;> by_cases hB : j ∈ B <;>
      simp [subsetCollisionCoeffs, hA, hB]

/-- At a nonzero involution, the collision representing a tail-light witness
can itself be chosen from the canonical swap representatives. -/
theorem exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    ∃ r : ReducedSubsetSumCollision g h,
      IsCanonicalReducedCollision hh r ∧
        (subsetCollisionCoeffs r.val.1 r.val.2 = c ∨
          subsetCollisionCoeffs r.val.1 r.val.2 = -c) := by
  rcases exists_reducedCollision_coeff_eq_or_neg_of_tail_light
      g hh hc hceil with ⟨r, _, hcoeff⟩
  by_cases hcanon : IsCanonicalReducedCollision hh r
  · exact ⟨r, hcanon, hcoeff⟩
  · let r' := reducedSubsetSumCollisionSwapEquiv hh r
    have hcanon' : IsCanonicalReducedCollision hh r' :=
      (canonicalReducedCollision_swap_iff_not hh hh0 r).mpr hcanon
    refine ⟨r', hcanon', ?_⟩
    change subsetCollisionCoeffs r.val.2 r.val.1 = c ∨
      subsetCollisionCoeffs r.val.2 r.val.1 = -c
    rw [subsetCollisionCoeffs_swap]
    rcases hcoeff with hcoeff | hcoeff
    · exact Or.inr (congrArg Neg.neg hcoeff)
    · left
      rw [hcoeff]
      simp

omit [DecidableEq G] in
/-- Geometry of the canonical light transition at the zero and omitted tail
coordinates of the attached witness. -/
theorem canonicalReducedCollision_geometry_of_coeff_eq_or_neg
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) {c : Fin (m + 1) → ℤ}
    {j b : Fin m} (hcj : c j.succ = 0) (hcb : c b.succ = -1)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 = c ∨
      subsetCollisionCoeffs q.val.1 q.val.2 = -c) :
    j ∉ q.val.1 ∪ q.val.2 ∧
      ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧ b ∈ q.val.2) ∨
        (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧ b ∈ q.val.1)) := by
  have hjzero : subsetCollisionCoeffs q.val.1 q.val.2 j.succ = 0 := by
    rcases hcoeff with hcoeff | hcoeff
    · rw [hcoeff, hcj]
    · rw [hcoeff]
      simp [hcj]
  have hjnot : j ∉ q.val.1 ∪ q.val.2 := by
    intro hj
    have hdisj := Finset.disjoint_left.mp q.property.1
    rcases Finset.mem_union.mp hj with hjA | hjB
    · have hjBn : j ∉ q.val.2 := fun hjB ↦ hdisj hjA hjB
      simp [subsetCollisionCoeffs, hjA, hjBn] at hjzero
    · by_cases hjA : j ∈ q.val.1
      · exact hdisj hjA hjB
      · simp [subsetCollisionCoeffs, hjA, hjB] at hjzero
  refine ⟨hjnot, ?_⟩
  rcases hcoeff with hcoeff | hcoeff
  · left
    refine ⟨hcoeff, ?_⟩
    have hbneg : subsetCollisionCoeffs q.val.1 q.val.2 b.succ = -1 := by
      rw [hcoeff, hcb]
    exact (Finset.mem_sdiff.mp
      ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        q.val.1 q.val.2 b).mp hbneg)).1
  · right
    refine ⟨hcoeff, ?_⟩
    have hbpos : subsetCollisionCoeffs q.val.1 q.val.2 b.succ = 1 := by
      rw [hcoeff]
      simp [hcb]
    by_contra hbA
    by_cases hbB : b ∈ q.val.2
    · simp [subsetCollisionCoeffs, hbA, hbB] at hbpos
    · simp [subsetCollisionCoeffs, hbA, hbB] at hbpos

/-- Every canonical attachment is either genuinely heavy on a tail
coordinate, or is (up to sign) another canonical reduced collision.  In the
light case that new shape avoids the attached coordinate `j`, while the
shared omitted coordinate `b` lies on the side determined by the sign. -/
theorem commonTouched_or_canonicalReducedCollisions_heavy_or_light_transition
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
                ((∃ k : Fin m, 2 ≤ c k.succ) ∨
                  ∃ q : ReducedSubsetSumCollision g h,
                    q ∈ canonicalReducedCollisions (g := g) hh ∧
                      j ∉ q.val.1 ∪ q.val.2 ∧
                      ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧
                          b ∈ q.val.2) ∨
                        (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                          b ∈ q.val.1))) := by
  rcases commonTouched_or_canonicalReducedCollisions_internal_attachments
      g hg hh hh0 with htouch | hattach
  · exact Or.inl htouch
  · right
    intro r hr j hj
    rcases hattach r hr j hj with ⟨b, hb, hbj, c, hc, hcj, hcb⟩
    refine ⟨b, hb, hbj, c, hc, hcj, hcb, ?_⟩
    by_cases hheavy : ∃ k : Fin m, 2 ≤ c k.succ
    · exact Or.inl hheavy
    · right
      have hceil : ∀ k : Fin m, c k.succ ≤ 1 := by
        intro k
        by_contra hk
        exact hheavy ⟨k, by omega⟩
      rcases exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
          g hh hh0 hc hceil with ⟨q, hq, hcoeff⟩
      have hgeom := canonicalReducedCollision_geometry_of_coeff_eq_or_neg
        q hcj hcb hcoeff
      exact ⟨q, mem_canonicalReducedCollisions_iff.mpr hq,
        hgeom.1, hgeom.2⟩

end MinModulus
