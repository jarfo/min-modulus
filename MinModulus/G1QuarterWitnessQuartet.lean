/-
# The quarter-witness quartet behind an all-zero triangle

The six-coordinate balanced center does more upstairs than produce a
relation after reduction.  At the original modulus it is a light witness at
a quarter target `t`.  Subtracting its affine value from each of the three
pure edge values gives three further light witnesses at the same target.
Their omission sets are the center triangle, while the balanced witness
omits the original vertex triple.
-/
import MinModulus.G1QuarterCenterTransport

namespace MinModulus

open Finset

/-- Two positive and two negative coordinates with zero total coefficient. -/
def balancedPairCoeffs {n : ℕ} (p q a b : Fin n) : Fin n → ℤ := fun i =>
  (if i = p then 1 else 0) + (if i = q then 1 else 0) -
    (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- The pure half-witness on an edge: coefficient `2` at its center and
coefficient `-1` at the two edge vertices. -/
def pureEdgeCoeffs {n : ℕ} (x a b : Fin n) : Fin n → ℤ := fun i =>
  (if i = x then 2 else 0) - (if i = a then 1 else 0) -
    (if i = b then 1 else 0)

/-- Each pure edge is exactly the sum of the balanced six-point quarter
witness and the quarter witness on the opposite center edge. -/
theorem balancedSix_add_quarterPairs_eq_pureEdges
    {n : ℕ} (x y z a b d : Fin n) :
    balancedSixCoeffs x y z a b d + balancedPairCoeffs x d y z =
        pureEdgeCoeffs x a b ∧
      balancedSixCoeffs x y z a b d + balancedPairCoeffs y a z x =
        pureEdgeCoeffs y b d ∧
      balancedSixCoeffs x y z a b d + balancedPairCoeffs z b x y =
        pureEdgeCoeffs z d a := by
  constructor
  · funext i
    simp only [balancedSixCoeffs, balancedPairCoeffs, pureEdgeCoeffs,
      Pi.add_apply]
    ring_nf
    split_ifs <;> omega
  constructor
  · funext i
    simp only [balancedSixCoeffs, balancedPairCoeffs, pureEdgeCoeffs,
      Pi.add_apply]
    ring_nf
    split_ifs <;> omega
  · funext i
    simp only [balancedSixCoeffs, balancedPairCoeffs, pureEdgeCoeffs,
      Pi.add_apply]
    ring_nf
    split_ifs <;> omega

/-- A balanced four-coordinate value identity is an admissible light
witness. -/
theorem balancedPairCoeffs_witness
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) {h : G} (p q a b : Fin n)
    (hpq : p ≠ q) (hab : a ≠ b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hval : g p + g q - g a - g b = h) :
    Witness g h (balancedPairCoeffs p q a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hpzero := congrFun hzero p
    simp [balancedPairCoeffs, hpq, hpa, hpb] at hpzero
  · intro i
    by_cases hia : i = a
    · subst i
      simp [balancedPairCoeffs, Ne.symm hpa, Ne.symm hqa, hab]
    by_cases hib : i = b
    · subst i
      simp [balancedPairCoeffs, Ne.symm hpb, Ne.symm hqb, hab.symm]
    simp [balancedPairCoeffs, hia, hib]
    omega
  · simp [balancedPairCoeffs, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  · simpa [balancedPairCoeffs, add_smul, sub_smul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] using hval

/-- The two negative coordinates are exactly the omissions of a balanced
pair vector. -/
theorem balancedPairCoeffs_exactOmissions
    {n : ℕ} (p q a b : Fin n)
    (hab : a ≠ b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ExactOmissions (balancedPairCoeffs p q a b) {a, b} := by
  intro i
  by_cases hia : i = a
  · subst i
    simp [balancedPairCoeffs, Ne.symm hpa, Ne.symm hqa, hab]
  by_cases hib : i = b
  · subst i
    simp [balancedPairCoeffs, Ne.symm hpb, Ne.symm hqb, hab.symm]
  simp [balancedPairCoeffs, hia, hib]
  omega

/-- An exact-pair witness with total positive mass concentrated as `2` at
one external coordinate is exactly the corresponding pure-edge vector. -/
theorem exactPair_coeff_two_eq_pureEdgeCoeffs
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) {h : G} {c : Fin n → ℤ}
    (hc : Witness g h c) (a b x : Fin n) (hab : a ≠ b)
    (homit : ∀ i, c i = -1 ↔ i = a ∨ i = b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hcx : c x = 2) :
    c = pureEdgeCoeffs x a b := by
  funext i
  by_cases hia : i = a
  · subst i
    have hca : c a = -1 := (homit a).2 (Or.inl rfl)
    simp [pureEdgeCoeffs, hca, Ne.symm hxa, hab]
  by_cases hib : i = b
  · subst i
    have hcb : c b = -1 := (homit b).2 (Or.inr rfl)
    simp [pureEdgeCoeffs, hcb, Ne.symm hxb, hab.symm]
  by_cases hix : i = x
  · subst i
    simp [pureEdgeCoeffs, hcx, hxa, hxb]
  have hci := witness_other_eq_zero_of_exact_pair_and_coeff_eq_two
    g hc a b x hab homit hxa hxb hcx i hia hib hix
  simp [pureEdgeCoeffs, hci, hia, hib, hix]

/-- The three vertex coordinates are exactly the omissions of the balanced
six-coordinate vector. -/
theorem balancedSixCoeffs_exactOmissions
    {n : ℕ} (x y z a b d : Fin n)
    (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ d)
    (hy : y ≠ b ∧ y ≠ d ∧ y ≠ a)
    (hz : z ≠ d ∧ z ≠ a ∧ z ≠ b) :
    ExactOmissions (balancedSixCoeffs x y z a b d) {a, b, d} := by
  intro i
  by_cases hia : i = a
  · subst i
    simp [balancedSixCoeffs, Ne.symm hx.1, Ne.symm hy.2.2,
      Ne.symm hz.2.1, hab, Ne.symm hda]
  by_cases hib : i = b
  · subst i
    simp [balancedSixCoeffs, Ne.symm hx.2.1, Ne.symm hy.1,
      Ne.symm hz.2.2, hab.symm, hbd]
  by_cases hid : i = d
  · subst i
    simp [balancedSixCoeffs, Ne.symm hx.2.2, Ne.symm hy.2.1,
      Ne.symm hz.1, hda, hbd.symm]
  simp [balancedSixCoeffs, hia, hib, hid]
  omega

/-- An all-zero exact omission triangle canonically expands to four light
witnesses at one quarter target.  One omits the original vertex triple; the
other three omit the three edges of the pure-center triangle. -/
theorem exists_light_quarterWitness_quartet_of_triangle_all_zero
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 0) (hDAb : cDA b = 0) :
    ∃ x y z : Fin n, ∃ t : G,
      (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
      (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
      (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      cAB x = 2 ∧ cBD y = 2 ∧ cDA z = 2 ∧
      t + t = h ∧
      Witness g t (balancedSixCoeffs x y z a b d) ∧
      ExactOmissions (balancedSixCoeffs x y z a b d) {a, b, d} ∧
      Witness g t (balancedPairCoeffs x d y z) ∧
      ExactOmissions (balancedPairCoeffs x d y z) {y, z} ∧
      Witness g t (balancedPairCoeffs y a z x) ∧
      ExactOmissions (balancedPairCoeffs y a z x) {z, x} ∧
      Witness g t (balancedPairCoeffs z b x y) ∧
      ExactOmissions (balancedPairCoeffs z b x y) {x, y} ∧
      balancedSixCoeffs x y z a b d + balancedPairCoeffs x d y z = cAB ∧
      balancedSixCoeffs x y z a b d + balancedPairCoeffs y a z x = cBD ∧
      balancedSixCoeffs x y z a b d + balancedPairCoeffs z b x y = cDA := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz⟩ :=
    exists_six_distinct_pure_centers_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  let t : G := g x + g y + g z - g a - g b - g d
  have ht : t + t = h :=
    double_balanced_center_sum_eq_target_of_pure_triangle
      g hh hcAB hcBD hcDA a b d x y z hab hbd hda hAB hBD hDA
        hx.1 hx.2.1 hy.1 hy.2.1 hz.1 hz.2.1 hABx hBDy hDAz
  have hABval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcAB a b x hab hAB hx.1 hx.2.1 hABx
  have hBDval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcBD b d y hbd hBD hy.1 hy.2.1 hBDy
  have hDAval := two_smul_eq_target_add_pair_of_exact_pair_coeff_two
    g hcDA d a z hda hDA hz.1 hz.2.1 hDAz
  have hABquarter : g x + g d - g y - g z = t := by
    calc
      g x + g d - g y - g z =
          ((2 : ℤ) • g x - g a - g b) - t := by
            simp only [t, two_zsmul]
            abel
      _ = h - t := by rw [hABval]; abel
      _ = t := by rw [← ht]; abel
  have hBDquarter : g y + g a - g z - g x = t := by
    calc
      g y + g a - g z - g x =
          ((2 : ℤ) • g y - g b - g d) - t := by
            simp only [t, two_zsmul]
            abel
      _ = h - t := by rw [hBDval]; abel
      _ = t := by rw [← ht]; abel
  have hDAquarter : g z + g b - g x - g y = t := by
    calc
      g z + g b - g x - g y =
          ((2 : ℤ) • g z - g d - g a) - t := by
            simp only [t, two_zsmul]
            abel
      _ = h - t := by rw [hDAval]; abel
      _ = t := by rw [← ht]; abel
  have hSix := balancedSixCoeffs_witness g x y z a b d hab hbd hda
    hx hy hz hxy hyz hzx rfl
  have hABq := balancedPairCoeffs_witness g x d y z hx.2.2 hyz
    hxy (Ne.symm hzx) (Ne.symm hy.2.1) (Ne.symm hz.1) hABquarter
  have hBDq := balancedPairCoeffs_witness g y a z x
    hy.2.2 hzx
    hyz (Ne.symm hxy) (Ne.symm hz.2.1) (Ne.symm hx.1) hBDquarter
  have hDAq := balancedPairCoeffs_witness g z b x y
    hz.2.2 hxy
    hzx (Ne.symm hyz) (Ne.symm hx.2.1) (Ne.symm hy.1) hDAquarter
  have hpure := balancedSix_add_quarterPairs_eq_pureEdges x y z a b d
  have hABpure := exactPair_coeff_two_eq_pureEdgeCoeffs
    g hcAB a b x hab hAB hx.1 hx.2.1 hABx
  have hBDpure := exactPair_coeff_two_eq_pureEdgeCoeffs
    g hcBD b d y hbd hBD hy.1 hy.2.1 hBDy
  have hDApure := exactPair_coeff_two_eq_pureEdgeCoeffs
    g hcDA d a z hda hDA hz.1 hz.2.1 hDAz
  exact ⟨x, y, z, t, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz,
    ht, hSix,
    balancedSixCoeffs_exactOmissions x y z a b d hab hbd hda hx hy hz,
    hABq,
    balancedPairCoeffs_exactOmissions x d y z hyz hxy (Ne.symm hzx)
      (Ne.symm hy.2.1) (Ne.symm hz.1),
    hBDq,
    balancedPairCoeffs_exactOmissions y a z x hzx hyz (Ne.symm hxy)
      (Ne.symm hz.2.1) (Ne.symm hx.1),
    hDAq,
    balancedPairCoeffs_exactOmissions z b x y hxy hzx (Ne.symm hyz)
      (Ne.symm hx.2.1) (Ne.symm hy.1),
    hpure.1.trans hABpure.symm,
    hpure.2.1.trans hBDpure.symm,
    hpure.2.2.trans hDApure.symm⟩

/-- Canonical exact-fan specialization: the all-zero two-singleton branch
contains the full quarter-target quartet upstairs. -/
theorem canonical_exactTriangle_two_zero_quarterWitness_quartet_zmod
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
    (huzero : subsetCollisionCoeffs u.val.1 u.val.2 k.succ = 0) :
    ∃ x y v : Fin (m + 1), ∃ t : ZMod N,
      (x ≠ j.succ ∧ x ≠ k.succ ∧ x ≠ z.succ) ∧
      (y ≠ k.succ ∧ y ≠ z.succ ∧ y ≠ j.succ) ∧
      (v ≠ z.succ ∧ v ≠ j.succ ∧ v ≠ k.succ) ∧
      x ≠ y ∧ y ≠ v ∧ v ≠ x ∧
      subsetCollisionCoeffs r.val.1 r.val.2 x = 2 ∧
      subsetCollisionCoeffs q.val.1 q.val.2 y = 2 ∧
      subsetCollisionCoeffs u.val.1 u.val.2 v = 2 ∧
      t + t = (M : ZMod N) ∧
      Witness g t
        (balancedSixCoeffs x y v j.succ k.succ z.succ) ∧
      ExactOmissions
        (balancedSixCoeffs x y v j.succ k.succ z.succ)
        {j.succ, k.succ, z.succ} ∧
      Witness g t (balancedPairCoeffs x z.succ y v) ∧
      ExactOmissions (balancedPairCoeffs x z.succ y v) {y, v} ∧
      Witness g t (balancedPairCoeffs y j.succ v x) ∧
      ExactOmissions (balancedPairCoeffs y j.succ v x) {v, x} ∧
      Witness g t (balancedPairCoeffs v k.succ x y) ∧
      ExactOmissions (balancedPairCoeffs v k.succ x y) {x, y} ∧
      balancedSixCoeffs x y v j.succ k.succ z.succ +
          balancedPairCoeffs x z.succ y v =
        subsetCollisionCoeffs r.val.1 r.val.2 ∧
      balancedSixCoeffs x y v j.succ k.succ z.succ +
          balancedPairCoeffs y j.succ v x =
        subsetCollisionCoeffs q.val.1 q.val.2 ∧
      balancedSixCoeffs x y v j.succ k.succ z.succ +
          balancedPairCoeffs v k.succ x y =
        subsetCollisionCoeffs u.val.1 u.val.2 := by
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
  simpa [cr, cq, cu] using
    exists_light_quarterWitness_quartet_of_triangle_all_zero
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

end MinModulus
