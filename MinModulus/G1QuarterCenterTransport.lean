/-
# Transporting the all-zero triangle center

An all-zero exact omission triangle produces a balanced six-coordinate
element `t` with `2t = N/2`.  Divisibility by four is only the numerical
shadow of this statement.  This file keeps the element itself and proves
that reduction modulo `N/2` sends it to the next half-modulus element.
-/
import MinModulus.G1TwoSingletonTriangle

namespace MinModulus

/-- The light coefficient vector carried by three positive centers and three
negative triangle vertices. -/
def balancedSixCoeffs {n : ℕ}
    (x y z a b d : Fin n) : Fin n → ℤ := fun i =>
  ((if i = x then 1 else 0) + (if i = y then 1 else 0) +
      (if i = z then 1 else 0)) -
    (if i = a then 1 else 0) - (if i = b then 1 else 0) -
      (if i = d then 1 else 0)

/-- Six distinct coordinates with three positive and three negative signs
turn their balanced value identity into an actual light `Witness`. -/
theorem balancedSixCoeffs_witness
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) {h : G} (x y z a b d : Fin n)
    (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ d)
    (hy : y ≠ b ∧ y ≠ d ∧ y ≠ a)
    (hz : z ≠ d ∧ z ≠ a ∧ z ≠ b)
    (hxy : x ≠ y) (_hyz : y ≠ z) (hzx : z ≠ x)
    (hval : g x + g y + g z - g a - g b - g d = h) :
    Witness g h (balancedSixCoeffs x y z a b d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have hxzero := congrFun hzero x
    simp [balancedSixCoeffs, hxy, Ne.symm hzx, hx.1, hx.2.1, hx.2.2]
      at hxzero
  · intro i
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
  · simp [balancedSixCoeffs, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  · simpa [balancedSixCoeffs, add_smul, sub_smul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] using hval

/-- Pairwise-distinct positive centers make the balanced six-coordinate
vector light: every coefficient is at most one. -/
theorem balancedSixCoeffs_le_one
    {n : ℕ} (x y z a b d : Fin n)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    ∀ i, balancedSixCoeffs x y z a b d i ≤ 1 := by
  intro i
  by_cases hix : i = x
  · subst i
    simp [balancedSixCoeffs, hxy, Ne.symm hzx]
    omega
  by_cases hiy : i = y
  · subst i
    simp [balancedSixCoeffs, hxy.symm, hyz]
    omega
  by_cases hiz : i = z
  · subst i
    simp [balancedSixCoeffs, hzx, hyz.symm]
    omega
  simp [balancedSixCoeffs, hix, hiy, hiz]
  omega

/-- If `N = 2M` and `M = 2K`, reduction from `ZMod N` to `ZMod M` sends
every solution of `t+t=M` to the distinguished half `K`.  In particular the
quarter center cannot disappear in the reduction kernel. -/
theorem quarterCenter_cast_eq_half
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (t : ZMod N) (ht : t + t = (M : ZMod N)) :
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M) t =
      (K : ZMod M) := by
  letI : NeZero M := ⟨by omega⟩
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  have hself : f t + f t = 0 := by
    rw [← map_add, ht]
    rw [map_natCast, ZMod.natCast_self]
  have hnonzero : f t ≠ 0 := by
    intro hzero
    have hmem : t ∈ AddSubgroup.zmultiples ((M : ℕ) : ZMod N) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      change ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩)
        (ZMod M) t = 0 at hzero
      rw [ZMod.castHom_apply, ← ZMod.natCast_val,
        ZMod.natCast_eq_zero_iff] at hzero
      obtain ⟨a, ha⟩ := hzero
      refine ⟨(a : ℤ), ?_⟩
      have hmul : (a : ZMod N) * ((M : ℕ) : ZMod N) =
          ((M * a : ℕ) : ZMod N) := by
        push_cast
        ring
      rw [natCast_zsmul, nsmul_eq_mul, hmul, ← ha,
        ZMod.natCast_zmod_val]
    rw [AddSubgroup.mem_zmultiples_iff] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hdoublezero : t + t = 0 := by
      rw [← ha]
      calc
        a • ((M : ℕ) : ZMod N) + a • ((M : ℕ) : ZMod N) =
            a • (((M : ℕ) : ZMod N) + (M : ZMod N)) :=
              (zsmul_add (M : ZMod N) (M : ZMod N) a).symm
        _ = 0 := by rw [half_add_half hN, smul_zero]
    have hhalfzero : (M : ZMod N) = 0 := by
      rw [← ht, hdoublezero]
    exact half_ne_zero hN (by omega) hhalfzero
  rcases zmod_eq_zero_or_half_of_add_self_eq_zero hM (f t) hself with
    hzero | hhalf
  · exact False.elim (hnonzero hzero)
  · exact hhalf

/-- Critical-range form: at positive depth, a quarter center for the current
half target reduces to the distinguished half target of the preceding
two-adic layer. -/
theorem criticalQuarterCenter_cast_eq_previousHalf
    {s q : ℕ} (hq : 0 < q) (hs : 1 ≤ s)
    (t : ZMod (2 ^ (s + 1) * q))
    (ht : t + t = ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    ZMod.castHom
        (show 2 ^ s * q ∣ 2 ^ (s + 1) * q by
          exact ⟨2, by rw [pow_succ]; ring⟩)
        (ZMod (2 ^ s * q)) t =
      ((2 ^ (s - 1) * q : ℕ) : ZMod (2 ^ s * q)) := by
  haveI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num) _) hq).ne'⟩
  cases s with
  | zero => omega
  | succ d =>
      have hN : 2 ^ (d + 1 + 1) * q = 2 * (2 ^ (d + 1) * q) := by
        rw [pow_succ]
        ring
      have hM : 2 ^ (d + 1) * q = 2 * (2 ^ d * q) := by
        rw [pow_succ]
        ring
      simpa using quarterCenter_cast_eq_half hN hM
        (mul_pos (pow_pos (by norm_num) d) hq) t ht

/-- The numerical quarter obstruction retains its full six-coordinate
origin.  After reduction modulo `M`, the balanced sum of the three pure
centers minus the three triangle vertices is exactly the next half `K`.
Thus an all-zero half-witness triangle at modulus `N=4K` creates a canonical
half-target relation one two-adic layer down. -/
theorem exists_six_distinct_quarterCenter_casts_to_half_of_triangle_all_zero
    {N M K n : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 0) (hDAb : cDA b = 0) :
    ∃ x y z : Fin n,
      (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
      (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
      (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      cAB x = 2 ∧ cBD y = 2 ∧ cDA z = 2 ∧
      let t := g x + g y + g z - g a - g b - g d
      t + t = (M : ZMod N) ∧
        ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M) t =
          (K : ZMod M) := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz⟩ :=
    exists_six_distinct_pure_centers_of_triangle_all_zero
      g hg (half_add_half hN) hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  let t : ZMod N := g x + g y + g z - g a - g b - g d
  have ht : t + t = (M : ZMod N) :=
    double_balanced_center_sum_eq_target_of_pure_triangle
      g (half_add_half hN) hcAB hcBD hcDA a b d x y z hab hbd hda
        hAB hBD hDA hx.1 hx.2.1 hy.1 hy.2.1 hz.1 hz.2.1
        hABx hBDy hDAz
  have hcast := quarterCenter_cast_eq_half hN hM hK t ht
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz,
    ht, hcast⟩

/-- The transported balanced relation is an actual tail-light witness for
the coordinatewise reduction of the tuple.  This is the coefficient language
used by the existing collision/transition machinery, although no validity of
the reduced tuple is asserted here. -/
theorem exists_light_balancedSix_halfWitness_after_cast_of_triangle_all_zero
    {N M K n : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    {cAB cBD cDA : Fin n → ℤ}
    (hcAB : Witness g (M : ZMod N) cAB)
    (hcBD : Witness g (M : ZMod N) cBD)
    (hcDA : Witness g (M : ZMod N) cDA)
    (a b d : Fin n) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 0) (hDAb : cDA b = 0) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    ∃ x y z : Fin n,
      (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
      (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
      (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      cAB x = 2 ∧ cBD y = 2 ∧ cDA z = 2 ∧
      Witness (fun i ↦ f (g i)) (K : ZMod M)
        (balancedSixCoeffs x y z a b d) ∧
      (∀ i, balancedSixCoeffs x y z a b d i ≤ 1) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz,
      _ht, hcast⟩ :=
    exists_six_distinct_quarterCenter_casts_to_half_of_triangle_all_zero
      hN hM hK g hg hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  have hval :
      f (g x) + f (g y) + f (g z) - f (g a) - f (g b) - f (g d) =
        (K : ZMod M) := by
    simpa [f, map_add, map_sub] using hcast
  have hw := balancedSixCoeffs_witness (fun i ↦ f (g i))
    x y z a b d hab hbd hda hx hy hz hxy hyz hzx hval
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hABx, hBDy, hDAz,
    hw, balancedSixCoeffs_le_one x y z a b d hxy hyz hzx⟩

/-- Canonical-fan specialization of the quarter-center transport theorem.
The exact two-singleton fan does not merely force `4 ∣ N`: its three light
collision witnesses expose six distinct tuple coordinates whose balanced
value reduces to the half element in `ZMod M`. -/
theorem canonical_exactTriangle_two_zero_quarterCenter_casts_to_half_zmod
    {N M K m : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
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
    ∃ x y v : Fin (m + 1),
      (x ≠ j.succ ∧ x ≠ k.succ ∧ x ≠ z.succ) ∧
      (y ≠ k.succ ∧ y ≠ z.succ ∧ y ≠ j.succ) ∧
      (v ≠ z.succ ∧ v ≠ j.succ ∧ v ≠ k.succ) ∧
      x ≠ y ∧ y ≠ v ∧ v ≠ x ∧
      subsetCollisionCoeffs r.val.1 r.val.2 x = 2 ∧
      subsetCollisionCoeffs q.val.1 q.val.2 y = 2 ∧
      subsetCollisionCoeffs u.val.1 u.val.2 v = 2 ∧
      let t := g x + g y + g v - g j.succ - g k.succ - g z.succ
      t + t = (M : ZMod N) ∧
        ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M) t =
          (K : ZMod M) := by
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
    witness_of_subsetSum_eq_add g (half_ne_zero hN (by omega))
      hrcard r.property.2
  have hcq : Witness g (M : ZMod N) cq :=
    witness_of_subsetSum_eq_add g (half_ne_zero hN (by omega))
      hqcard q.property.2
  have hcu : Witness g (M : ZMod N) cu :=
    witness_of_subsetSum_eq_add g (half_ne_zero hN (by omega))
      hucard u.property.2
  have hR := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) r hr hrB
  have hQ := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) q hq hqB
  have hU := canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair
    (half_add_half hN) u hu huB
  exact exists_six_distinct_quarterCenter_casts_to_half_of_triangle_all_zero
    hN hM hK g hg hcr hcq hcu j.succ k.succ z.succ
      ((Fin.succ_injective _).ne hjk)
      ((Fin.succ_injective _).ne (Ne.symm hzk))
      ((Fin.succ_injective _).ne hzj)
      (by simpa [cr] using hR)
      (by simpa [cq] using hQ)
      (by simpa [cu] using hU)
      (by simpa [cr] using hrzero)
      (by simpa [cq] using hqzero)
      (by simpa [cu] using huzero)

/-- Witness-valued form of the canonical transport: the all-zero exact fan
produces a concrete light half-witness for the reduced tuple. -/
theorem canonical_exactTriangle_two_zero_light_halfWitness_after_cast_zmod
    {N M K m : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
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
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    ∃ x y v : Fin (m + 1),
      (x ≠ j.succ ∧ x ≠ k.succ ∧ x ≠ z.succ) ∧
      (y ≠ k.succ ∧ y ≠ z.succ ∧ y ≠ j.succ) ∧
      (v ≠ z.succ ∧ v ≠ j.succ ∧ v ≠ k.succ) ∧
      x ≠ y ∧ y ≠ v ∧ v ≠ x ∧
      subsetCollisionCoeffs r.val.1 r.val.2 x = 2 ∧
      subsetCollisionCoeffs q.val.1 q.val.2 y = 2 ∧
      subsetCollisionCoeffs u.val.1 u.val.2 v = 2 ∧
      Witness (fun i ↦ f (g i)) (K : ZMod M)
        (balancedSixCoeffs x y v j.succ k.succ z.succ) ∧
      (∀ i, balancedSixCoeffs x y v j.succ k.succ z.succ i ≤ 1) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  obtain ⟨x, y, v, hx, hy, hv, hxy, hyv, hvx, hrx, hqy, huv,
      _ht, hcast⟩ :=
    canonical_exactTriangle_two_zero_quarterCenter_casts_to_half_zmod
      hN hM hK g hg r q u hr hq hu hjk hzj hzk hrB hqB huB
        hrzero hqzero huzero
  have hval :
      f (g x) + f (g y) + f (g v) - f (g j.succ) - f (g k.succ) -
          f (g z.succ) = (K : ZMod M) := by
    simpa [f, map_add, map_sub] using hcast
  have hw := balancedSixCoeffs_witness (fun i ↦ f (g i))
    x y v j.succ k.succ z.succ
      ((Fin.succ_injective _).ne hjk)
      ((Fin.succ_injective _).ne (Ne.symm hzk))
      ((Fin.succ_injective _).ne hzj)
      hx hy hv hxy hyv hvx hval
  exact ⟨x, y, v, hx, hy, hv, hxy, hyv, hvx, hrx, hqy, huv, hw,
    balancedSixCoeffs_le_one x y v j.succ k.succ z.succ hxy hyv hvx⟩

end MinModulus
