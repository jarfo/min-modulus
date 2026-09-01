/-
# Padding-weighted count for the quarter-witness quartet

Every tail-light witness has a canonical disjoint positive/negative tail
shape even when its target is not an involution.  Its common-padding fiber
therefore contributes the usual exact power-of-two weight to the translated
subset-sum overlap.  Applying this to the quarter quartet gives four distinct
reduced shapes whose weights add without duplication.
-/
import MinModulus.G1QuarterWitnessQuartet

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The disjoint reduced collision encoded by the positive and negative tail
sets of a light witness.  No order-two assumption on the target is needed. -/
def reducedCollisionOfTailLightWitness
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    ReducedSubsetSumCollision g h :=
  ⟨(witnessPositiveTail c, witnessNegativeTail c),
    witnessTails_disjoint c, witnessTails_value g hc hceil⟩

omit [DecidableEq G] in
/-- The reduced tail shape reconstructs the entire light coefficient vector,
including its anchor coefficient. -/
theorem reducedCollisionOfTailLightWitness_coeffs
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (hceil : ∀ j : Fin m, c j.succ ≤ 1) :
    subsetCollisionCoeffs
        (reducedCollisionOfTailLightWitness g hc hceil).val.1
        (reducedCollisionOfTailLightWitness g hc hceil).val.2 = c := by
  exact subsetCollisionCoeffs_witnessTails c hc.2.2.1
    (fun j ↦ hc.2.1 j.succ) hceil

omit [DecidableEq G] in
/-- If every nonzero full coordinate of a light witness lies in `S`, then
its reduced tail support has cardinality at most `|S|`. -/
theorem reducedCollisionOfTailLightWitness_support_card_le
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (hceil : ∀ j : Fin m, c j.succ ≤ 1)
    (S : Finset (Fin (m + 1)))
    (hsupport : ∀ i, c i ≠ 0 → i ∈ S) :
    ((reducedCollisionOfTailLightWitness g hc hceil).val.1 ∪
        (reducedCollisionOfTailLightWitness g hc hceil).val.2).card ≤
      S.card := by
  let T := (reducedCollisionOfTailLightWitness g hc hceil).val.1 ∪
    (reducedCollisionOfTailLightWitness g hc hceil).val.2
  have hsubset : T.image Fin.succ ⊆ S := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    apply hsupport j.succ
    change j ∈ witnessPositiveTail c ∪ witnessNegativeTail c at hj
    rcases Finset.mem_union.mp hj with hj | hj
    · simp [witnessPositiveTail] at hj
      omega
    · simp [witnessNegativeTail] at hj
      omega
  change T.card ≤ S.card
  rw [← Finset.card_image_of_injective T (Fin.succ_injective m)]
  exact Finset.card_le_card hsubset

/-- The balanced six-point vector is supported on its six displayed
coordinates. -/
theorem balancedSixCoeffs_ne_zero_mem
    (x y z a b d i : Fin (m + 1))
    (hi : balancedSixCoeffs x y z a b d i ≠ 0) :
    i ∈ ({x, y, z, a, b, d} : Finset (Fin (m + 1))) := by
  contrapose! hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  push Not at hi
  simp [balancedSixCoeffs, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
    hi.2.2.2.2.1, hi.2.2.2.2.2]

/-- A balanced pair vector is supported on its four displayed
coordinates. -/
theorem balancedPairCoeffs_ne_zero_mem
    (p q a b i : Fin (m + 1))
    (hi : balancedPairCoeffs p q a b i ≠ 0) :
    i ∈ ({p, q, a, b} : Finset (Fin (m + 1))) := by
  contrapose! hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  push Not at hi
  simp [balancedPairCoeffs, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

omit [DecidableEq G] in
/-- Distinct light coefficient vectors give distinct reduced collision
shapes. -/
theorem reducedCollisionOfTailLightWitness_ne_of_coeff_ne
    (g : Fin (m + 1) → G) {h : G}
    {c₁ c₂ : Fin (m + 1) → ℤ}
    (hc₁ : Witness g h c₁) (hceil₁ : ∀ j : Fin m, c₁ j.succ ≤ 1)
    (hc₂ : Witness g h c₂) (hceil₂ : ∀ j : Fin m, c₂ j.succ ≤ 1)
    (hne : c₁ ≠ c₂) :
    reducedCollisionOfTailLightWitness g hc₁ hceil₁ ≠
      reducedCollisionOfTailLightWitness g hc₂ hceil₂ := by
  intro heq
  apply hne
  calc
    c₁ = subsetCollisionCoeffs
        (reducedCollisionOfTailLightWitness g hc₁ hceil₁).val.1
        (reducedCollisionOfTailLightWitness g hc₁ hceil₁).val.2 :=
      (reducedCollisionOfTailLightWitness_coeffs g hc₁ hceil₁).symm
    _ = subsetCollisionCoeffs
        (reducedCollisionOfTailLightWitness g hc₂ hceil₂).val.1
        (reducedCollisionOfTailLightWitness g hc₂ hceil₂).val.2 := by rw [heq]
    _ = c₂ := reducedCollisionOfTailLightWitness_coeffs g hc₂ hceil₂

/-- Exact omission data separates two coefficient vectors whenever one
omission set contains a coordinate absent from the other. -/
theorem coeff_ne_of_exactOmissions_of_mem_not_mem
    {c₁ c₂ : Fin (m + 1) → ℤ} {S T : Finset (Fin (m + 1))}
    (hS : ExactOmissions c₁ S) (hT : ExactOmissions c₂ T)
    (e : Fin (m + 1)) (heS : e ∈ S) (heT : e ∉ T) : c₁ ≠ c₂ := by
  intro heq
  have hc₁ : c₁ e = -1 := (hS e).2 heS
  have hc₂ : c₂ e = -1 := by rw [← heq]; exact hc₁
  exact heT ((hT e).1 hc₂)

/-- Four pairwise-distinct reduced shapes contribute the sum of their exact
padding weights to the overlap with an arbitrary translate. -/
theorem four_distinct_reducedCollisionWeights_le_overlap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G)
    (r₀ r₁ r₂ r₃ : ReducedSubsetSumCollision g h)
    (h01 : r₀ ≠ r₁) (h02 : r₀ ≠ r₂) (h03 : r₀ ≠ r₃)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃) :
    reducedCollisionWeight (m := m) r₀ +
        reducedCollisionWeight (m := m) r₁ +
        reducedCollisionWeight (m := m) r₂ +
        reducedCollisionWeight (m := m) r₃ ≤
      ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card := by
  classical
  rw [card_subsetSumOverlap_eq_sum_reduced_weights g hg h]
  have hsub : ({r₀, r₁, r₂, r₃} :
      Finset (ReducedSubsetSumCollision g h)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset hsub
    (f := fun r : ReducedSubsetSumCollision g h ↦
      reducedCollisionWeight (m := m) r)
  simpa [reducedCollisionWeight, Nat.add_assoc, h01, h02, h03, h12, h13, h23,
    Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13,
    Ne.symm h23] using hle

/-- The all-zero triangle contributes four distinct padding fibers to the
quarter translate overlap.  This is the first additive, multi-layer count
extracted from the quarter quartet. -/
theorem exists_four_distinct_quarterLayers_of_triangle_all_zero
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {cAB cBD cDA : Fin (m + 1) → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin (m + 1)) (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hABd : cAB d = 0) (hBDa : cBD a = 0) (hDAb : cDA b = 0) :
    ∃ t : G, ∃ rD rAB rBD rDA : ReducedSubsetSumCollision g t,
      t + t = h ∧
      rD ≠ rAB ∧ rD ≠ rBD ∧ rD ≠ rDA ∧
      rAB ≠ rBD ∧ rAB ≠ rDA ∧ rBD ≠ rDA ∧
      reducedCollisionWeight (m := m) rD +
      reducedCollisionWeight (m := m) rAB +
          reducedCollisionWeight (m := m) rBD +
          reducedCollisionWeight (m := m) rDA ≤
        ((subsetSumRange g) ∩ (subsetSumShiftRange g t)).card ∧
      2 ^ (m - 6) + 3 * 2 ^ (m - 4) ≤
        ((subsetSumRange g) ∩ (subsetSumShiftRange g t)).card := by
  obtain ⟨x, y, z, t, hx, hy, hz, hxy, hyz, hzx,
      _hABx, _hBDy, _hDAz, ht, hD, hDomit, hABq, hABomit,
      hBDq, hBDomit, hDAq, hDAomit, _hABsum, _hBDsum, _hDAsum⟩ :=
    exists_light_quarterWitness_quartet_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  have hDceil : ∀ j : Fin m,
      balancedSixCoeffs x y z a b d j.succ ≤ 1 :=
    fun j ↦ balancedSixCoeffs_le_one x y z a b d hxy hyz hzx j.succ
  have hABceil : ∀ j : Fin m,
      balancedPairCoeffs x d y z j.succ ≤ 1 :=
    fun j ↦ balancedPairCoeffs_le_one x d y z hx.2.2 j.succ
  have hBDceil : ∀ j : Fin m,
      balancedPairCoeffs y a z x j.succ ≤ 1 :=
    fun j ↦ balancedPairCoeffs_le_one y a z x hy.2.2 j.succ
  have hDAceil : ∀ j : Fin m,
      balancedPairCoeffs z b x y j.succ ≤ 1 :=
    fun j ↦ balancedPairCoeffs_le_one z b x y hz.2.2 j.succ
  let rD := reducedCollisionOfTailLightWitness g hD hDceil
  let rAB := reducedCollisionOfTailLightWitness g hABq hABceil
  let rBD := reducedCollisionOfTailLightWitness g hBDq hBDceil
  let rDA := reducedCollisionOfTailLightWitness g hDAq hDAceil
  have hrDsupport : (rD.val.1 ∪ rD.val.2).card ≤ 6 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hD hDceil ({x, y, z, a, b, d} : Finset (Fin (m + 1)))
        (balancedSixCoeffs_ne_zero_mem x y z a b d)
    have hle' : (rD.val.1 ∪ rD.val.2).card ≤
        ({x, y, z, a, b, d} : Finset (Fin (m + 1))).card := by
      simpa [rD] using hle
    exact hle'.trans Finset.card_le_six
  have hrABsupport : (rAB.val.1 ∪ rAB.val.2).card ≤ 4 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hABq hABceil ({x, d, y, z} : Finset (Fin (m + 1)))
        (balancedPairCoeffs_ne_zero_mem x d y z)
    have hle' : (rAB.val.1 ∪ rAB.val.2).card ≤
        ({x, d, y, z} : Finset (Fin (m + 1))).card := by
      simpa [rAB] using hle
    exact hle'.trans Finset.card_le_four
  have hrBDsupport : (rBD.val.1 ∪ rBD.val.2).card ≤ 4 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hBDq hBDceil ({y, a, z, x} : Finset (Fin (m + 1)))
        (balancedPairCoeffs_ne_zero_mem y a z x)
    have hle' : (rBD.val.1 ∪ rBD.val.2).card ≤
        ({y, a, z, x} : Finset (Fin (m + 1))).card := by
      simpa [rBD] using hle
    exact hle'.trans Finset.card_le_four
  have hrDAsupport : (rDA.val.1 ∪ rDA.val.2).card ≤ 4 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hDAq hDAceil ({z, b, x, y} : Finset (Fin (m + 1)))
        (balancedPairCoeffs_ne_zero_mem z b x y)
    have hle' : (rDA.val.1 ∪ rDA.val.2).card ≤
        ({z, b, x, y} : Finset (Fin (m + 1))).card := by
      simpa [rDA] using hle
    exact hle'.trans Finset.card_le_four
  have hcDAB : balancedSixCoeffs x y z a b d ≠
      balancedPairCoeffs x d y z :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hDomit hABomit a
      (by simp) (by simp [Ne.symm hy.2.2, Ne.symm hz.2.1])
  have hcDBD : balancedSixCoeffs x y z a b d ≠
      balancedPairCoeffs y a z x :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hDomit hBDomit b
      (by simp) (by simp [Ne.symm hz.2.2, Ne.symm hx.2.1])
  have hcDDA : balancedSixCoeffs x y z a b d ≠
      balancedPairCoeffs z b x y :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hDomit hDAomit d
      (by simp) (by simp [Ne.symm hx.2.2, Ne.symm hy.2.1])
  have hcABBD : balancedPairCoeffs x d y z ≠
      balancedPairCoeffs y a z x :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hABomit hBDomit y
      (by simp) (by simp [Ne.symm hxy, hyz])
  have hcABDA : balancedPairCoeffs x d y z ≠
      balancedPairCoeffs z b x y :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hABomit hDAomit z
      (by simp) (by simp [hzx, Ne.symm hyz])
  have hcBDDA : balancedPairCoeffs y a z x ≠
      balancedPairCoeffs z b x y :=
    coeff_ne_of_exactOmissions_of_mem_not_mem hBDomit hDAomit z
      (by simp) (by simp [hzx, Ne.symm hyz])
  have hrDAB : rD ≠ rAB :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hD hDceil hABq hABceil hcDAB
  have hrDBD : rD ≠ rBD :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hD hDceil hBDq hBDceil hcDBD
  have hrDDA : rD ≠ rDA :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hD hDceil hDAq hDAceil hcDDA
  have hrABBD : rAB ≠ rBD :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hABq hABceil hBDq hBDceil hcABBD
  have hrABDA : rAB ≠ rDA :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hABq hABceil hDAq hDAceil hcABDA
  have hrBDDA : rBD ≠ rDA :=
    reducedCollisionOfTailLightWitness_ne_of_coeff_ne
      g hBDq hBDceil hDAq hDAceil hcBDDA
  have hfour := four_distinct_reducedCollisionWeights_le_overlap
    g hg t rD rAB rBD rDA hrDAB hrDBD hrDDA hrABBD hrABDA hrBDDA
  have hwD : 2 ^ (m - 6) ≤ reducedCollisionWeight (m := m) rD := by
    simp only [reducedCollisionWeight]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwAB : 2 ^ (m - 4) ≤ reducedCollisionWeight (m := m) rAB := by
    simp only [reducedCollisionWeight]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwBD : 2 ^ (m - 4) ≤ reducedCollisionWeight (m := m) rBD := by
    simp only [reducedCollisionWeight]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwDA : 2 ^ (m - 4) ≤ reducedCollisionWeight (m := m) rDA := by
    simp only [reducedCollisionWeight]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have huniform : 2 ^ (m - 6) + 3 * 2 ^ (m - 4) ≤
      ((subsetSumRange g) ∩ (subsetSumShiftRange g t)).card := by
    omega
  exact ⟨t, rD, rAB, rBD, rDA, ht, hrDAB, hrDBD, hrDDA,
    hrABBD, hrABDA, hrBDDA, hfour, huniform⟩

/-- Canonical exact-fan specialization of the four-fiber count. -/
theorem canonical_exactTriangle_two_zero_four_quarterLayers_zmod
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
    ∃ t : ZMod N,
      ∃ rD rAB rBD rDA : ReducedSubsetSumCollision g t,
      t + t = (M : ZMod N) ∧
      rD ≠ rAB ∧ rD ≠ rBD ∧ rD ≠ rDA ∧
      rAB ≠ rBD ∧ rAB ≠ rDA ∧ rBD ≠ rDA ∧
      reducedCollisionWeight (m := m) rD +
      reducedCollisionWeight (m := m) rAB +
          reducedCollisionWeight (m := m) rBD +
          reducedCollisionWeight (m := m) rDA ≤
        ((subsetSumRange g) ∩ (subsetSumShiftRange g t)).card ∧
      2 ^ (m - 6) + 3 * 2 ^ (m - 4) ≤
        ((subsetSumRange g) ∩ (subsetSumShiftRange g t)).card := by
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
  exact exists_four_distinct_quarterLayers_of_triangle_all_zero
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
