import MinModulus.CycleFibreCapacity
import MinModulus.G1MersenneCharge

namespace MinModulus

open Finset

/-- A full own-size fibre cover makes its entire embedded image a
cyclic-kernel support transversal. -/
theorem cyclicKernelSupportTransversal_image_of_full_fibre_cover
    {m n M : ℕ} {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin n → G) (hg : ValidTuple g) (f : Fin m ↪ Fin n)
    (hpref : ∀ i, g (f i) = τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m),
      s.card = m ∧ (s.map u).sum = z)
    (v : ZMod M) :
    CyclicKernelSupportTransversal g (τ v) (Finset.univ.image f) := by
  classical
  intro z _hzne c hc
  by_contra hnot
  push Not at hnot
  have hzero (i : Fin m) : c (f i) = 0 :=
    hnot _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let w : ZMod M := (∑ i, u i) - z • v
  obtain ⟨s, hscard, hsvalue⟩ := hcover w
  let delta : Fin m → ℤ := fun i ↦ (s.count i : ℤ) - 1
  have hscount : (∑ i : Fin m, s.count i) = m := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
    exact hscard
  have hdelta : (∑ i, delta i) = 0 := by
    dsimp [delta]
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hscount]
    simp
  have hsweight : (∑ i : Fin m, s.count i • g (f i)) = τ w := by
    have hsum : (∑ i : Fin m, s.count i • g (f i)) =
        (s.map (fun i ↦ g (f i))).sum := by
      rw [Finset.sum_multiset_map_count]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hcount : s.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
      simp [hcount]
    rw [hsum]
    simp only [hpref]
    simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def]
      using congrArg τ hsvalue
  have hdvalue : (∑ i, delta i • g (f i)) = -(z • τ v) := by
    simp only [delta, sub_smul, natCast_zsmul, one_smul, Finset.sum_sub_distrib]
    rw [hsweight]
    simp only [hpref, ← map_sum]
    dsimp [w]
    rw [map_sub, map_zsmul]
    abel
  let D : Fin n → ℤ := Function.extend f delta (fun _ ↦ 0)
  have hDsum : (∑ i, D i) = 0 := by
    exact (sum_extend_embedding_zero f delta).trans hdelta
  have hDvalue : (∑ i, D i • g i) = -(z • τ v) := by
    exact (sum_zsmul_extend_embedding_zero f delta g).trans hdvalue
  have hDleft (i : Fin m) : D (f i) = delta i :=
    f.injective.extend_apply delta (fun _ ↦ 0) i
  have hDoutside (j : Fin n) (hj : ¬ ∃ i, f i = j) : D j = 0 :=
    Function.extend_apply' delta (fun _ ↦ 0) j hj
  apply (validTuple_iff_no_zero_witness g).mp hg (c + D)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hC
    apply hc.1
    funext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      exact hzero i
    · have h := congrFun hC j
      simpa only [Pi.add_apply, Pi.zero_apply, hDoutside j hj, add_zero] using h
  · intro j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [Pi.add_apply, hzero, zero_add, hDleft, delta]
      omega
    · simpa only [Pi.add_apply, hDoutside j hj, add_zero] using hc.2.1 j
  · simp only [Pi.add_apply, Finset.sum_add_distrib, hc.2.2.1, hDsum, add_zero]
  · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hc.2.2.2,
      hDvalue, add_neg_cancel]

/-- Minimal cyclic-kernel descent can be chosen inside any given support
transversal, retaining the quotient and every private witness. -/
theorem exists_minimalCyclicKernelTransversal_descent_subset
    {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (y : ZMod N)
    {L : Finset (Fin n)} (hL : CyclicKernelSupportTransversal g y L) :
    ∃ B : Finset (Fin n), B ⊆ L ∧
      MinimalCyclicKernelSupportTransversal g y B ∧
      AdmitsValidTuple (n - B.card) (N / addOrderOf y) ∧
      ∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin n → ℤ,
        z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
        ∀ a ∈ B, a ≠ b → c a = 0 := by
  classical
  obtain ⟨B, hBL, hmin⟩ := exists_minimalCyclicKernelSupportTransversal_subset g y hL
  let R : Finset (Fin n) := Finset.univ \ B
  let e : Fin R.card ↪ Fin n := (R.orderEmbOfFin rfl).toEmbedding
  have hhit : CyclicKernelWitnessTransversal g y e :=
    minimalCyclicKernelTransversal_complement g y hmin
  have hdesc : AdmitsValidTuple R.card (N / addOrderOf y) :=
    admitsValidTuple_div_addOrderOf_of_cyclicKernelTransversal g hg y e hhit
  have hRcard : R.card = n - B.card := by
    simp [R, Finset.card_sdiff_of_subset (Finset.subset_univ B)]
  refine ⟨B, hBL, hmin, by simpa [hRcard] using hdesc, ?_⟩
  intro b hb
  exact exists_private_witness_of_minimalCyclicKernelTransversal g y hmin hb

/-- A support transversal of size d for a kernel of exact Mersenne order
contains a minimal descent transversal. Charge failure forces equality. -/
theorem exists_cycle_supported_descent_of_full_transversal
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (hd : 2 ≤ d) (ht : 1 ≤ t)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    (y : ZMod (2 ^ t * q)) (horder : addOrderOf y = 2 ^ d - 1)
    (L : Finset (Fin (n + 1))) (hLcard : L.card = d)
    (hL : CyclicKernelSupportTransversal g y L) :
    ∃ B : Finset (Fin (n + 1)), B ⊆ L ∧
      OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d ∧
      (OddPrimaryRecursiveCounterexample (n + 1) B.card t q (addOrderOf y) ∨ B = L) := by
  classical
  obtain ⟨B, hBL, hmin, hquotient, hprivate⟩ :=
    exists_minimalCyclicKernelTransversal_descent_subset g hg y hL
  have hodd : Odd (addOrderOf y) := by
    rw [horder]
    exact odd_two_pow_sub_one (by omega)
  have hrN : addOrderOf y ∣ 2 ^ t * q := by
    simpa using addOrderOf_dvd_card (x := y)
  have hrq : addOrderOf y ∣ q :=
    (hodd.coprime_two_right.pow_right t).dvd_of_dvd_mul_left hrN
  have hqpos : 0 < q := by
    exact Nat.pos_of_ne_zero (fun hq ↦ NeZero.ne (2 ^ t * q) (by simp [hq]))
  have hrTwo : 2 ≤ addOrderOf y := by
    have hpow := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hd
    norm_num at hpow
    omega
  have hstrict : q / addOrderOf y < q := Nat.div_lt_self hqpos (by omega)
  have hdesc : AdmitsValidTuple (n + 1 - B.card) (2 ^ t * (q / addOrderOf y)) := by
    rwa [Nat.mul_div_assoc (2 ^ t) hrq] at hquotient
  have hlower : 2 ^ (d - 1) ≤ addOrderOf y := by
    have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (d - 1) := by rw [pow_succ, Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    omega
  rcases oddPrimaryRecursiveCounterexample_or_chargeFailure hrq hcritical hdesc with hrec | hfail
  · exact ⟨B, hBL, ⟨hmin, hdesc, hprivate, hlower, hrq, hstrict, Or.inl hrec⟩,
      Or.inl hrec⟩
  · have hB : B.Nonempty := nonempty_of_oddPrimaryStratumChargeFailure (by omega) hfail
    have hnotSmall := not_nearTotal_minimalCyclicKernelTransversal_of_order_le_oddFactor
      ht g hg hcritical (Nat.le_of_dvd hqpos hrq) hmin hB
    have hkeep : 2 ≤ n + 1 - B.card := by omega
    have hBcard : B.card ≤ n + 1 := by simpa using Finset.card_le_univ B
    have hdB : d ≤ B.card := cycle_length_le_card_of_mersenne_chargeFailure
      hBcard hkeep (by omega) hfail
    have hLB : L.card ≤ B.card := by omega
    have hfull : B = L := Finset.eq_of_subset_of_card_le hBL hLB
    exact ⟨B, hBL, ⟨hmin, hdesc, hprivate, hlower, hrq, hstrict,
      Or.inr ⟨hB, hfail, hkeep, by omega⟩⟩, Or.inr hfull⟩

/-- An embedded affine doubling cycle supplies a minimal descent transversal
inside the cycle. The only failed-charge alternative deletes the whole cycle. -/
theorem exists_cycle_supported_descent_of_doubling_subtuple
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (hd : 2 ≤ d) (ht : 1 ≤ t)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    (leaf : Fin d ↪ Fin (n + 1)) (base : ZMod (2 ^ t * q))
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j, g (leaf (R j)) - base = 2 • (g (leaf j) - base)) :
    ∃ a : Fin d, ∃ B : Finset (Fin (n + 1)),
      B ⊆ Finset.univ.image leaf ∧
      addOrderOf (g (leaf a) - base) = 2 ^ d - 1 ∧
      OddPrimaryFullCycleMinimalTransversalChargeDescent g (g (leaf a) - base) B d ∧
      (OddPrimaryRecursiveCounterexample (n + 1) B.card t q
        (addOrderOf (g (leaf a) - base)) ∨ B = Finset.univ.image leaf) := by
  classical
  letI : NeZero (2 ^ d - 1) := ⟨by
    have h := Nat.one_lt_two_pow (by omega : d ≠ 0)
    omega⟩
  let x : Fin d → ZMod (2 ^ t * q) := fun j ↦ g (leaf j) - base
  have hx : ValidTuple x :=
    validTuple_sub_const (fun j ↦ g (leaf j)) (validTuple_embedding leaf g hg) base
  obtain ⟨a, e, he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) x hx R hdouble
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hd x hx R hdouble a
  obtain ⟨τ, hτ, hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (x a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2 ^ d - 1)) = r • x a := by
    have hr : (r : ZMod (2 ^ d - 1)) = r • (1 : ZMod (2 ^ d - 1)) := by simp
    rw [hr, map_nsmul, hτone]
  let u : Fin d → ZMod (2 ^ d - 1) := fun i ↦ ((2 ^ (e.symm i).val : ℕ) : ZMod (2 ^ d - 1))
  have hpref : ∀ i, g (leaf i) - base = τ (u i) := by
    intro i
    rw [hτnat]
    exact (by simpa only [Equiv.apply_symm_apply, x] using he (e.symm i))
  have hcover (z : ZMod (2 ^ d - 1)) :
      ∃ s : Multiset (Fin d), s.card = d ∧ (s.map u).sum = z := by
    obtain ⟨s, hs, hvalue⟩ := exists_power_multiset_sum_at_mersenne hd z
    exact ⟨s.map e, by simpa only [Multiset.card_map] using hs,
      by simpa only [Multiset.map_map, Function.comp_def, u, Equiv.symm_apply_apply] using hvalue⟩
  have htranslated : CyclicKernelSupportTransversal (fun j ↦ g j - base)
      (x a) (Finset.univ.image leaf) := by
    rw [← hτone]
    exact cyclicKernelSupportTransversal_image_of_full_fibre_cover τ u
      (fun j ↦ g j - base) (validTuple_sub_const g hg base) leaf hpref hcover 1
  have hL : CyclicKernelSupportTransversal g (x a) (Finset.univ.image leaf) := by
    intro z hz c hc
    apply htranslated z hz c
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hc.2.2.1, zero_smul, sub_zero, hc.2.2.2]
  have hLcard : (Finset.univ.image leaf).card = d := by
    simp [Finset.card_image_of_injective _ leaf.injective]
  obtain ⟨B, hBL, hdesc, hsplit⟩ := exists_cycle_supported_descent_of_full_transversal
    hd ht g hg hcritical (x a) ho (Finset.univ.image leaf) hLcard hL
  exact ⟨a, B, hBL, ho, hdesc, hsplit⟩

/-- The saturated G1 pure-star algebra gives descent supported on its leaf
cycle; charge failure forces deletion of exactly that cycle. -/
theorem PureEdgeStarLeafPermutationAlgebra.exists_cycle_supported_descent
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (n + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (n + 1))
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center) :
    ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (n + 1)),
      B ⊆ Finset.univ.image (fun j : Fin d ↦ (T^[j.val] a : Fin (n + 1))) ∧
      addOrderOf y = 2 ^ d - 1 ∧
      OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d ∧
      (OddPrimaryRecursiveCounterexample (n + 1) B.card t q (addOrderOf y) ∨
        B = Finset.univ.image (fun j : Fin d ↦ (T^[j.val] a : Fin (n + 1)))) := by
  let leafFun : Fin d → Fin (n + 1) :=
    fun j ↦ (T^[j.val] a : Fin (n + 1))
  have hleaf : Function.Injective leafFun := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hjk
  let leaf : Fin d ↪ Fin (n + 1) := ⟨leafFun, hleaf⟩
  obtain ⟨P, S, hlocal, _hsum⟩ := halg
  let R : Equiv.Perm (Fin d) := P.symm.trans S
  have hdouble : ∀ j, g (leaf (R j)) - (h + g r) =
      2 • (g (leaf j) - (h + g r)) := by
    intro j
    have hrel : (2 : ℤ) • g (leaf j) =
        h + g r + g (leaf (R j)) := by
      simpa [leaf, leafFun, R] using (hlocal (P.symm j)).2.2.2.2
    rw [two_zsmul] at hrel
    rw [two_nsmul]
    calc
      g (leaf (R j)) - (h + g r) =
          (h + g r + g (leaf (R j))) -
            ((h + g r) + (h + g r)) := by abel
      _ = (g (leaf j) + g (leaf j)) -
            ((h + g r) + (h + g r)) := by rw [← hrel]
      _ = (g (leaf j) - (h + g r)) +
            (g (leaf j) - (h + g r)) := by abel
  obtain ⟨i, B, hBL, horder, hdesc, hsplit⟩ :=
    exists_cycle_supported_descent_of_doubling_subtuple
      hcycle.1 ht g hg hcritical leaf (h + g r) R hdouble
  exact ⟨g (leaf i) - (h + g r), B, hBL, horder, hdesc, hsplit⟩

end MinModulus
