import MinModulus.G1CycleSupportedDescent
import MinModulus.CycleThinCover

namespace MinModulus
open Finset

/-- A kernel witness meeting a full thin zero-sum fibre in at most one
coordinate must omit that coordinate and target its negative. -/
theorem private_fibre_witness_owner_and_target
    {m n M : ℕ} {G : Type*} [AddCommGroup G]
    (hm : 0 < m) (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin n → G) (hg : ValidTuple g) (f : Fin m ↪ Fin n)
    (hpref : ∀ i, g (f i) = τ (u i)) (hsum : (∑ i, u i) = 0)
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card = m ∧ (s.map u).sum = z)
    (hthin : ∀ z : ZMod M, z ≠ 0 → ∃ s : Multiset (Fin m),
      s.card = m - 1 ∧ (s.map u).sum = z)
    (b : Fin m) (v : ZMod M) (c : Fin n → ℤ) (hc : Witness g (τ v) c)
    (hzero : ∀ i : Fin m, i ≠ b → c (f i) = 0) :
    c (f b) = -1 ∧ τ v = -g (f b) := by
  classical
  obtain ⟨j, hj, hcj⟩ : ∃ j : Fin n, (¬ ∃ i, f i = j) ∧ c j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    have hsupport (j : Fin n) (hj : j ≠ f b) : c j = 0 := by
      by_cases hin : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := hin
        exact hzero i (fun hi ↦ hj (congrArg f hi))
      · exact hnot j (fun i hi ↦ hin ⟨i, hi⟩)
    have hsumc : (∑ j, c j) = c (f b) := by
      apply Finset.sum_eq_single (f b)
      · intro j _ hj
        exact hsupport j hj
      · simp
    have hcb : c (f b) = 0 := hsumc.symm.trans hc.2.2.1
    apply hc.1
    funext j
    by_cases hj : j = f b
    · simpa only [hj, Pi.zero_apply] using hcb
    · exact hsupport j hj
  have hreplace (s : Multiset (Fin m)) (hcard : s.card = m)
      (hvalue : (s.map u).sum = -v)
      (hfloor : ∀ i, -1 ≤ c (f i) + ((s.count i : ℤ) - 1)) : False := by
    let delta : Fin m → ℤ := fun i ↦ (s.count i : ℤ) - 1
    have hscount : (∑ i : Fin m, s.count i) = m := by
      rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
      exact hcard
    have hdelta : (∑ i, delta i) = 0 := by
      dsimp [delta]
      rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hscount]
      simp
    have hsweight : (∑ i : Fin m, s.count i • g (f i)) = τ (-v) := by
      have hsum' : (∑ i : Fin m, s.count i • g (f i)) =
          (s.map (fun i ↦ g (f i))).sum := by
        rw [Finset.sum_multiset_map_count]
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hcount : s.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
        simp [hcount]
      rw [hsum']
      simp only [hpref]
      simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def]
        using congrArg τ hvalue
    have hdvalue : (∑ i, delta i • g (f i)) = -τ v := by
      simp only [delta, sub_smul, natCast_zsmul, one_smul, Finset.sum_sub_distrib]
      rw [hsweight]
      simp only [hpref, ← map_sum, hsum, map_zero, map_neg, sub_zero]
    let D : Fin n → ℤ := Function.extend f delta (fun _ ↦ 0)
    have hDsum : (∑ i, D i) = 0 := (sum_extend_embedding_zero f delta).trans hdelta
    have hDvalue : (∑ i, D i • g i) = -τ v :=
      (sum_zsmul_extend_embedding_zero f delta g).trans hdvalue
    have hDleft (i : Fin m) : D (f i) = delta i :=
      f.injective.extend_apply delta (fun _ ↦ 0) i
    have hDoutside (j : Fin n) (hj : ¬ ∃ i, f i = j) : D j = 0 :=
      Function.extend_apply' delta (fun _ ↦ 0) j hj
    apply (validTuple_iff_no_zero_witness g).mp hg (c + D)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hC
      apply hcj
      have h := congrFun hC j
      simpa only [Pi.add_apply, hDoutside j hj, add_zero, Pi.zero_apply] using h
    · intro j
      by_cases hj : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := hj
        simpa only [Pi.add_apply, hDleft, delta] using hfloor i
      · simpa only [Pi.add_apply, hDoutside j hj, add_zero] using hc.2.1 j
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hc.2.2.1, hDsum, add_zero]
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hc.2.2.2,
        hDvalue, add_neg_cancel]
  have hcb : c (f b) = -1 := by
    by_contra hnot
    have hnonneg : 0 ≤ c (f b) := by have := hc.2.1 (f b); omega
    obtain ⟨s, hs, hv⟩ := hcover (-v)
    apply hreplace s hs hv
    intro i
    by_cases hi : i = b
    · subst i; omega
    · rw [hzero i hi]
      omega
  refine ⟨hcb, ?_⟩
  have hw : -v - u b = 0 := by
    by_contra hw
    obtain ⟨s, hs, hv⟩ := hthin (-v - u b) hw
    apply hreplace (b ::ₘ s)
    · simp only [Multiset.card_cons, hs]
      omega
    · simp only [Multiset.map_cons, Multiset.sum_cons, hv]
      abel
    · intro i
      by_cases hi : i = b
      · subst i
        simp only [hcb, Multiset.count_cons_self, Nat.cast_add, Nat.cast_one]
        omega
      · simp only [hzero i hi, Multiset.count_cons_of_ne hi, zero_add]
        omega
  have h := congrArg τ hw
  rw [map_sub, map_neg, map_zero, ← hpref b] at h
  simpa only [neg_neg] using congrArg Neg.neg (sub_eq_zero.mp h)

/-- Beside an outside coordinate killed by two, a full thin zero-sum
fibre admits no kernel witness supported on just one fibre coordinate. -/
theorem no_private_fibre_witness_beside_involution
    {m n M : ℕ} {G : Type*} [AddCommGroup G]
    (hm : 0 < m) (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin n → G) (hg : ValidTuple g) (f : Fin m ↪ Fin n)
    (hpref : ∀ i, g (f i) = τ (u i)) (hsum : (∑ i, u i) = 0)
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card = m ∧ (s.map u).sum = z)
    (hthin : ∀ z : ZMod M, z ≠ 0 → ∃ s : Multiset (Fin m),
      s.card = m - 1 ∧ (s.map u).sum = z)
    (r : Fin n) (hrout : ∀ i, f i ≠ r) (hr : g r + g r = 0)
    (b : Fin m) (v : ZMod M) (c : Fin n → ℤ) (hc : Witness g (τ v) c)
    (hzero : ∀ i : Fin m, i ≠ b → c (f i) = 0) : False := by
  classical
  obtain ⟨hcb, htarget⟩ := private_fibre_witness_owner_and_target
    hm τ u g hg f hpref hsum hcover hthin b v c hc hzero
  let D : Fin n → ℤ := Function.extend f (fun _ ↦ (-1 : ℤ)) (fun _ ↦ 0)
  have hDsum : (∑ i, D i) = -(m : ℤ) := by
    rw [sum_extend_embedding_zero]
    simp
  have hDvalue : (∑ i, D i • g i) = 0 := by
    rw [sum_zsmul_extend_embedding_zero]
    simp only [neg_one_zsmul, hpref]
    rw [Finset.sum_neg_distrib, ← map_sum, hsum, map_zero, neg_zero]
  have hDleft (i : Fin m) : D (f i) = -1 :=
    f.injective.extend_apply (fun _ ↦ (-1 : ℤ)) (fun _ ↦ 0) i
  have hDoutside (j : Fin n) (hj : ¬ ∃ i, f i = j) : D j = 0 :=
    Function.extend_apply' (fun _ ↦ (-1 : ℤ)) (fun _ ↦ 0) j hj
  have hDr : D r = 0 := hDoutside r (by rintro ⟨i, hi⟩; exact hrout i hi)
  have hDge (j : Fin n) : -1 ≤ D j := by
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hDleft]
    · rw [hDoutside j hj]
      omega
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkill : (m : ℤ) • g r = 0 := by
      rw [hk, Nat.cast_add, add_smul, ← smul_add, hr, smul_zero]
    let C : Fin n → ℤ := fun i ↦ D i + if i = r then (m : ℤ) else 0
    apply (validTuple_iff_no_zero_witness g).mp hg C
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hC
      have h := congrFun hC (f b)
      simp only [C, hDleft, hrout b, ↓reduceIte, add_zero, Pi.zero_apply] at h
      omega
    · intro i
      have := hDge i
      dsimp [C]
      split_ifs <;> omega
    · simp only [C, Finset.sum_add_distrib, hDsum]
      simp
    · simpa only [C, add_smul, Finset.sum_add_distrib, hDvalue, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, zero_add] using hkill
  · have hkill : ((m : ℤ) - 1) • g r = 0 := by
      have heq : (m : ℤ) - 1 = (k : ℤ) + k := by omega
      rw [heq, add_smul, ← smul_add, hr, smul_zero]
    let C : Fin n → ℤ := fun i ↦ c i + D i +
      (if i = f b then 1 else 0) + (if i = r then (m : ℤ) - 1 else 0)
    apply (validTuple_iff_no_zero_witness g).mp hg C
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hC
      have h := congrFun hC (f b)
      simp only [C, hcb, hDleft, hrout b, ↓reduceIte, add_zero, Pi.zero_apply] at h
      omega
    · intro j
      by_cases hj : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := hj
        dsimp [C]
        rw [hDleft]
        simp only [hrout i, ↓reduceIte, add_zero]
        by_cases hi : i = b
        · subst i
          simp only [hcb, ↓reduceIte]
          omega
        · have hne : f i ≠ f b := fun h ↦ hi (f.injective h)
          simp only [hzero i hi, hne, ↓reduceIte]
          omega
      · have hne : j ≠ f b := fun h ↦ hj ⟨b, h.symm⟩
        have hge := hc.2.1 j
        dsimp [C]
        simp only [hDoutside j hj, hne, ↓reduceIte, add_zero]
        split_ifs <;> omega
    · simp only [C, Finset.sum_add_distrib, hc.2.2.1, hDsum]
      simp
    · simp only [C, add_smul, Finset.sum_add_distrib, hc.2.2.2, hDvalue,
        ite_smul, zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, htarget, hkill, add_zero, neg_add_cancel]

/-- Any one coordinate can be retained when quotienting a full thin
zero-sum fibre beside an outside involution. -/
theorem cyclicKernelSupportTransversal_erase_fibre_beside_involution
    {m n M : ℕ} {G : Type*} [AddCommGroup G]
    (hm : 0 < m) (τ : ZMod M →+ G) (u : Fin m → ZMod M)
    (g : Fin n → G) (hg : ValidTuple g) (f : Fin m ↪ Fin n)
    (hpref : ∀ i, g (f i) = τ (u i)) (hsum : (∑ i, u i) = 0)
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card = m ∧ (s.map u).sum = z)
    (hthin : ∀ z : ZMod M, z ≠ 0 → ∃ s : Multiset (Fin m),
      s.card = m - 1 ∧ (s.map u).sum = z)
    (r : Fin n) (hrout : ∀ i, f i ≠ r) (hr : g r + g r = 0)
    (b : Fin m) (v : ZMod M) :
    CyclicKernelSupportTransversal g (τ v) ((Finset.univ.image f).erase (f b)) := by
  classical
  intro z _hz c hc
  by_contra hnot
  push Not at hnot
  apply no_private_fibre_witness_beside_involution hm τ u g hg f hpref hsum hcover hthin
    r hrout hr b (z • v) c (by simpa only [map_zsmul] using hc)
  intro i hi
  apply hnot (f i)
  exact Finset.mem_erase.mpr ⟨fun h ↦ hi (f.injective h),
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- An affine doubling cycle beside an outside translated involution gives
an actual recursive counterexample at a smaller odd factor. The chosen
minimal transversal deletes strictly fewer coordinates than the cycle. -/
theorem exists_recursive_descent_of_doubling_cycle_beside_involution
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (hd : 2 ≤ d) (ht : 1 ≤ t)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    (leaf : Fin d ↪ Fin (n + 1)) (base : ZMod (2 ^ t * q))
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j, g (leaf (R j)) - base = 2 • (g (leaf j) - base))
    (r : Fin (n + 1)) (hrout : ∀ j, leaf j ≠ r)
    (hr : (g r - base) + (g r - base) = 0) :
    ∃ i : Fin d, ∃ B : Finset (Fin (n + 1)),
      B ⊆ Finset.univ.image leaf ∧ B.card < d ∧
      addOrderOf (g (leaf i) - base) = 2 ^ d - 1 ∧
      OddPrimaryFullCycleMinimalTransversalChargeDescent g (g (leaf i) - base) B d ∧
      OddPrimaryRecursiveCounterexample (n + 1) B.card t q
        (addOrderOf (g (leaf i) - base)) := by
  classical
  letI : NeZero (2 ^ d - 1) := ⟨by
    have h := Nat.one_lt_two_pow (by omega : d ≠ 0)
    omega⟩
  obtain ⟨i, B, hBL, horder, hdesc, hsplit⟩ :=
    exists_cycle_supported_descent_of_doubling_subtuple hd ht g hg hcritical leaf base R hdouble
  let x : Fin d → ZMod (2 ^ t * q) := fun j ↦ g (leaf j) - base
  have hx : ValidTuple x :=
    validTuple_sub_const (fun j ↦ g (leaf j)) (validTuple_embedding leaf g hg) base
  obtain ⟨a, e, he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) x hx R hdouble
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hd x hx R hdouble a
  obtain ⟨τ, _hτ, hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (x a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2 ^ d - 1)) = r • x a := by
    have hr : (r : ZMod (2 ^ d - 1)) = r • (1 : ZMod (2 ^ d - 1)) := by simp
    rw [hr, map_nsmul, hτone]
  let u : Fin d → ZMod (2 ^ d - 1) := fun j ↦ ((2 ^ (e.symm j).val : ℕ) : ZMod (2 ^ d - 1))
  have hpref : ∀ j, g (leaf j) - base = τ (u j) := by
    intro j
    rw [hτnat]
    exact (by simpa only [Equiv.apply_symm_apply, x] using he (e.symm j))
  have hsum : (∑ j, u j) = 0 := by
    dsimp only [u]
    rw [Equiv.sum_comp e.symm (fun j : Fin d ↦ ((2 ^ j.val : ℕ) : ZMod (2 ^ d - 1))),
      ← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self]
  have hcover (z : ZMod (2 ^ d - 1)) :
      ∃ s : Multiset (Fin d), s.card = d ∧ (s.map u).sum = z := by
    obtain ⟨s, hs, hvalue⟩ := exists_power_multiset_sum_at_mersenne hd z
    exact ⟨s.map e, by simpa only [Multiset.card_map] using hs,
      by simpa only [Multiset.map_map, Function.comp_def, u, Equiv.symm_apply_apply] using hvalue⟩
  have hthin (z : ZMod (2 ^ d - 1)) (hz : z ≠ 0) :
      ∃ s : Multiset (Fin d), s.card = d - 1 ∧ (s.map u).sum = z := by
    obtain ⟨s, hs, hvalue⟩ := exists_power_multiset_card_pred_of_ne_zero hd z hz
    exact ⟨s.map e, by simpa only [Multiset.card_map] using hs,
      by simpa only [Multiset.map_map, Function.comp_def, u, Equiv.symm_apply_apply] using hvalue⟩
  have htrans := cyclicKernelSupportTransversal_erase_fibre_beside_involution (by omega)
    τ u (fun j ↦ g j - base) (validTuple_sub_const g hg base) leaf hpref hsum
    hcover hthin r hrout hr i (u i)
  rw [← hpref i] at htrans
  have hproper : CyclicKernelSupportTransversal g (g (leaf i) - base)
      ((Finset.univ.image leaf).erase (leaf i)) := by
    intro z hz c hc
    apply htrans z hz c
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hc.2.2.1, zero_smul, sub_zero, hc.2.2.2]
  have hneq : B ≠ Finset.univ.image leaf := by
    intro hfull
    have hmin := hdesc.1
    rw [hfull] at hmin
    exact hmin.2 (leaf i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hproper
  have hcard : B.card < d := by
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBL, hneq⟩)
    simpa only [Finset.card_image_of_injective _ leaf.injective, Finset.card_univ,
      Fintype.card_fin] using h
  exact ⟨i, B, hBL, hcard, horder, hdesc, hsplit.resolve_right hneq⟩

/-- The involution already present at a G1 pure-star center eliminates the
entire-cycle deletion alternative in the saturated permutation branch. -/
theorem PureEdgeStarLeafPermutationAlgebra.exists_recursive_descent
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (r : Fin (n + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (n + 1))
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center) :
    ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (n + 1)),
      B ⊆ Finset.univ.image (fun j : Fin d ↦ (T^[j.val] a : Fin (n + 1))) ∧
      B.card < d ∧ addOrderOf y = 2 ^ d - 1 ∧
      OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d ∧
      OddPrimaryRecursiveCounterexample (n + 1) B.card t q (addOrderOf y) := by
  let leafFun : Fin d → Fin (n + 1) :=
    fun j ↦ (T^[j.val] a : Fin (n + 1))
  have hleaf : Function.Injective leafFun := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hjk
  let leaf : Fin d ↪ Fin (n + 1) := ⟨leafFun, hleaf⟩
  have hrout : ∀ j, leaf j ≠ r := by
    intro j
    exact ((mem_witnessPureEdgeStarLeaves_iff g h r (leaf j)).mp (T^[j.val] a).property).1
  have hr : (g r - (h + g r)) + (g r - (h + g r)) = 0 := by
    have heq : g r - (h + g r) = -h := by abel
    rw [heq, ← neg_add, hh, neg_zero]
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
  obtain ⟨i, B, hBL, hcard, horder, hdesc, hrec⟩ :=
    exists_recursive_descent_of_doubling_cycle_beside_involution
      hcycle.1 ht g hg hcritical leaf (h + g r) R hdouble r hrout hr
  exact ⟨g (leaf i) - (h + g r), B, hBL, hcard, horder, hdesc, hrec⟩

/-- Odd-factor induction closes the saturated G1 permutation branch. -/
theorem PureEdgeStarLeafPermutationAlgebra.stratumBound_le_of_smaller_odd_factors
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (r : Fin (n + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (n + 1))
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center)
    (hIH : ∀ k q', q' < q → Odd q' → AdmitsValidTuple k (2 ^ t * q') →
      stratumBound k t ≤ 2 ^ t * q') :
    stratumBound (n + 1) t ≤ 2 ^ t * q := by
  by_contra hnot
  have hcritical : 2 ^ t * q < stratumBound (n + 1) t := by omega
  obtain ⟨y, B, _hBL, _hcard, _horder, hdesc, hrec⟩ :=
    halg.exists_recursive_descent ht g hg hcritical hh r T hcycle center
  have hdiv : addOrderOf y ∣ q := hdesc.2.2.2.2.1
  have hlt : q / addOrderOf y < q := hdesc.2.2.2.2.2.1
  exact (not_lt_of_ge (hIH (n + 1 - B.card) (q / addOrderOf y) hlt
    (odd_oddFactorQuotient hq hdiv) hrec.1)) hrec.2

/-- With smaller odd factors settled, the global G1 cycle trichotomy
retains only its two nonsaturated center-incidence alternatives. -/
theorem PureEdgeStarLeafPermutationOutcome.nonsaturated_of_smaller_odd_factors
    {n d t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (n + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (r : Fin (n + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (n + 1))
    (hout : PureEdgeStarLeafPermutationOutcome g h r T a d center)
    (hIH : ∀ k q', q' < q → Odd q' → AdmitsValidTuple k (2 ^ t * q') →
      stratumBound k t ≤ 2 ^ t * q') :
    2 * d + 1 ≤ n + 1 ∨
      (d + 2 ≤ n + 1 ∧ ∃ j k ell : Fin d,
        center j = (T^[k.val] a : Fin (n + 1)) ∧
        center ell ∉ Set.range (fun i : Fin d ↦ (T^[i.val] a : Fin (n + 1)))) := by
  rcases hout with hcap | hmixed | halg
  · exact Or.inl hcap
  · exact Or.inr hmixed
  · exact (not_lt_of_ge (halg.stratumBound_le_of_smaller_odd_factors
      ht hq g hg hh r T hcycle center hIH) hcritical).elim

end MinModulus
