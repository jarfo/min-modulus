import MinModulus.CycleSparseTargets
import MinModulus.G1SubtupleWitnessKernel

/-!
# Exact short-sum rigidity beside a Mersenne cycle

A valid zero-sum tuple closed under doubling predecessors has no nonempty
zero-sum multiset shorter than its own length. Every proper subset is its
unique shortest multiset representation. For a mapped Mersenne cycle,
this makes the sparse-target alternative exact, with a unique support.
-/

namespace MinModulus
open Finset

/-- A nonempty zero-sum multiset on a valid predecessor-closed zero-sum
family needs at least as many coins as the entire family. -/
theorem length_le_card_of_zero_sum_multiset_of_doubling_predecessors
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin m → G) (hx : ValidTuple x)
    (hzero : (∑ i, x i) = 0) (hpred : ∀ i, ∃ j, x i = 2 • x j)
    (s : Multiset (Fin m)) (hs : 0 < s.card) (hv : (s.map x).sum = 0) :
    m ≤ s.card := by
  classical
  by_contra hnot
  obtain ⟨t, ht, htv⟩ := exists_multiset_card_ge_of_doubling_predecessors
    x hpred s hs (by omega : s.card ≤ m - 1)
  have htpos : 0 < t.card := by omega
  have hdecomp : t = 0 ∨ ∃ i u, t = i ::ₘ u :=
    Multiset.induction_on t (Or.inl rfl) (fun i u _ ↦ Or.inr ⟨i, u, rfl⟩)
  rcases hdecomp with ht0 | ⟨i, u, hu⟩
  · simp [ht0] at htpos
  obtain ⟨j, hj⟩ := hpred i
  let v := j ::ₘ j ::ₘ u
  have hvcard : v.card = m := by
    rw [hu] at ht
    simp only [v, Multiset.card_cons] at ht ⊢
    omega
  have hvsum : (v.map x).sum = 0 := by
    rw [hu] at htv
    simpa only [v, Multiset.map_cons, Multiset.sum_cons, hj, two_nsmul,
      add_assoc, hv] using htv
  have hcount : (∑ a : Fin m, v.count a) = m := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
    exact hvcard
  have hweight : (∑ a : Fin m, v.count a • x a) = ∑ a, x a := by
    rw [hzero, ← hvsum, Finset.sum_multiset_map_count]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    have hc : v.count a = 0 := Multiset.count_eq_zero.mpr (by simpa using ha)
    simp [hc]
  have hbad := hx (fun a ↦ v.count a) hcount hweight j
  simp only [v, Multiset.count_cons_self] at hbad
  omega

/-- Every proper subset of such a family is its unique representation
among all multisets with no more coins. -/
theorem multiset_eq_subset_of_card_le_of_valid_zero_sum_predecessors
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin m → G) (hx : ValidTuple x)
    (hzero : (∑ i, x i) = 0) (hpred : ∀ i, ∃ j, x i = 2 • x j)
    (S : Finset (Fin m)) (hS : S.card < m)
    (p : Multiset (Fin m)) (hp : p.card ≤ S.card)
    (hv : (p.map x).sum = ∑ i ∈ S, x i) : p = S.val := by
  classical
  let t := p + Sᶜ.val
  have hc : t.card = p.card + (m - S.card) := by
    simp only [t, Multiset.card_add]
    change p.card + Sᶜ.card = p.card + (m - S.card)
    rw [Finset.card_compl, Fintype.card_fin]
  have htpos : 0 < t.card := by omega
  have htv : (t.map x).sum = 0 := by
    simp only [t, Multiset.map_add, Multiset.sum_add, hv]
    change (∑ i ∈ S, x i) + (∑ i ∈ Sᶜ, x i) = 0
    rw [Finset.sum_add_sum_compl, hzero]
  have hge := length_le_card_of_zero_sum_multiset_of_doubling_predecessors
    x hx hzero hpred t htpos htv
  have ht : t.card = m := by omega
  have hcount : (∑ a : Fin m, t.count a) = m := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
    exact ht
  have hweight : (∑ a : Fin m, t.count a • x a) = ∑ a, x a := by
    rw [hzero, ← htv, Finset.sum_multiset_map_count]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    have hz : t.count a = 0 := Multiset.count_eq_zero.mpr (by simpa using ha)
    simp [hz]
  have hall := hx (fun a ↦ t.count a) hcount hweight
  apply Multiset.ext.mpr
  intro a
  have ha := hall a
  by_cases haS : a ∈ S
  · have hone : S.val.count a = 1 := Multiset.count_eq_one_of_mem S.nodup haS
    have hnone : Sᶜ.val.count a = 0 := Multiset.count_eq_zero.mpr (by simpa using haS)
    simpa only [t, Multiset.count_add, hnone, add_zero, hone] using ha
  · have hnone : S.val.count a = 0 := Multiset.count_eq_zero.mpr haS
    have hmem : a ∈ Sᶜ := Finset.mem_compl.mpr haS
    have hone : Sᶜ.val.count a = 1 := Multiset.count_eq_one_of_mem Sᶜ.nodup hmem
    simp only [t, Multiset.count_add, hone] at ha
    rw [hnone]
    omega

/-- Proper subset sums of a valid predecessor-closed zero-sum family
are distinct, even when the subsets have different sizes. -/
theorem proper_subset_sum_injective_of_valid_zero_sum_predecessors
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin m → G) (hx : ValidTuple x)
    (hzero : (∑ i, x i) = 0) (hpred : ∀ i, ∃ j, x i = 2 • x j)
    (S T : Finset (Fin m)) (hS : S.card < m) (hT : T.card < m)
    (hvalue : (∑ i ∈ S, x i) = ∑ i ∈ T, x i) : S = T := by
  rcases le_total S.card T.card with h | h
  · exact Finset.val_injective
      (multiset_eq_subset_of_card_le_of_valid_zero_sum_predecessors
        x hx hzero hpred T hT S.val h hvalue)
  · exact (Finset.val_injective
      (multiset_eq_subset_of_card_le_of_valid_zero_sum_predecessors
        x hx hzero hpred S hS T.val h hvalue.symm)).symm

/-- The small-subset sumset has its exact binomial cardinality. -/
theorem card_small_subset_sums_of_valid_zero_sum_predecessors
    {m k : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : Fin m → G) (hx : ValidTuple x)
    (hzero : (∑ i, x i) = 0) (hpred : ∀ i, ∃ j, x i = 2 • x j)
    (hkm : k ≤ m) :
    (((Finset.range k).biUnion (fun r ↦
      (Finset.univ : Finset (Fin m)).powersetCard r)).image
      (fun S ↦ ∑ i ∈ S, x i)).card = ∑ r ∈ Finset.range k, m.choose r := by
  classical
  let K := (Finset.range k).biUnion (fun r ↦
    (Finset.univ : Finset (Fin m)).powersetCard r)
  have hsmall (S : Finset (Fin m)) (hS : S ∈ K) : S.card < m := by
    obtain ⟨r, hr, hSr⟩ := Finset.mem_biUnion.mp hS
    have hcard := (Finset.mem_powersetCard.mp hSr).2
    have hrlt := Finset.mem_range.mp hr
    omega
  have hinj : Set.InjOn (fun S : Finset (Fin m) ↦ ∑ i ∈ S, x i) K := by
    intro S hS T hT hvalue
    exact proper_subset_sum_injective_of_valid_zero_sum_predecessors
      x hx hzero hpred S T (hsmall S hS) (hsmall T hT) hvalue
  change (K.image _).card = _
  rw [Finset.card_image_iff.mpr hinj]
  dsimp [K]
  rw [Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i _ j _ hij
    exact (Finset.univ : Finset (Fin m)).pairwise_disjoint_powersetCard hij

/-- The holes of the shortened cycle cover are exactly its negated
small-subset sums, including zero. This is an equivalence, not only an
upper bound on possible holes. -/
theorem mersenne_short_cover_iff_not_sparse_sum
    {m k : ℕ} [NeZero (2 ^ m - 1)]
    {G : Type*} [AddCommGroup G]
    (hk : 0 < k) (hkm : k < m)
    (τ : ZMod (2 ^ m - 1) →+ G)
    (x : Fin m → G) (hx : ValidTuple x)
    (hpowers : ∀ i, x i = τ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    (z : ZMod (2 ^ m - 1)) :
    (∃ s : Multiset (Fin m), s.card = m - k ∧ (s.map x).sum = -τ z) ↔
    ¬ ∃ S : Finset (Fin m), S.card < k ∧ (∑ i ∈ S, x i) = τ z := by
  classical
  have hzero : (∑ i, x i) = 0 := by
    simp only [hpowers, ← map_sum]
    rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self, map_zero]
  have hpred (i : Fin m) : ∃ j, x i = 2 • x j := by
    obtain ⟨j, hj⟩ := mersenne_power_doubling_predecessor (by omega) i
    exact ⟨j, by simpa only [hpowers, map_nsmul] using congrArg τ hj⟩
  constructor
  · rintro ⟨s, hs, hv⟩ ⟨S, hS, hSv⟩
    have hcard : (s + S.val).card = m - k + S.card := by simp [hs]
    have hpos : 0 < (s + S.val).card := by omega
    have hsum : ((s + S.val).map x).sum = 0 := by
      simp only [Multiset.map_add, Multiset.sum_add, hv]
      change -τ z + (∑ i ∈ S, x i) = 0
      rw [hSv, neg_add_cancel]
    have hge := length_le_card_of_zero_sum_multiset_of_doubling_predecessors
      x hx hzero hpred (s + S.val) hpos hsum
    omega
  · intro hnot
    rcases mersenne_short_cover_or_sparse_sum hk hkm z with ⟨s, hs, hv⟩ | ⟨S, hS, hv⟩
    · refine ⟨s, hs, ?_⟩
      simp only [hpowers]
      simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def, map_neg]
        using congrArg τ hv
    · apply False.elim
      apply hnot
      refine ⟨S, hS, ?_⟩
      simp only [hpowers, ← map_sum, hv]

/-- Every possible outside surplus target has a unique small cycle
support. Thus distinct targets consume distinct elements of the binomial
sumset counted above. -/
theorem outside_surplus_unique_sparse_target_of_valid_mersenne_cycle
    {m n k : ℕ} [NeZero (2 ^ m - 1)]
    {G : Type*} [AddCommGroup G]
    (hk : 0 < k) (hkm : k < m)
    (τ : ZMod (2 ^ m - 1) →+ G)
    (g : Fin (m + n) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m,
      g (Fin.castAdd n i) = τ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    (c : Fin n → ℤ) (hc : ∀ j, -1 ≤ c j) (hsum : (∑ j, c j) = k)
    (z : ZMod (2 ^ m - 1))
    (hvalue : (∑ j, c j • g (Fin.natAdd m j)) = τ z) :
    ∃! S : Finset (Fin m), S.card < k ∧
      τ z = ∑ i ∈ S, g (Fin.castAdd n i) := by
  classical
  obtain ⟨S, hS, hSv⟩ := outside_surplus_sparse_target_of_valid_mersenne_cycle
    hk hkm τ g hg hpref c hc hsum z hvalue
  let x : Fin m → G := fun i ↦ g (Fin.castAdd n i)
  have hx : ValidTuple x :=
    validTuple_embedding ⟨Fin.castAdd n, Fin.castAdd_injective m n⟩ g hg
  have hzero : (∑ i, x i) = 0 := by
    simp only [x, hpref, ← map_sum]
    rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self, map_zero]
  have hpred (i : Fin m) : ∃ j, x i = 2 • x j := by
    obtain ⟨j, hj⟩ := mersenne_power_doubling_predecessor (by omega) i
    exact ⟨j, by simpa only [x, hpref, map_nsmul] using congrArg τ hj⟩
  refine ⟨S, ⟨hS, hSv⟩, ?_⟩
  intro T hT
  exact proper_subset_sum_injective_of_valid_zero_sum_predecessors
    x hx hzero hpred T S (by omega) (by omega) (hT.2.symm.trans hSv)

end MinModulus
