import research.HalfDegreeCoinGrowth

set_option autoImplicit false

/-! The generic odd-stratum growth problem as an inequality for repeated sums. -/
namespace MinModulus.Research
open Finset

/-- Degree-k coin sums admitting a repeated coordinate. -/
noncomputable def repeatedCoinCover {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k : ℕ) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (fun x ↦ ∃ s : Multiset (Fin n),
    s.card = k ∧ (s.map g).sum = x ∧ ¬ s.Nodup)

/-- A multiset without distinct entries contains two copies of one entry. -/
theorem exists_double_cons_of_not_nodup {α : Type*} [DecidableEq α]
    (s : Multiset α) (h : ¬ s.Nodup) :
    ∃ a t, s = a ::ₘ a ::ₘ t := by
  have hh : ¬ ∀ a, s.count a ≤ 1 := by
    intro hh
    exact h (Multiset.nodup_iff_count_le_one.mpr hh)
  push Not at hh
  obtain ⟨a,ha⟩ := hh
  have ham : a ∈ s := Multiset.count_pos.mp (by omega)
  have hae : a ∈ s.erase a := by
    apply Multiset.count_pos.mp
    rw [Multiset.count_erase_self]
    omega
  refine ⟨a,(s.erase a).erase a,?_⟩
  rw [Multiset.cons_erase hae,Multiset.cons_erase ham]

/-- Repeated degree-(k+2) sums are precisely the translates of C_k by doubled entries. -/
theorem repeatedCoinCover_eq_doubled_translates {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    repeatedCoinCover g (k+2) = Finset.univ.biUnion
      (fun i ↦ (actualFibreCoinCover g k).image (fun x ↦ 2 • g i+x)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s,hc,hs,hn⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨i,t,rfl⟩ := exists_double_cons_of_not_nodup s hn
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨(t.map g).sum,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,by simpa using hc,rfl⟩
    · simpa only [Multiset.map_cons,Multiset.sum_cons,two_nsmul,add_assoc] using hs
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hi
    obtain ⟨t,hc,hs⟩ := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,i ::ₘ i ::ₘ t,by simp [hc],?_,?_⟩
    · simpa only [Multiset.map_cons,Multiset.sum_cons,hs,two_nsmul,add_assoc] using hyx
    · simp

/-- Every coin sum is either squarefree or repeated. -/
theorem coinCover_eq_squarefree_union_repeated {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    actualFibreCoinCover g k = subsetCoinSums g Finset.univ k ∪ repeatedCoinCover g k := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
    by_cases hn : s.Nodup
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨s,hn⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hc⟩,hs⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,hc,hs,hn⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hs | hr
    · exact subsetCoinSums_subset_coinCover g Finset.univ hs
    · obtain ⟨s,hc,hs,_⟩ := (Finset.mem_filter.mp hr).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,hc,hs⟩

/-- Validity separates squarefree and repeated representations at every degree. -/
theorem squarefree_disjoint_repeatedCoinCover {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    Disjoint (subsetCoinSums g Finset.univ k) (repeatedCoinCover g k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hr
  obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
  obtain ⟨s,hc,hs,hn⟩ := (Finset.mem_filter.mp hr).2
  have he := multiset_eq_finset_of_validTuple_card_sum g hg S s
    (hc.trans (Finset.mem_powersetCard.mp hS).2.symm) (hs.trans hSx.symm)
  exact hn (he ▸ S.nodup)

/-- Exact binomial/repeated decomposition of the coin-cover cardinality. -/
theorem coinCover_card_eq_choose_add_repeated {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    (actualFibreCoinCover g k).card = n.choose k + (repeatedCoinCover g k).card := by
  rw [coinCover_eq_squarefree_union_repeated g,
    Finset.card_union_of_disjoint (squarefree_disjoint_repeatedCoinCover g hg),
    subsetCoinSums_card g hg]
  simp

/-- The desired binomial increment is exactly a comparison with repeated sums. -/
theorem coin_growth_iff_repeated_growth {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    ((actualFibreCoinCover g (k+1)).card+n.choose (k+2) ≤
      (actualFibreCoinCover g (k+2)).card) ↔
    (actualFibreCoinCover g (k+1)).card ≤ (repeatedCoinCover g (k+2)).card := by
  rw [coinCover_card_eq_choose_add_repeated g hg (k := k+2)]
  omega

/-- The single-coin cover contains exactly the distinct entries. -/
theorem one_coin_card_eq {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    (actualFibreCoinCover g 1).card = n := by
  classical
  have he : actualFibreCoinCover g 1 = Finset.univ.image g := by
    ext x
    constructor
    · intro hx
      obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨i,rfl⟩ := Multiset.card_eq_one.mp hc
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa using hs⟩
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,{i},by simp,by simp⟩
  rw [he,Finset.card_image_of_injective _ (validTuple_injective g hg)]
  simp

/-- Exact pair counting, using only the shared Sidon interface on both revisions. -/
theorem two_coin_card_eq_of_odd {n N : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) :
    (actualFibreCoinCover g 2).card = (n+1).choose 2 := by
  classical
  let value : Sym2 (Fin n) → ZMod N := fun p ↦ (p.toMultiset.map g).sum
  have hi : Function.Injective value := by
    intro p q
    induction p, q using Sym2.inductionOn₂ with
    | hf a b c d =>
      intro he
      have heq : g a+g b=g c+g d := by simpa [value,Sym2.toMultiset] using he
      apply Sym2.eq_iff.mpr
      rcases pair_sum_eq_or_diagonal_of_validTuple g hg a b c d heq with h | ⟨hab,hcd⟩
      · exact h
      · subst b; subst d
        have hac : a=c := by
          apply validTuple_injective g hg
          apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
          simpa only [Nat.cast_ofNat,two_mul] using heq
        exact Or.inl ⟨hac,hac⟩
  have he : actualFibreCoinCover g 2=Finset.univ.image value := by
    ext x
    constructor
    · intro hx
      obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨a,b,rfl⟩ := Multiset.card_eq_two.mp hc
      exact Finset.mem_image.mpr ⟨s(a,b),Finset.mem_univ _,by simpa [value,Sym2.toMultiset] using hs⟩
    · intro hx
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.toMultiset,Sym2.card_toMultiset p,rfl⟩
  rw [he,Finset.card_image_of_injective _ hi,← Finset.sym2_univ,Finset.card_sym2]
  simp

/-- The growth steps into degrees two and three already hold uniformly. -/
theorem coin_growth_through_three {n N : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 2) :
    (actualFibreCoinCover g k).card+n.choose (k+1) ≤
      (actualFibreCoinCover g (k+1)).card := by
  have hc : k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl
  · rw [one_coin_card_eq g hg,two_coin_card_eq_of_odd hN g hg]
    have h := Nat.choose_succ_succ n 1
    norm_num only [Nat.choose_one_right,Nat.succ_eq_add_one,Nat.reduceAdd] at h ⊢
    omega
  · rw [two_coin_card_eq_of_odd hN g hg]
    simpa [add_comm] using choose_three_add_choose_two_le_three_coin_card hN g hg

/-- The only remaining growth degrees are d>=4 in the half-degree range. -/
def HigherRepeatedCoinGrowth {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) : Prop :=
  ∀ k : ℕ, 2 ≤ k → 2*(k+2) ≤ n+1 →
    (actualFibreCoinCover g (k+1)).card ≤ (repeatedCoinCover g (k+2)).card

/-- The remaining hypothesis can be stated entirely with doubled-coordinate translates. -/
theorem higherRepeatedCoinGrowth_iff_doubled_translates {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    HigherRepeatedCoinGrowth g ↔ ∀ k : ℕ, 2 ≤ k → 2*(k+2) ≤ n+1 →
      (actualFibreCoinCover g (k+1)).card ≤
        (Finset.univ.biUnion (fun i ↦
          (actualFibreCoinCover g k).image (fun x ↦ 2 • g i+x))).card := by
  simp only [HigherRepeatedCoinGrowth,repeatedCoinCover_eq_doubled_translates]

/-- An exact generic reduction, with the first two increments discharged. -/
theorem halfDegreeCoinGrowth_iff_higherRepeatedCoinGrowth {n N : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) :
    HalfDegreeCoinGrowth g ↔ HigherRepeatedCoinGrowth g := by
  constructor
  · intro h k hk hhalf
    exact (coin_growth_iff_repeated_growth g hg).mp (h (k+1) (by omega) hhalf)
  · intro h k hk hhalf
    by_cases hsmall : k ≤ 2
    · exact coin_growth_through_three hN g hg k hk hsmall
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (coin_growth_iff_repeated_growth g hg).mpr (h j (by omega) hhalf)

/-- Proving the remaining uniform repeated-sum inequality would settle all G2. -/
theorem oddStratumLowerBound_of_higherRepeatedCoinGrowth
    (hGrowth : ∀ {n N : ℕ} [NeZero N], Odd N →
      ∀ g : Fin n → ZMod N, ValidTuple g → HigherRepeatedCoinGrowth g) :
    OddStratumLowerBound := by
  apply oddStratumLowerBound_of_halfDegreeCoinGrowth
  intro n N _ hN g hg
  exact (halfDegreeCoinGrowth_iff_higherRepeatedCoinGrowth hN g hg).mpr (hGrowth hN g hg)

/-- Every odd counterexample forces a strict failure in a degree at least four. -/
theorem exists_doubled_growth_failure_of_odd_counterexample
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1) :
    ∃ k : ℕ, 2 ≤ k ∧ 2*(k+2) ≤ n+1 ∧
      (Finset.univ.biUnion (fun i ↦
        (actualFibreCoinCover g k).image (fun x ↦ 2 • g i+x))).card <
        (actualFibreCoinCover g (k+1)).card := by
  have h : ¬ HigherRepeatedCoinGrowth g := by
    intro h
    have hh := (halfDegreeCoinGrowth_iff_higherRepeatedCoinGrowth hN g hg).mpr h
    have hb := odd_modulus_lower_bound_of_halfDegreeCoinGrowth hn hN g hg hh
    omega
  rw [higherRepeatedCoinGrowth_iff_doubled_translates] at h
  push Not at h
  exact h

end MinModulus.Research
