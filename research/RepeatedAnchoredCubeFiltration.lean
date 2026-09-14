import research.AnchoredCubeCoinFiltration

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A cube value has a repeated representation exactly two degrees after
its subset size: the first spare zero-anchor coin is still squarefree. -/
theorem anchored_subset_sum_mem_repeatedCoinCover_iff
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (S : Finset (Fin n)) (hqS : q ∉ S) (k : ℕ) :
    (∑ i ∈ S, g i) ∈ repeatedCoinCover g k ↔ S.card+2 ≤ k := by
  classical
  constructor
  · intro hx
    obtain ⟨t,hc,hs,hn⟩ := (Finset.mem_filter.mp hx).2
    by_contra hnot
    by_cases hle : t.card ≤ S.card
    · have he := multiset_eq_finset_of_card_le_of_zero_anchor g hg q hq S hqS t hle hs
      exact hn (he ▸ S.nodup)
    · have htc : t.card=(insert q S).card := by rw [Finset.card_insert_of_notMem hqS]; omega
      have hts : (t.map g).sum=∑ i ∈ insert q S, g i := by simp [hqS,hq,hs]
      have he := multiset_eq_finset_of_validTuple_card_sum g hg (insert q S) t htc hts
      exact hn (he ▸ (insert q S).nodup)
  · intro hcard
    let t := S.val+Multiset.replicate (k-S.card) q
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,?_,?_,?_⟩
    · simp [t]; omega
    · simp [t,hq]
    · intro hn
      have h := Multiset.nodup_iff_count_le_one.mp hn q
      have hSq : S.val.count q=0 := Multiset.count_eq_zero.mpr hqS
      simp only [t,Multiset.count_add,Multiset.count_replicate_self,hSq,zero_add] at h
      omega

/-- The repeated cover meets the anchored cube in exactly the cube's
coin filtration two degrees earlier. -/
theorem zero_anchor_cube_inter_repeatedCoinCover_card
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (k : ℕ) :
    (zeroAnchorSubsetCube g q ∩ repeatedCoinCover g (k+2)).card =
      ∑ j ∈ Finset.range (k+1), (n-1).choose j := by
  classical
  have he : zeroAnchorSubsetCube g q ∩ repeatedCoinCover g (k+2) =
      zeroAnchorSubsetCube g q ∩ actualFibreCoinCover g k := by
    ext x
    by_cases hx : x ∈ zeroAnchorSubsetCube g q
    · obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
      have hqS : q ∉ S := fun h ↦
        (Finset.mem_erase.mp (Finset.mem_powerset.mp hS h)).1 rfl
      have hmem : (∑ i ∈ S,g i) ∈ zeroAnchorSubsetCube g q :=
        Finset.mem_image.mpr ⟨S,hS,rfl⟩
      simp only [Finset.mem_inter,hmem,true_and,
        anchored_subset_sum_mem_repeatedCoinCover_iff g hg q hq S hqS,
        anchored_subset_sum_mem_coinCover_iff g hg q hq S hqS]
      omega
    · simp [hx]
  rw [he,zero_anchor_cube_inter_coinCover_card g hg q hq]

/-- Duplicating a member of a nonempty anchored subset either leaves the
cube or lands in a strictly smaller subset layer. -/
theorem duplicate_subset_sum_in_cube_card_lt
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (S T : Finset (Fin n)) (hqT : q ∉ T)
    (i : Fin n) (hi : i ∈ S)
    (he : (∑ j ∈ S,g j)+g i=∑ j ∈ T,g j) :
    T.card < S.card := by
  classical
  have hmem : (∑ j ∈ T,g j) ∈ repeatedCoinCover g (S.card+1) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,i ::ₘ S.val,by simp,?_,?_⟩
    · simpa [add_comm] using he
    · simp [hi]
  have hc := (anchored_subset_sum_mem_repeatedCoinCover_iff g hg q hq T hqT _).mp hmem
  omega

end MinModulus.Research
