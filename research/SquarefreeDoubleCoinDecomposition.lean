import research.RepeatedCoinGrowth

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Every multiset has a squarefree remainder after removing pairs. -/
theorem exists_squarefree_double_decomposition {α : Type*} [DecidableEq α]
    (s : Multiset α) : ∃ S : Finset α, ∃ t : Multiset α, s=S.val+(t+t) := by
  suffices ∀ k : ℕ, ∀ s : Multiset α, s.card=k →
      ∃ S : Finset α, ∃ t : Multiset α, s=S.val+(t+t) by
    exact this s.card s rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hc
    by_cases hn : s.Nodup
    · exact ⟨⟨s,hn⟩,0,by simp⟩
    · obtain ⟨a,t,rfl⟩ := exists_double_cons_of_not_nodup s hn
      have ht : t.card < k := by simp only [Multiset.card_cons] at hc; omega
      obtain ⟨S,u,hu⟩ := ih t.card ht t rfl
      refine ⟨S,a ::ₘ u,?_⟩
      simp only [hu,Multiset.cons_add,Multiset.add_cons]

/-- The squarefree remainder and the halved multiset are unique. -/
theorem squarefree_double_decomposition_unique {α : Type*} [DecidableEq α]
    (S T : Finset α) (u v : Multiset α)
    (h : S.val+(u+u)=T.val+(v+v)) : S=T ∧ u=v := by
  have hc (a : α) : S.val.count a=T.val.count a ∧ u.count a=v.count a := by
    have he := congrArg (Multiset.count a) h
    simp only [Multiset.count_add] at he
    have hs := Multiset.nodup_iff_count_le_one.mp S.nodup a
    have ht := Multiset.nodup_iff_count_le_one.mp T.nodup a
    omega
  exact ⟨Finset.val_injective (Multiset.ext.mpr (fun a ↦ (hc a).1)),
    Multiset.ext.mpr (fun a ↦ (hc a).2)⟩

/-- An arbitrary coin value is a squarefree sum plus twice a smaller coin value. -/
theorem mem_coinCover_iff_squarefree_double {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (x : ZMod N) :
    x ∈ actualFibreCoinCover g k ↔
      ∃ (S : Finset (Fin n)) (r : ℕ) (y : ZMod N),
        S.card+2*r=k ∧ y ∈ actualFibreCoinCover g r ∧
        (∑ i ∈ S, g i)+2 • y=x := by
  classical
  constructor
  · intro hx
    obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨S,t,rfl⟩ := exists_squarefree_double_decomposition s
    refine ⟨S,t.card,(t.map g).sum,?_,?_,?_⟩
    · simpa only [Multiset.card_add,← Finset.card_def,two_mul] using hc
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,rfl,rfl⟩
    · simpa only [Multiset.map_add,Multiset.sum_add,← Finset.sum_eq_multiset_sum,
        two_nsmul] using hs
  · rintro ⟨S,r,y,hc,hy,he⟩
    obtain ⟨t,ht,hs⟩ := (Finset.mem_filter.mp hy).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.val+(t+t),?_,?_⟩
    · simpa only [Multiset.card_add,← Finset.card_def,ht,two_mul] using hc
    · simpa only [Multiset.map_add,Multiset.sum_add,← Finset.sum_eq_multiset_sum,
        hs,two_nsmul] using he

/-- Repeated coin values are exactly the squarefree-plus-double layers with positive
halved degree. No validity assumption is needed. -/
theorem mem_repeatedCoinCover_iff_squarefree_double {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (x : ZMod N) :
    x ∈ repeatedCoinCover g k ↔
      ∃ (S : Finset (Fin n)) (r : ℕ) (y : ZMod N),
        1 ≤ r ∧ S.card+2*r=k ∧ y ∈ actualFibreCoinCover g r ∧
        (∑ i ∈ S, g i)+2 • y=x := by
  classical
  constructor
  · intro hx
    obtain ⟨s,hc,hs,hn⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨S,t,rfl⟩ := exists_squarefree_double_decomposition s
    have ht : 1 ≤ t.card := by
      by_contra h
      have hz : t=0 := Multiset.card_eq_zero.mp (by omega)
      exact hn (by simpa only [hz,zero_add,add_zero] using S.nodup)
    refine ⟨S,t.card,(t.map g).sum,ht,?_,?_,?_⟩
    · simpa only [Multiset.card_add,← Finset.card_def,two_mul] using hc
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,rfl,rfl⟩
    · simpa only [Multiset.map_add,Multiset.sum_add,← Finset.sum_eq_multiset_sum,
        two_nsmul] using hs
  · rintro ⟨S,r,y,hr,hc,hy,he⟩
    obtain ⟨t,ht,hs⟩ := (Finset.mem_filter.mp hy).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.val+(t+t),?_,?_,?_⟩
    · simpa only [Multiset.card_add,← Finset.card_def,ht,two_mul] using hc
    · simpa only [Multiset.map_add,Multiset.sum_add,← Finset.sum_eq_multiset_sum,
        hs,two_nsmul] using he
    · intro hn
      have htt := (Multiset.nodup_add.mp hn).2.1
      have hz : t=0 := disjoint_self.mp (Multiset.nodup_add.mp htt).2.2
      simp only [hz,Multiset.card_zero] at ht
      omega

/-- The full coin cover is a finite union over every squarefree remainder and
every halved degree, including all multiplicity patterns recursively. -/
theorem coinCover_eq_squarefree_doubled_union {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    actualFibreCoinCover g k = (Finset.range (k/2+1)).biUnion (fun r ↦
      ((Finset.univ : Finset (Fin n)).powersetCard (k-2*r)).biUnion (fun S ↦
        (actualFibreCoinCover g r).image (fun y ↦ (∑ i ∈ S, g i)+2 • y))) := by
  classical
  ext x
  rw [mem_coinCover_iff_squarefree_double]
  constructor
  · rintro ⟨S,r,y,hc,hy,he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r,Finset.mem_range.mpr (by omega),Finset.mem_biUnion.mpr ?_⟩
    refine ⟨S,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by omega⟩,?_⟩
    exact Finset.mem_image.mpr ⟨y,hy,he⟩
  · intro hx
    obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨S,hS,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hrc := Finset.mem_range.mp hr
    have hSc := (Finset.mem_powersetCard.mp hS).2
    exact ⟨S,r,y,by omega,hy,he⟩

/-- Omitting the zero halved degree gives exactly the repeated coin cover. -/
theorem repeatedCoinCover_eq_squarefree_doubled_union {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) :
    repeatedCoinCover g k = (Finset.Icc 1 (k/2)).biUnion (fun r ↦
      ((Finset.univ : Finset (Fin n)).powersetCard (k-2*r)).biUnion (fun S ↦
        (actualFibreCoinCover g r).image (fun y ↦ (∑ i ∈ S, g i)+2 • y))) := by
  classical
  ext x
  rw [mem_repeatedCoinCover_iff_squarefree_double]
  constructor
  · rintro ⟨S,r,y,hr,hc,hy,he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r,Finset.mem_Icc.mpr ⟨hr,by omega⟩,Finset.mem_biUnion.mpr ?_⟩
    refine ⟨S,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by omega⟩,?_⟩
    exact Finset.mem_image.mpr ⟨y,hy,he⟩
  · intro hx
    obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨S,hS,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hrc := Finset.mem_Icc.mp hr
    have hSc := (Finset.mem_powersetCard.mp hS).2
    exact ⟨S,r,y,hrc.1,by omega,hy,he⟩

/-- At odd modulus each fixed remainder layer has the full smaller coin-cover
cardinality. This does not assert disjointness between different layers. -/
theorem squarefree_doubled_coin_layer_card {n N r : ℕ} [NeZero N]
    (hN : Odd N) (g : Fin n → ZMod N) (S : Finset (Fin n)) :
    ((actualFibreCoinCover g r).image (fun y ↦ (∑ i ∈ S, g i)+2 • y)).card=
      (actualFibreCoinCover g r).card := by
  classical
  apply Finset.card_image_of_injective
  intro x y h
  have hh : 2 • x=2 • y := add_left_cancel h
  apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
  simpa only [Nat.cast_ofNat,two_nsmul,two_mul] using hh

end MinModulus.Research
