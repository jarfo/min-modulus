import research.HigherTranslateRigidity

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- The midpoint of a nonempty even squarefree sum cannot lie in the
coin cover of half its degree. -/
theorem squarefree_midpoint_outside_half_coin_cover {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) (t : ZMod N)
    (ht : 2 • t=∑ i ∈ S, g i) : t ∉ actualFibreCoinCover g k := by
  classical
  intro hmem
  obtain ⟨u,hu,hut⟩ := (Finset.mem_filter.mp hmem).2
  have he : u+u=S.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg S _
    · simp [hu,hS,two_mul]
    · simpa only [Multiset.map_add,Multiset.sum_add,hut,two_nsmul] using ht
  have hn : (u+u).Nodup := he.symm ▸ S.nodup
  have hz : u=0 := disjoint_self.mp (Multiset.nodup_add.mp hn).2.2
  simp only [hz,Multiset.card_zero] at hu
  omega

/-- A midpoint of a squarefree 2k-sum has at most 2k+1 coordinate hits
in the degree-(k+1) cover, uniformly in k and n. -/
theorem squarefree_midpoint_coin_hits_le {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) (t : ZMod N)
    (ht : 2 • t=∑ i ∈ S, g i) :
    (coinTranslateHits g (k+1) t).card ≤ 2*k+1 := by
  classical
  have hout := squarefree_midpoint_outside_half_coin_cover hk g hg S hS t ht
  by_contra h
  have hmany : 2*k+2 ≤ (coinTranslateHits g (k+1) t).card := by omega
  let K := coinTranslateHits g (k+1) t \ S
  have hK : 1 < K.card := by
    have hsum := Finset.card_sdiff_add_card_inter (coinTranslateHits g (k+1) t) S
    have hle := Finset.card_le_card (Finset.inter_subset_right :
      coinTranslateHits g (k+1) t ∩ S ⊆ S)
    rw [hS] at hle
    dsimp only [K]
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hK
  have hiH := (Finset.mem_sdiff.mp hi).1
  have hjH := (Finset.mem_sdiff.mp hj).1
  have hiS := (Finset.mem_sdiff.mp hi).2
  have hjS := (Finset.mem_sdiff.mp hj).2
  have hrep := outside_coin_translate_hit_repeated_of_many_hits g hg t hout
    (by omega : k+3 ≤ (coinTranslateHits g (k+1) t).card) i
    (Finset.mem_filter.mp hiH).2
  obtain ⟨u,hu,hut,hun⟩ := (Finset.mem_filter.mp hrep).2
  obtain ⟨v,hv,hvt⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hjH).2).2
  let T := insert i (insert j S)
  have he : u+v=T.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg T _
    · simp [T,hij,hiS,hjS,hu,hv,hS]
      omega
    · simp only [Multiset.map_add,Multiset.sum_add,hut,hvt]
      have hT : (∑ a ∈ T, g a)=g i+g j+∑ a ∈ S, g a := by
        simp [T,hij,hiS,hjS,add_assoc]
      rw [hT,← ht,two_nsmul]
      abel
  have hn : (u+v).Nodup := he.symm ▸ T.nodup
  exact hun (Multiset.nodup_add.mp hn).1

/-- At odd order, every squarefree 2k-sum yields at least n-(2k+1)
anchors outside the doubled degree-(k+1) cover. The displayed values
are repeated sums of degree 2k+2. -/
theorem squarefree_doubled_coin_escape_count {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) :
    n-(2*k+1) ≤ (Finset.univ.filter (fun a : Fin n ↦
      2 • g a+(∑ i ∈ S, g i) ∉
        (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x))).card := by
  classical
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro x y h
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using h
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective hd) (∑ i ∈ S, g i)
  change 2 • t=∑ i ∈ S, g i at ht
  have hmem (a : Fin n) :
      2 • g a+(∑ i ∈ S, g i) ∈
        (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x) ↔
      g a+t ∈ actualFibreCoinCover g (k+1) := by
    have he : 2 • (g a+t)=2 • g a+(∑ i ∈ S, g i) := by rw [nsmul_add,ht]
    rw [← he]
    exact Finset.mem_image.trans ⟨fun ⟨y,hy,he⟩ ↦ hd he ▸ hy,
      fun hy ↦ ⟨g a+t,hy,rfl⟩⟩
  have heq : Finset.univ.filter (fun a : Fin n ↦
      2 • g a+(∑ i ∈ S, g i) ∉
        (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)) =
      Finset.univ \ coinTranslateHits g (k+1) t := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
      coinTranslateHits,hmem]
  rw [heq,Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,Fintype.card_fin]
  have hh := squarefree_midpoint_coin_hits_le hk g hg S hS t ht
  omega

end MinModulus.Research
