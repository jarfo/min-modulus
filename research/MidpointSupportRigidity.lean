import research.HigherMidpointEscapes

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- If two midpoint hits lie outside the squarefree support, they are
the only hits anywhere. -/
theorem midpoint_hits_subset_pair_of_two_outside {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) (t : ZMod N)
    (ht : 2 • t=∑ a ∈ S, g a) (i j : Fin n) (hij : i ≠ j)
    (hiS : i ∉ S) (hjS : j ∉ S)
    (hi : g i+t ∈ actualFibreCoinCover g (k+1))
    (hj : g j+t ∈ actualFibreCoinCover g (k+1)) :
    coinTranslateHits g (k+1) t ⊆ ({i,j} : Finset (Fin n)) := by
  classical
  have hout := squarefree_midpoint_outside_half_coin_cover hk g hg S hS t ht
  obtain ⟨u,hu,hut⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨v,hv,hvt⟩ := (Finset.mem_filter.mp hj).2
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
  obtain ⟨hnu,hnv,huv⟩ := Multiset.nodup_add.mp hn
  let U : Finset (Fin n) := ⟨u,hnu⟩
  let V : Finset (Fin n) := ⟨v,hnv⟩
  have hiU : i ∉ U := outside_coin_translate_anchor_not_mem g t hout i U hu hut.symm
  have hjV : j ∉ V := outside_coin_translate_anchor_not_mem g t hout j V hv hvt.symm
  intro a ha
  have hau := coin_translate_hit_mem_insert_of_squarefree_hit g hg t i U hu hiU hut.symm a
    (Finset.mem_filter.mp ha).2
  have hav := coin_translate_hit_mem_insert_of_squarefree_hit g hg t j V hv hjV hvt.symm a
    (Finset.mem_filter.mp ha).2
  by_contra hnot
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hnot
  have hau' : a ∈ u := (Finset.mem_insert.mp hau).resolve_left hnot.1
  have hav' : a ∈ v := (Finset.mem_insert.mp hav).resolve_left hnot.2
  exact Multiset.disjoint_left.mp huv hau' hav'

/-- At most two midpoint hits can be outside the squarefree support. -/
theorem midpoint_outside_support_hits_le_two {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) (t : ZMod N)
    (ht : 2 • t=∑ a ∈ S, g a) :
    (coinTranslateHits g (k+1) t \ S).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega :
    1 < (coinTranslateHits g (k+1) t \ S).card)
  have hsub := midpoint_hits_subset_pair_of_two_outside hk g hg S hS t ht i j hij
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
  have hle := Finset.card_le_card ((Finset.sdiff_subset :
    coinTranslateHits g (k+1) t \ S ⊆ coinTranslateHits g (k+1) t).trans hsub)
  rw [Finset.card_pair hij] at hle
  omega

/-- At least n-(2k+2) coordinates outside the support escape the
next-degree coin cover under midpoint translation. -/
theorem midpoint_outside_support_escape_count {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) (t : ZMod N)
    (ht : 2 • t=∑ a ∈ S, g a) :
    n-(2*k+2) ≤ (Finset.univ.filter (fun a : Fin n ↦
      a ∉ S ∧ g a+t ∉ actualFibreCoinCover g (k+1))).card := by
  classical
  let H := coinTranslateHits g (k+1) t
  have heq : Finset.univ.filter (fun a : Fin n ↦
      a ∉ S ∧ g a+t ∉ actualFibreCoinCover g (k+1)) =
      (Finset.univ \ S) \ H := by
    ext a
    simp [H,coinTranslateHits]
  have hinter : (Finset.univ \ S) ∩ H=H \ S := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have hsum := Finset.card_sdiff_add_card_inter (Finset.univ \ S) H
  rw [hinter,Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ,Fintype.card_fin,hS] at hsum
  have hcap := midpoint_outside_support_hits_le_two hk g hg S hS t ht
  rw [heq]
  dsimp only [H] at hsum ⊢
  omega

/-- At odd order, at least n-(2k+2) single-repeat values anchored
outside S escape the doubled half-degree cover. -/
theorem squarefree_single_repeat_escape_count {n N k : ℕ} [NeZero N]
    (hk : 1 ≤ k) (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (hS : S.card=2*k) :
    n-(2*k+2) ≤ (Finset.univ.filter (fun a : Fin n ↦
      a ∉ S ∧ 2 • g a+(∑ i ∈ S, g i) ∉
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
      a ∉ S ∧ 2 • g a+(∑ i ∈ S, g i) ∉
        (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)) =
      Finset.univ.filter (fun a : Fin n ↦
        a ∉ S ∧ g a+t ∉ actualFibreCoinCover g (k+1)) := by
    ext a
    simp only [Finset.mem_filter,hmem]
  rw [heq]
  exact midpoint_outside_support_escape_count hk g hg S hS t ht

end MinModulus.Research
