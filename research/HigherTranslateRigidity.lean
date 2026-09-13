import research.RepeatedCoinGrowth

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Coordinates whose translate lies in a specified coin degree. -/
noncomputable def coinTranslateHits {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (d : ℕ) (t : ZMod N) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ g i+t ∈ actualFibreCoinCover g d)

/-- A squarefree hit either contains its translated coordinate, or confines
every other hit to the displayed support together with that coordinate. -/
theorem coin_translate_hit_mem_insert_of_squarefree_hit
    {n N d : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (j : Fin n) (S : Finset (Fin n)) (hS : S.card=d)
    (hj : j ∉ S) (he : g j+t=∑ i ∈ S, g i)
    (a : Fin n) (ha : g a+t ∈ actualFibreCoinCover g d) : a ∈ insert j S := by
  classical
  by_contra hn
  have haj : a ≠ j := by intro hh; subst a; simp at hn
  have haS : a ∉ S := fun hh ↦ hn (Finset.mem_insert_of_mem hh)
  obtain ⟨u,huc,huv⟩ := (Finset.mem_filter.mp ha).2
  have hsame : j ::ₘ u=(insert a S).val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg (insert a S) (j ::ₘ u)
    · simp only [Multiset.card_cons,Finset.card_insert_of_notMem haS]
      omega
    · simp only [Multiset.map_cons,Multiset.sum_cons,huv,Finset.sum_insert haS]
      rw [← he]
      abel
  have hmem : j ∈ insert a S := by
    change j ∈ (insert a S).val
    rw [← hsame]
    simp
  exact (Finset.mem_insert.mp hmem).elim (fun hh ↦ haj hh.symm) hj

/-- An outside shift cannot cancel a coordinate in a squarefree hit. -/
theorem outside_coin_translate_anchor_not_mem
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (t : ZMod N)
    (ht : t ∉ actualFibreCoinCover g k) (j : Fin n) (S : Finset (Fin n))
    (hS : S.card=k+1) (he : g j+t=∑ i ∈ S, g i) : j ∉ S := by
  classical
  intro hj
  have hsum : t=∑ i ∈ S.erase j, g i := by
    have hh := Finset.add_sum_erase S g hj
    rw [← he] at hh
    exact (add_left_cancel hh).symm
  apply ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(S.erase j).val,?_,?_⟩
  · change (S.erase j).card=k
    rw [Finset.card_erase_of_mem hj,hS]
    omega
  · exact hsum.symm

/-- At every degree, a squarefree hit of an outside translate permits
at most d+1 translated coordinates in the degree-d cover. -/
theorem outside_coin_translate_hits_le_of_squarefree_hit
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : t ∉ actualFibreCoinCover g k)
    (j : Fin n) (S : Finset (Fin n)) (hS : S.card=k+1)
    (he : g j+t=∑ i ∈ S, g i) : (coinTranslateHits g (k+1) t).card ≤ k+2 := by
  classical
  have hj := outside_coin_translate_anchor_not_mem g t ht j S hS he
  have hsub : coinTranslateHits g (k+1) t ⊆ insert j S := by
    intro a ha
    exact coin_translate_hit_mem_insert_of_squarefree_hit g hg t j S hS hj he a
      (Finset.mem_filter.mp ha).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hj,hS] at hc
  exact hc

/-- More than d+1 hits force every hit to be repeated, uniformly in d. -/
theorem outside_coin_translate_hit_repeated_of_many_hits
    {n N k : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (t : ZMod N) (ht : t ∉ actualFibreCoinCover g k)
    (hmany : k+3 ≤ (coinTranslateHits g (k+1) t).card)
    (a : Fin n) (ha : g a+t ∈ actualFibreCoinCover g (k+1)) :
    g a+t ∈ repeatedCoinCover g (k+1) := by
  classical
  obtain ⟨u,huc,huv⟩ := (Finset.mem_filter.mp ha).2
  have hnot : ¬ u.Nodup := by
    intro hu
    have hh := outside_coin_translate_hits_le_of_squarefree_hit g hg t ht a
      (⟨u,hu⟩ : Finset (Fin n)) huc huv.symm
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,huc,huv,hnot⟩

/-- A complete outside translate permits an injective translation from
every positive coin degree into the repeated cover k degrees higher. -/
theorem repeated_coin_growth_of_full_higher_translate
    {n N k r : ℕ} [NeZero N] (hn : k+3 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (ht : t ∉ actualFibreCoinCover g k)
    (hcover : ∀ i, g i+t ∈ actualFibreCoinCover g (k+1)) :
    (actualFibreCoinCover g (r+1)).card ≤ (repeatedCoinCover g (r+k+1)).card := by
  classical
  have hhits : coinTranslateHits g (k+1) t=Finset.univ := by
    ext i
    simp [coinTranslateHits,hcover]
  have hrep (i : Fin n) : g i+t ∈ repeatedCoinCover g (k+1) :=
    outside_coin_translate_hit_repeated_of_many_hits g hg t ht
      (by simpa [hhits] using hn) i (hcover i)
  have hsub : (actualFibreCoinCover g (r+1)).image (fun x ↦ x+t) ⊆
      repeatedCoinCover g (r+k+1) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s,hsc,hsv⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨i,hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < s.card)
    obtain ⟨v,rfl⟩ := Multiset.exists_cons_of_mem hi
    obtain ⟨u,huc,huv,hu⟩ := (Finset.mem_filter.mp (hrep i)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,u+v,?_,?_,?_⟩
    · simp only [Multiset.card_cons] at hsc
      simp only [Multiset.card_add,huc]
      omega
    · simp only [Multiset.map_add,Multiset.sum_add,huv]
      simp only [Multiset.map_cons,Multiset.sum_cons] at hsv
      rw [← hsv]
      abel
    · intro huv
      exact hu (Multiset.nodup_add.mp huv).1
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ (fun _ _ hh ↦ add_right_cancel hh)] at hc

end MinModulus.Research
