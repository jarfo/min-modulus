import research.AnchoredCubeCoinFiltration

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A partial row of Pascal's triangle is the sum of the two adjacent
partial rows below it, including the boundary terms. -/
theorem partial_choose_succ_eq_adjacent_rows (m k : ℕ) :
    (∑ j ∈ Finset.range (k+1), (m+1).choose j) =
      (∑ j ∈ Finset.range (k+1), m.choose j)+
      (∑ j ∈ Finset.range k, m.choose j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn := Finset.sum_range_succ (fun j ↦ (m+1).choose j) (k+1)
    have hm := Finset.sum_range_succ (fun j ↦ m.choose j) (k+1)
    have hm0 := Finset.sum_range_succ (fun j ↦ m.choose j) k
    have hp := Nat.choose_succ_succ m k
    simp only [Nat.succ_eq_add_one] at *
    omega

/-- The repeated-cover target is exactly an outside-cube target at any
zero anchor. Neither side is asserted to hold here. -/
theorem repeated_bound_iff_outside_anchored_cube_bound
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (k : ℕ) :
    ((∑ j ∈ Finset.range k, n.choose j) ≤ (repeatedCoinCover g k).card+1) ↔
      ((∑ j ∈ Finset.range k, (n-1).choose j) ≤
        (actualFibreCoinCover g k \ zeroAnchorSubsetCube g q).card+1) := by
  have hn : n-1+1=n := by have := q.isLt; omega
  have hp := partial_choose_succ_eq_adjacent_rows (n-1) k
  rw [hn,Finset.sum_range_succ] at hp
  have hc := coinCover_card_eq_choose_add_repeated (k := k) g hg
  have ho := coinCover_card_eq_anchored_partial_choose_add_outside g hg q hq k
  omega

/-- Translating the coordinates translates every repeated degree-k value
by the same amount, and therefore preserves the cardinality. -/
theorem repeatedCoinCover_sub_const_card
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N) (k : ℕ) :
    (repeatedCoinCover (fun i ↦ g i-b) k).card=(repeatedCoinCover g k).card := by
  classical
  have hshift (t : Multiset (Fin n)) :
      (t.map (fun i ↦ g i-b)).sum=(t.map g).sum-t.card • b := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons i t ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,ih,
        add_nsmul,one_nsmul]
      abel
  have he : repeatedCoinCover (fun i ↦ g i-b) k =
      (repeatedCoinCover g k).image (fun x ↦ x-k • b) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t,hc,hs,hn⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_image.mpr ⟨(t.map g).sum,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,hc,rfl,hn⟩,?_⟩
      simpa only [hshift,hc] using hs
    · intro hx
      obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
      obtain ⟨t,hc,hs,hn⟩ := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,hc,by simpa [hshift,hc,hs] using hyx,hn⟩
  rw [he,Finset.card_image_of_injective _ (fun x y h ↦ add_right_cancel (by simpa only [sub_eq_add_neg] using h))]

/-- The same outside-cube target is equivalent to the original repeated
bound at every anchor, with no normalization hypothesis on the input. -/
theorem repeated_bound_iff_outside_any_anchor_bound
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (k : ℕ) :
    ((∑ j ∈ Finset.range k, n.choose j) ≤ (repeatedCoinCover g k).card+1) ↔
      ((∑ j ∈ Finset.range k, (n-1).choose j) ≤
        (actualFibreCoinCover (fun i ↦ g i-g q) k \
          zeroAnchorSubsetCube (fun i ↦ g i-g q) q).card+1) := by
  have h := repeated_bound_iff_outside_anchored_cube_bound
    (fun i ↦ g i-g q) (validTuple_sub_const g hg (g q)) q (by simp) k
  rwa [repeatedCoinCover_sub_const_card] at h

end MinModulus.Research
