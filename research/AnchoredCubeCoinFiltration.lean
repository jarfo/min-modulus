import research.RepeatedCoinGrowth
import MinModulus.G1OddPrimarySingletonComplement

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- With a zero anchor outside a subset, that subset is its unique
representation using no more coins. -/
theorem multiset_eq_finset_of_card_le_of_zero_anchor
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (q : Fin n) (hq : g q=0)
    (S : Finset (Fin n)) (hqS : q ∉ S) (s : Multiset (Fin n))
    (hc : s.card ≤ S.card) (hs : (s.map g).sum=∑ i ∈ S, g i) :
    s=S.val := by
  classical
  let t := s+Multiset.replicate (S.card-s.card) q
  have htcard : t.card=S.card := by simp [t]; omega
  have htsum : (t.map g).sum=∑ i ∈ S, g i := by simp [t,hq,hs]
  have he := multiset_eq_finset_of_validTuple_card_sum g hg S t htcard htsum
  have hcount := congrArg (fun u : Multiset (Fin n) ↦ u.count q) he
  have hSq : S.val.count q=0 := Multiset.count_eq_zero.mpr hqS
  simp only [t,Multiset.count_add,Multiset.count_replicate_self,hSq] at hcount
  have heq : S.card-s.card=0 := by omega
  simpa [t,heq] using he

/-- Coin degree on an anchored subset sum is exactly its subset size,
with arbitrary additional zero coins allowed. -/
theorem anchored_subset_sum_mem_coinCover_iff
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (S : Finset (Fin n)) (hqS : q ∉ S) (k : ℕ) :
    (∑ i ∈ S, g i) ∈ actualFibreCoinCover g k ↔ S.card ≤ k := by
  classical
  constructor
  · intro hx
    obtain ⟨s,hc,hs⟩ := (Finset.mem_filter.mp hx).2
    by_contra hnot
    have he := multiset_eq_finset_of_card_le_of_zero_anchor g hg q hq S hqS s
      (by omega) hs
    have hec := congrArg Multiset.card he
    change s.card=S.card at hec
    omega
  · intro hcard
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.val+Multiset.replicate (k-S.card) q,?_,?_⟩
    · simp; omega
    · simp [hq]

/-- The subset-sum cube away from an explicitly zero anchor. -/
noncomputable def zeroAnchorSubsetCube {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (q : Fin n) : Finset (ZMod N) :=
  ((Finset.univ.erase q).powerset).image (fun S ↦ ∑ i ∈ S, g i)

/-- Subset sums avoiding a zero anchor are distinct even at different degrees. -/
theorem zero_anchor_subset_sum_injective
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (q : Fin n) (hq : g q=0) :
    Set.InjOn (fun S : Finset (Fin n) ↦ ∑ i ∈ S, g i)
      (Finset.univ.erase q).powerset := by
  classical
  intro S hS T hT he
  have hqS : q ∉ S := fun h ↦ (Finset.mem_erase.mp (Finset.mem_powerset.mp hS h)).1 rfl
  have hqT : q ∉ T := fun h ↦ (Finset.mem_erase.mp (Finset.mem_powerset.mp hT h)).1 rfl
  rcases le_total S.card T.card with hc | hc
  · exact Finset.val_injective (multiset_eq_finset_of_card_le_of_zero_anchor
      g hg q hq T hqT S.val hc he)
  · exact (Finset.val_injective (multiset_eq_finset_of_card_le_of_zero_anchor
      g hg q hq S hqS T.val hc he.symm)).symm

/-- The exact portion of each coin cover already supplied by the anchored cube. -/
theorem zero_anchor_cube_inter_coinCover_card
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (k : ℕ) :
    (zeroAnchorSubsetCube g q ∩ actualFibreCoinCover g k).card =
      ∑ j ∈ Finset.range (k+1), (n-1).choose j := by
  classical
  let A := Finset.univ.erase q
  let K := (Finset.range (k+1)).biUnion (fun j ↦ A.powersetCard j)
  have hK (S : Finset (Fin n)) : S ∈ K ↔ S ⊆ A ∧ S.card ≤ k := by
    simp only [K,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard]
    constructor
    · rintro ⟨j,hj,hS,hcard⟩; exact ⟨hS,by omega⟩
    · rintro ⟨hS,hcard⟩; exact ⟨S.card,by omega,hS,rfl⟩
  have he : zeroAnchorSubsetCube g q ∩ actualFibreCoinCover g k =
      K.image (fun S ↦ ∑ i ∈ S, g i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hB,hC⟩ := Finset.mem_inter.mp hx
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hB
      have hsub : S ⊆ A := Finset.mem_powerset.mp hS
      have hqS : q ∉ S := fun h ↦ (Finset.mem_erase.mp (hsub h)).1 rfl
      exact Finset.mem_image.mpr ⟨S,(hK S).mpr ⟨hsub,
        (anchored_subset_sum_mem_coinCover_iff g hg q hq S hqS k).mp hC⟩,rfl⟩
    · intro hx
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hsub,hcard⟩ := (hK S).mp hS
      have hqS : q ∉ S := fun h ↦ (Finset.mem_erase.mp (hsub h)).1 rfl
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
        ⟨S,Finset.mem_powerset.mpr hsub,rfl⟩,
        (anchored_subset_sum_mem_coinCover_iff g hg q hq S hqS k).mpr hcard⟩
  have hinj : Set.InjOn (fun S : Finset (Fin n) ↦ ∑ i ∈ S, g i) K := by
    intro S hS T hT he
    exact zero_anchor_subset_sum_injective g hg q hq
      (Finset.mem_powerset.mpr ((hK S).mp hS).1)
      (Finset.mem_powerset.mpr ((hK T).mp hT).1) he
  rw [he,Finset.card_image_iff.mpr hinj]
  dsimp [K]
  rw [Finset.card_biUnion]
  · simp [A,Finset.card_powersetCard]
  · intro i _ j _ hij
    exact A.pairwise_disjoint_powersetCard hij

/-- All additional coin values lie outside the entire anchored cube.
This is an exact disjoint count in every degree. -/
theorem coinCover_card_eq_anchored_partial_choose_add_outside
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (k : ℕ) :
    (actualFibreCoinCover g k).card =
      (∑ j ∈ Finset.range (k+1), (n-1).choose j)+
      (actualFibreCoinCover g k \ zeroAnchorSubsetCube g q).card := by
  classical
  have h := Finset.card_sdiff_add_card_inter
    (actualFibreCoinCover g k) (zeroAnchorSubsetCube g q)
  rw [Finset.inter_comm,zero_anchor_cube_inter_coinCover_card g hg q hq] at h
  omega

/-- The exact outside-cube decomposition applies at every anchor of every
valid tuple, by normalization; oddness is not needed. -/
theorem coinCover_sub_anchor_card_eq_partial_choose_add_outside
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (k : ℕ) :
    (actualFibreCoinCover (fun i ↦ g i-g q) k).card =
      (∑ j ∈ Finset.range (k+1), (n-1).choose j)+
      (actualFibreCoinCover (fun i ↦ g i-g q) k \
        zeroAnchorSubsetCube (fun i ↦ g i-g q) q).card := by
  exact coinCover_card_eq_anchored_partial_choose_add_outside
    (fun i ↦ g i-g q) (validTuple_sub_const g hg (g q)) q (by simp) k

end MinModulus.Research
