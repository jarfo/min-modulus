import research.RepeatedAnchoredCubeFiltration
import MinModulus.OddOrder

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Under injective doubling, a nonempty anchored subset has a duplicated
member whose value escapes the entire anchored cube. -/
theorem exists_duplicate_subset_sum_outside_cube
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hdouble : Function.Injective (fun x : ZMod N ↦ x+x))
    (q : Fin n) (hq : g q=0) (S : Finset (Fin n))
    (hqS : q ∉ S) (hS : S.Nonempty) :
    ∃ i ∈ S, (∑ j ∈ S,g j)+g i ∉ zeroAnchorSubsetCube g q := by
  classical
  by_contra hnot
  have hinside (i : Fin n) (hi : i ∈ S) :
      (∑ j ∈ S,g j)+g i ∈ zeroAnchorSubsetCube g q := by
    by_contra h; exact hnot ⟨i,hi,h⟩
  have hex (i : Fin n) : ∃ T : Finset (Fin n), q ∉ T ∧
      (i ∈ S → (∑ j ∈ T,g j)=(∑ j ∈ S,g j)+g i) := by
    by_cases hi : i ∈ S
    · obtain ⟨T,hT,he⟩ := Finset.mem_image.mp (hinside i hi)
      exact ⟨T,(fun h ↦ (Finset.mem_erase.mp (Finset.mem_powerset.mp hT h)).1 rfl),
        fun _ ↦ he⟩
    · exact ⟨∅,by simp,fun h ↦ False.elim (hi h)⟩
  choose T hqT hvalue using hex
  have hcard (i : Fin n) (hi : i ∈ S) : (T i).card < S.card :=
    duplicate_subset_sum_in_cube_card_lt g hg q hq S (T i) (hqT i) i hi
      (hvalue i hi).symm
  have hself (i : Fin n) (hi : i ∈ S) : i ∉ T i := by
    intro hit
    have hs : (∑ j ∈ (T i).erase i,g j)=(∑ j ∈ S,g j) := by
      apply add_right_cancel (b := g i)
      rw [Finset.sum_erase_add _ _ hit,hvalue i hi]
    have he := multiset_eq_finset_of_card_le_of_zero_anchor g hg q hq S hqS
      ((T i).erase i).val (by
        change ((T i).erase i).card ≤ S.card
        exact Finset.card_erase_le.trans (Nat.le_of_lt (hcard i hi))) hs
    have hc := congrArg Multiset.card he
    change ((T i).erase i).card=S.card at hc
    have hl := Finset.card_erase_le (s := T i) (a := i)
    have ht := hcard i hi
    omega
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image S (fun j ↦ (T j).card) hS
  have hsub : S.erase i ⊆ T i := by
    intro j hj
    obtain ⟨hji,hjS⟩ := Finset.mem_erase.mp hj
    by_contra hjT
    have hqU : q ∉ insert j (T i) := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he ↦ hqS (he ▸ hjS),hqT i⟩
    have hs : ((i ::ₘ (T j).val).map g).sum=∑ a ∈ insert j (T i),g a := by
      simp only [Multiset.map_cons,Multiset.sum_cons,Finset.sum_insert hjT]
      change g i+(∑ a ∈ T j,g a)=g j+(∑ a ∈ T i,g a)
      rw [hvalue i hi,hvalue j hjS]
      abel
    have he := multiset_eq_finset_of_card_le_of_zero_anchor g hg q hq
      (insert j (T i)) hqU (i ::ₘ (T j).val)
      (by simp only [Multiset.card_cons,Finset.card_val,
        Finset.card_insert_of_notMem hjT]; exact Nat.add_le_add_right (hmax j hjS) 1) hs
    have hm : i ∈ (insert j (T i)).val := he ▸ Multiset.mem_cons_self _ _
    have hm' : i=j ∨ i ∈ T i := Finset.mem_insert.mp hm
    exact hm'.elim (fun h ↦ hji h.symm) (hself i hi)
  have heT : S.erase i=T i := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem hi]
    have := hcard i hi
    omega)
  have hv := hvalue i hi
  have hs := Finset.sum_erase_add S g hi
  rw [heT] at hs
  rw [← hs] at hv
  have hd : g i+g i=0+0 := by
    have hc : (∑ j ∈ T i,g j)+0=(∑ j ∈ T i,g j)+(g i+g i) := by
      simpa only [add_zero,add_assoc] using hv
    simpa only [zero_add] using (add_left_cancel hc).symm
  have hgi : g i=0 := hdouble hd
  have hqi : q ≠ i := fun h ↦ hqS (h ▸ hi)
  have he := multiset_eq_finset_of_card_le_of_zero_anchor g hg q hq {i}
    (by simpa) (0 : Multiset (Fin n)) (by simp) (by simp [hgi])
  have hc := congrArg Multiset.card he
  simpa using hc

/-- Every nonempty anchored subset has a duplication escaping the full
cube at odd cyclic modulus, in arbitrary dimension and subset degree. -/
theorem exists_duplicate_subset_sum_outside_cube_of_odd
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (q : Fin n) (hq : g q=0) (S : Finset (Fin n))
    (hqS : q ∉ S) (hS : S.Nonempty) :
    ∃ i ∈ S, (∑ j ∈ S,g j)+g i ∉ zeroAnchorSubsetCube g q := by
  exact exists_duplicate_subset_sum_outside_cube g hg
    (fun _ _ he ↦ add_self_injective_zmod hN _ _ he) q hq S hqS hS

end MinModulus.Research
