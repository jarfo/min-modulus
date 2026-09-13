import research.SingleRepeatFibres
import research.MidpointSupportRigidity

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Count single-repeat incidences on any selected values by first
choosing the squarefree residual support and then its outside anchor. -/
theorem sum_single_repeat_fibre_card_on_values
    {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (Y : Finset (ZMod N)) :
    (∑ x ∈ Y, (singleRepeatFibre g k x).card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (Finset.univ.filter (fun a : Fin n ↦ a ∉ S ∧
          2 • g a+(∑ i ∈ S, g i) ∈ Y)).card := by
  classical
  simp_rw [← single_repeat_configuration_fibre_card g hg]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  let L := (singleRepeatConfigurations n k).filter
    (fun p ↦ (∑ i ∈ p.1, g i)+g p.2 ∈ Y)
  let Q := ((Finset.univ : Finset (Fin n)).powersetCard k).sigma
    (fun S ↦ Finset.univ.filter (fun a : Fin n ↦ a ∉ S ∧
      2 • g a+(∑ i ∈ S, g i) ∈ Y))
  have hL (p : Σ _ : Finset (Fin n), Fin n) :
      p ∈ L ↔ p.1.card=k+1 ∧ p.2 ∈ p.1 ∧ (∑ i ∈ p.1, g i)+g p.2 ∈ Y := by
    constructor
    · intro hp
      obtain ⟨hp,hy⟩ := Finset.mem_filter.mp hp
      obtain ⟨hS,ha⟩ := Finset.mem_sigma.mp hp
      exact ⟨(Finset.mem_powersetCard.mp hS).2,ha,hy⟩
    · rintro ⟨hS,ha,hy⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hS⟩,ha⟩,hy⟩
  have hQ (p : Σ _ : Finset (Fin n), Fin n) :
      p ∈ Q ↔ p.1.card=k ∧ p.2 ∉ p.1 ∧ 2 • g p.2+(∑ i ∈ p.1, g i) ∈ Y := by
    constructor
    · intro hp
      obtain ⟨hS,ha⟩ := Finset.mem_sigma.mp hp
      exact ⟨(Finset.mem_powersetCard.mp hS).2,(Finset.mem_filter.mp ha).2⟩
    · rintro ⟨hS,ha,hy⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _,hS⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hy⟩⟩
  have hcard : L.card=Q.card := by
    refine Finset.card_bij' (fun p _ ↦ ⟨p.1.erase p.2,p.2⟩)
      (fun p _ ↦ ⟨insert p.2 p.1,p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hc,ha,hy⟩ := (hL p).mp hp
      apply (hQ _).mpr
      refine ⟨?_,Finset.notMem_erase _ _,?_⟩
      · rw [Finset.card_erase_of_mem ha,hc]; omega
      · have he : 2 • g p.2+(∑ i ∈ p.1.erase p.2, g i)=
            (∑ i ∈ p.1, g i)+g p.2 := by
          rw [← Finset.sum_erase_add p.1 g ha,two_nsmul]; abel
        exact he.symm ▸ hy
    · intro p hp
      obtain ⟨hc,ha,hy⟩ := (hQ p).mp hp
      apply (hL _).mpr
      refine ⟨?_,Finset.mem_insert_self _ _,?_⟩
      · rw [Finset.card_insert_of_notMem ha,hc]
      · have he : (∑ i ∈ insert p.2 p.1, g i)+g p.2=
            2 • g p.2+(∑ i ∈ p.1, g i) := by
          rw [Finset.sum_insert ha,two_nsmul]; abel
        exact he.symm ▸ hy
    · rintro ⟨S,a⟩ hp
      have ha := ((hL ⟨S,a⟩).mp hp).2.1
      simp only [Finset.insert_erase ha]
    · rintro ⟨S,a⟩ hp
      have ha := ((hQ ⟨S,a⟩).mp hp).2.1
      simp only [Finset.erase_insert ha]
  change L.card = _
  rw [hcard,Finset.card_sigma]

/-- Sum the midpoint escape bound over all residual supports. This gives
an all-degree incidence lower bound outside the doubled half-degree cover. -/
theorem single_repeat_outside_doubled_cover_incidence_lower_bound
    {n N k : ℕ} [NeZero N] (hk : 1 ≤ k) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    let E := (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)
    (n-(2*k+2))*n.choose (2*k) ≤
      ∑ x ∈ Eᶜ, (singleRepeatFibre g (2*k) x).card := by
  classical
  intro E
  rw [sum_single_repeat_fibre_card_on_values g hg Eᶜ]
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2*k), (n-(2*k+2)) := by
      simp only [Finset.sum_const,Finset.card_powersetCard,Finset.card_univ,
        Fintype.card_fin,smul_eq_mul,mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro S hS
      have h := squarefree_single_repeat_escape_count hk hN g hg S
        (Finset.mem_powersetCard.mp hS).2
      simpa only [Finset.mem_compl] using h

/-- Incidences on selected values are at most the number of occupied
repeated values plus the number of colliding unordered anchor pairs. -/
theorem single_repeat_incidence_le_values_add_pair_collisions
    {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (Y : Finset (ZMod N)) :
    (∑ x ∈ Y, (singleRepeatFibre g k x).card) ≤
      ((repeatedCoinCover g (k+2)) ∩ Y).card +
        ∑ x ∈ Y, ((singleRepeatFibre g k x).card).choose 2 := by
  classical
  have hnum (r : ℕ) : r ≤ 1+r.choose 2 := by
    rcases r with _ | r
    · simp
    rcases r with _ | r
    · simp
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    omega
  have hpoint (x : ZMod N) : (singleRepeatFibre g k x).card ≤
      (if x ∈ repeatedCoinCover g (k+2) then 1 else 0) +
        ((singleRepeatFibre g k x).card).choose 2 := by
    by_cases hx : x ∈ repeatedCoinCover g (k+2)
    · simpa only [if_pos hx] using hnum (singleRepeatFibre g k x).card
    · have hz : singleRepeatFibre g k x=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hx (mem_repeatedCoinCover_of_single_repeat g x a ha)
      simp [hz]
  calc
    _ ≤ ∑ x ∈ Y, ((if x ∈ repeatedCoinCover g (k+2) then 1 else 0) +
        ((singleRepeatFibre g k x).card).choose 2) :=
      Finset.sum_le_sum (fun x _ ↦ hpoint x)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        _ = (Y.filter (fun x ↦ x ∈ repeatedCoinCover g (k+2))).card := by
          simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
        _ = _ := by
          congr 1
          ext x
          simp only [Finset.mem_filter,Finset.mem_inter,and_comm]

/-- A uniform global lower bound with the entire unresolved loss
expressed as pair collisions outside the doubled half-degree cover. -/
theorem single_repeat_outside_doubled_cover_pair_collision_bound
    {n N k : ℕ} [NeZero N] (hk : 1 ≤ k) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    let E := (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)
    (n-(2*k+2))*n.choose (2*k) ≤
      ((repeatedCoinCover g (2*k+2)) \ E).card +
        ∑ x ∈ Eᶜ, ((singleRepeatFibre g (2*k) x).card).choose 2 := by
  classical
  intro E
  have hlo := single_repeat_outside_doubled_cover_incidence_lower_bound hk hN g hg
  have hhi := single_repeat_incidence_le_values_add_pair_collisions g Eᶜ (k := 2*k)
  have heq : (repeatedCoinCover g (2*k+2)) ∩ Eᶜ =
      (repeatedCoinCover g (2*k+2)) \ E := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_compl,Finset.mem_sdiff]
  rw [heq] at hhi
  exact hlo.trans hhi

/-- Reindex pair collisions by the unordered anchor pair, so that local
translated-intersection estimates can be summed without overcounting. -/
theorem single_repeat_pair_collisions_eq_sum_anchor_pairs
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (Y : Finset G) :
    (∑ x ∈ Y, ((singleRepeatFibre g k x).card).choose 2) =
      ∑ P ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
        (Y.filter (fun x ↦ P ⊆ singleRepeatFibre g k x)).card := by
  classical
  have heq (x : G) : (singleRepeatFibre g k x).powersetCard 2 =
      ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        (fun P ↦ P ⊆ singleRepeatFibre g k x) := by
    ext P
    simp only [Finset.mem_powersetCard,Finset.mem_filter,Finset.subset_univ,true_and]
    tauto
  simp_rw [← Finset.card_powersetCard,heq]
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun x P ↦ P ⊆ singleRepeatFibre g k x)
    (s := Y) (t := (Finset.univ : Finset (Fin n)).powersetCard 2)

/-- Common single-repeat values of two distinct anchors inject into a
translated squarefree intersection on coordinates excluding both anchors.
This connects fibre collision counts to the all-degree intersection bounds. -/
theorem single_repeat_pair_values_card_le_residual_intersection
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (a b : Fin n) (hab : a ≠ b)
    (Y : Finset G) :
    let A := (Finset.univ : Finset (Fin n)) \ {a,b}
    let C := A.powersetCard k
    (Y.filter (fun x ↦ a ∈ singleRepeatFibre g k x ∧
      b ∈ singleRepeatFibre g k x)).card ≤
      ((C.image (fun S ↦ (∑ i ∈ S, g i)+2 • (g a-g b))) ∩
        (C.image (fun S ↦ ∑ i ∈ S, g i))).card := by
  classical
  intro A C
  have hsub (S : Finset (Fin n)) (ha : a ∉ S) (hb : b ∉ S) : S ⊆ A := by
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact not_or.mpr ⟨by intro h; subst i; exact ha hi,
      by intro h; subst i; exact hb hi⟩
  apply Finset.card_le_card_of_injOn (fun x ↦ x-2 • g b)
  · intro x hx
    obtain ⟨ha,hb⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨S,haS,hSc,hSx⟩ := (mem_singleRepeatFibre g x a).mp ha
    obtain ⟨T,hbT,hTc,hTx⟩ := (mem_singleRepeatFibre g x b).mp hb
    have hbS := single_repeat_support_avoids_other_anchor g hg a b hab S T
      haS (hSc.trans hTc.symm) (hSx.trans hTx.symm)
    have haT := single_repeat_support_avoids_other_anchor g hg b a hab.symm T S
      hbT (hTc.trans hSc.symm) (hTx.trans hSx.symm)
    have hUc : (S.erase a).card=k := by rw [Finset.card_erase_of_mem haS,hSc]; omega
    have hVc : (T.erase b).card=k := by rw [Finset.card_erase_of_mem hbT,hTc]; omega
    have hU : S.erase a ∈ C := Finset.mem_powersetCard.mpr
      ⟨hsub _ (Finset.notMem_erase _ _) (fun h ↦ hbS (Finset.mem_of_mem_erase h)),hUc⟩
    have hV : T.erase b ∈ C := Finset.mem_powersetCard.mpr
      ⟨hsub _ (fun h ↦ haT (Finset.mem_of_mem_erase h)) (Finset.notMem_erase _ _),hVc⟩
    have hUval : (∑ i ∈ S.erase a, g i)+2 • g a=x := by
      calc
        _ = (∑ i ∈ S, g i)+g a := by
          rw [← Finset.sum_erase_add S g haS,two_nsmul]; abel
        _ = x := hSx
    have hVval : (∑ i ∈ T.erase b, g i)+2 • g b=x := by
      calc
        _ = (∑ i ∈ T, g i)+g b := by
          rw [← Finset.sum_erase_add T g hbT,two_nsmul]; abel
        _ = x := hTx
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨S.erase a,hU,?_⟩
      change (∑ i ∈ S.erase a, g i)+2 • (g a-g b)=x-2 • g b
      rw [← hUval,smul_sub]
      abel
    · apply Finset.mem_image.mpr
      refine ⟨T.erase b,hV,?_⟩
      change (∑ i ∈ T.erase b, g i)=x-2 • g b
      rw [← hVval,add_sub_cancel_right]
  · intro x _ y _ hxy
    have h := congrArg (fun z ↦ z+2 • g b) hxy
    simpa only [sub_add_cancel] using h

end MinModulus.Research
