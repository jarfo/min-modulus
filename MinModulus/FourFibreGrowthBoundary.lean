import MinModulus.FibreGrowthSaturation
import MinModulus.CoarsenedDoublingGrowth
import MinModulus.FibreMultiplicityEscapeDensity

namespace MinModulus
open Finset
open scoped Classical

/-- At four-point growth saturation the fibre is precisely at zero,
with complementary proper zero-sum subsets of weights D and 2D. -/
theorem zero_partition_of_four_fibre_growth_saturation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : 3*((∑ i, 2^(r i))-n+1)=∑ i, 2^(r i)) :
    z=0 ∧ (∑ i, (g i+b))=0 ∧
      ∃ U : Finset (Fin n), U.card < Uᶜ.card ∧
        (∑ i ∈ U, (g i+b))=0 ∧ (∑ i ∈ Uᶜ, (g i+b))=0 ∧
        (∑ i ∈ U, 2^(r i))=(∑ i, 2^(r i))-n+1 ∧
        (∑ i ∈ Uᶜ, 2^(r i))=2*((∑ i, 2^(r i))-n+1) := by
  classical
  let F := Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)
  let W := ∑ i, 2^(r i)
  let D := W-n+1
  have hD : 0 < D := by dsimp [D]; omega
  change 3*D=W at hboundary
  change 4 ≤ F.card at hfour
  have hf := fibre_card_sub_one_mul_growth_step_le_total_weight g hg b z r hp
  change (F.card-1)*D ≤ W at hf
  have hcard : F.card=4 := by
    have hsub : F.card-1+1=F.card := by omega
    nlinarith [hf]
  have hbase := dimension_le_total_ranked_weight r
  change n ≤ W at hbase
  have hn : 0 < n := by dsimp [D] at hboundary; omega
  have heq : (F.card-1)*D=W := by rw [hcard]; simpa using hboundary
  obtain ⟨hz,htotal⟩ := zero_value_and_total_of_fibre_growth_saturation g hg b z r hp hn heq
  refine ⟨hz,htotal,?_⟩
  have hproper : ∃ U ∈ F, U ≠ ∅ ∧ U ≠ Finset.univ := by
    by_contra h
    push Not at h
    have hsub : F ⊆ ({∅,Finset.univ} : Finset (Finset (Fin n))) := by
      intro U hU
      by_cases he : U=∅
      · simp [he]
      · simp [h U hU (Finset.nonempty_iff_ne_empty.mpr he)]
    have hc := Finset.card_le_card hsub
    have hc2 : ({∅,Finset.univ} : Finset (Finset (Fin n))).card ≤ 2 := by simpa using Finset.card_insert_le (∅ : Finset (Fin n)) {Finset.univ}
    omega
  obtain ⟨A,hA,hA0,hA1⟩ := hproper
  have hAz : (∑ i ∈ A, (g i+b))=0 := (Finset.mem_filter.mp hA).2.trans hz
  have hAc : (∑ i ∈ Aᶜ, (g i+b))=0 := by
    have hh := Finset.sum_add_sum_compl A (fun i ↦ g i+b)
    rw [hAz,htotal,zero_add] at hh
    exact hh
  have hAcF : Aᶜ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAc.trans hz.symm⟩
  have hcardne : A.card ≠ Aᶜ.card := by
    intro hc
    have he := tuple_subset_fibre_cardinality_injective g hg b z hA hAcF hc
    have hd : Disjoint A A := by
      rw [he]
      exact Finset.disjoint_left.mpr (fun i hi hic ↦ (Finset.mem_compl.mp hi) (by simpa only [← he] using hic))
    have hempty := (Finset.disjoint_self_iff_empty A).mp hd
    exact hA0 hempty
  have hfinish (U : Finset (Fin n)) (hU0 : U ≠ ∅) (hU1 : U ≠ Finset.univ)
      (hU : (∑ i ∈ U, (g i+b))=0) (hUc : (∑ i ∈ Uᶜ, (g i+b))=0)
      (hc : U.card < Uᶜ.card) :
      ∃ U : Finset (Fin n), U.card < Uᶜ.card ∧
        (∑ i ∈ U, (g i+b))=0 ∧ (∑ i ∈ Uᶜ, (g i+b))=0 ∧
        (∑ i ∈ U, 2^(r i))=D ∧ (∑ i ∈ Uᶜ, 2^(r i))=2*D := by
    have hpos : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU0)
    have hUcn : Uᶜ.card < n := by
      have hh := Finset.card_compl_add_card U
      simp only [Fintype.card_fin] at hh
      omega
    have hlo := ranked_weight_separation_of_unequal_collision g hg b r hp U ∅
      (by simpa using hU) (by simpa using hpos)
    simp only [Finset.sum_empty,zero_add] at hlo
    have hmid := ranked_weight_separation_of_unequal_collision g hg b r hp Uᶜ U
      (hUc.trans hU.symm) hc
    have hhi := ranked_weight_separation_of_unequal_collision g hg b r hp Finset.univ Uᶜ
      (by simpa only [Finset.sum_eq_multiset_sum] using htotal.trans hUc.symm) (by simpa using hUcn)
    change D ≤ ∑ i ∈ U, 2^(r i) at hlo
    change (∑ i ∈ U, 2^(r i))+D ≤ ∑ i ∈ Uᶜ, 2^(r i) at hmid
    change (∑ i ∈ Uᶜ, 2^(r i))+D ≤ W at hhi
    refine ⟨U,hc,hU,hUc,?_,?_⟩ <;> omega
  rcases lt_or_gt_of_ne hcardne with hc | hc
  · exact hfinish A hA0 hA1 hAz hAc hc
  · have hc0 : Aᶜ ≠ ∅ := by simpa using hA1
    have hc1 : Aᶜ ≠ Finset.univ := by simpa using hA0
    have hh := hfinish Aᶜ hc0 hc1 hAc (by simpa using hAz) (by simpa using hc)
    exact hh

/-- Four-fibre saturation is impossible when all but one unit of its
growth step is realized by distinct rank-zero contraction roots. -/
theorem not_four_fibre_growth_saturation_of_contraction_roots
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (R : Finset (Fin n)) (t : Fin n → Fin n)
    (hR : ∀ i ∈ R, r i=0 ∧ r (t i)=1 ∧ g (t i)+b=2 • (g i+b))
    (hcard : R.card+1=(∑ i, 2^(r i))-n+1) :
    3*((∑ i, 2^(r i))-n+1) ≠ ∑ i, 2^(r i) := by
  intro hboundary
  obtain ⟨_,htotal,U,hsmall,hU,hUc,hwU,hwUc⟩ :=
    zero_partition_of_four_fibre_growth_saturation g hg b z r hp hfour hboundary
  let W := ∑ i, 2^(r i)
  let D := W-n+1
  change R.card+1=D at hcard
  change 3*D=W at hboundary
  change (∑ i ∈ U, 2^(r i))=D at hwU
  change (∑ i ∈ Uᶜ, 2^(r i))=2*D at hwUc
  have hD : 0 < D := by omega
  have hbase := dimension_le_total_ranked_weight r
  change n ≤ W at hbase
  have hDn : D=W-n+1 := rfl
  have hn : n=2*D+1 := by omega
  have hweight_le_card (S : Finset (Fin n)) (hS : S ⊆ R) :
      (∑ i ∈ S, 2^(r i)) ≤ R.card := by
    have hs : (∑ i ∈ S, 2^(r i))=S.card := by
      calc
        _ = ∑ _i ∈ S, (1 : ℕ) := Finset.sum_congr rfl (fun i hi ↦ by rw [(hR i (hS hi)).1]; simp)
        _ = S.card := by simp
    rw [hs]
    exact Finset.card_le_card hS
  have hneU : (U \ R).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hweight_le_card U (Finset.sdiff_eq_empty_iff_subset.mp he)
    omega
  have hneUc : (Uᶜ \ R).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hweight_le_card Uᶜ (Finset.sdiff_eq_empty_iff_subset.mp he)
    omega
  have hstep (S : Finset (Fin n)) : ∀ i ∈ S ∩ R,
      r (t i)=r i+1 ∧ g (t i)+b=2 • (g i+b) := by
    intro i hi
    obtain ⟨h0,h1,hval⟩ := hR i (Finset.mem_inter.mp hi).2
    exact ⟨by omega,hval⟩
  have hcardU : U.card ≤ ∑ i ∈ U, 2^(r i) := by
    simpa using Finset.sum_le_sum (s:=U) (fun i _ ↦ Nat.one_le_pow (r i) 2 (by decide))
  have hcardUc : Uᶜ.card ≤ ∑ i ∈ Uᶜ, 2^(r i) := by
    simpa using Finset.sum_le_sum (s:=Uᶜ) (fun i _ ↦ Nat.one_le_pow (r i) 2 (by decide))
  have hfirst := zero_subset_coarsening_card_obstruction g hg b r hp U Uᶜ R t (hstep U)
    hU hUc hneU (by omega)
  have hsecond := zero_subset_coarsening_card_obstruction g hg b r hp Uᶜ Finset.univ R t (hstep Uᶜ)
    hUc (by simpa using htotal) hneUc (by simp; omega)
  simp only [Finset.card_univ,Fintype.card_fin] at hsecond
  have hcomp := Finset.card_compl_add_card U
  simp only [Fintype.card_fin] at hcomp
  have hsplit : (U ∩ R).card+(Uᶜ ∩ R).card=R.card := by
    have he : R \ U=Uᶜ ∩ R := by ext i; simp; tauto
    have hh := Finset.card_sdiff_add_card_inter R U
    rw [he,Finset.inter_comm R U] at hh
    omega
  omega

/-- Rank-one targets supply equally many distinct rank-zero contraction
roots, so a four-point fibre cannot saturate a two-level rank system. -/
theorem not_four_fibre_growth_saturation_of_ranks_le_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hr : ∀ i, r i ≤ 1)
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    3*((∑ i, 2^(r i))-n+1) ≠ ∑ i, 2^(r i) := by
  classical
  let T := Finset.univ.filter (fun i ↦ r i=1)
  have hT (j : T) : r j.val=1 := (Finset.mem_filter.mp j.property).2
  choose p hpr hpval using (fun j : T ↦ hp j.val (by rw [hT]; decide))
  have hpzero (j : T) : r (p j)=0 := by have := hpr j; rw [hT] at this; omega
  have hpinj : Function.Injective p := by
    intro i j he
    apply Subtype.ext
    apply validTuple_injective g hg
    apply add_right_cancel (b:=b)
    rw [hpval i,hpval j,he]
  let R : Finset (Fin n) := Finset.univ.image p
  have hRcard : R.card=T.card := by
    simp only [R,Finset.card_image_of_injective _ hpinj,Finset.card_univ,Fintype.card_coe]
  have hRzero : ∀ i ∈ R, r i=0 := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact hpzero j
  have ht : ∀ i : Fin n, ∃ j : Fin n, i ∈ R → r j=1 ∧ g j+b=2 • (g i+b) := by
    intro i
    by_cases hi : i ∈ R
    · obtain ⟨j,_,he⟩ := Finset.mem_image.mp hi
      exact ⟨j.val,fun _ ↦ ⟨hT j,by simpa only [he] using hpval j⟩⟩
    · exact ⟨i,fun h ↦ (hi h).elim⟩
  choose t ht using ht
  have hweight : (∑ i, 2^(r i))=n+T.card := by
    calc
      _ = ∑ i : Fin n, (1+(if r i=1 then 1 else 0) : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        have h := hr i
        interval_cases hri : r i <;> norm_num
      _ = n+T.card := by simp [T,Finset.sum_add_distrib]
  apply not_four_fibre_growth_saturation_of_contraction_roots g hg b z r hp hfour R t
  · intro i hi
    exact ⟨hRzero i hi,(ht i hi).1,(ht i hi).2⟩
  · rw [hweight,hRcard]
    omega

/-- A complete forest with arms of length at most two supplies a
predecessor rank certificate taking only the values zero and one. -/
theorem exists_two_level_ranks_of_short_actual_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hL : ∀ a, L a ≤ 2) :
    ∃ r : Fin n → ℕ,
      (∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b)) ∧
      (∀ i, r i ≤ 1) ∧ (∑ i, 2^(r i))=∑ a, (2^(L a)-1) := by
  classical
  let r : Fin n → ℕ := fun i ↦ (E.symm i).2.val
  have hr (a : β) (j : Fin (L a)) : r (E ⟨a,j⟩)=j.val := by
    exact congrArg (fun p : Σ a : β, Fin (L a) ↦ p.2.val) (E.symm_apply_apply ⟨a,j⟩)
  refine ⟨r,?_,?_,?_⟩
  · intro i hi
    obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective i
    rw [hr] at hi
    let p : Fin (L a) := ⟨j.val-1,by omega⟩
    refine ⟨E ⟨a,p⟩,?_,?_⟩
    · rw [hr,hr]
      dsimp [p]
      omega
    · rw [hchain,hchain,show j.val=p.val+1 by dsimp [p]; omega,pow_succ',mul_smul]
  · intro i
    obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective i
    rw [hr]
    have := hL a
    omega
  · rw [← Equiv.sum_comp E]
    simp only [Fintype.sum_sigma,hr,sum_binary_powers]

/-- Actual doubling contractions exclude equality in the relaxed
four-fibre forest bound. Thus every such forest needs one more unit. -/
theorem dimension_add_four_le_twice_forest_arms_of_four_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+4 ≤ 2*Fintype.card β := by
  classical
  have hold := dimension_add_three_le_twice_forest_arms_of_four_fibre L g hg E x b z hchain hfour
  by_contra h
  have he : n+3=2*Fintype.card β := by omega
  obtain ⟨r,hp,hsum⟩ := exists_global_ranks_of_actual_forest L g E x b hchain
  have htax := fibre_card_sub_two_mul_growth_tax_bound g hg b z r hp (by omega)
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  let W := ∑ i, 2^(r i)
  change 4 ≤ m at hfour
  change (m-2)*(W-n)+m-1 ≤ n at htax
  rw [Nat.add_sub_assoc (by omega : 1 ≤ m)] at htax
  have hm := Nat.mul_le_mul_right (W-n) (by omega : 2 ≤ m-2)
  have hsmall : 2*(W-n)+3 ≤ n := by omega
  have hbase := dimension_le_total_ranked_weight r
  change n ≤ W at hbase
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hline := twice_total_length_le_binary_weight_add_arm_count L
  rw [hsize,← hsum] at hline
  change 2*n ≤ W+Fintype.card β at hline
  have hboundary : 3*(W-n+1)=W := by omega
  have hlinear : 2*n=W+Fintype.card β := by omega
  have hpoint (a : β) : 2*L a ≤ (2^(L a)-1)+1 := by
    have hh := Nat.mul_le_pow (by decide : 2 ≠ 1) (L a)
    have hh' := pow_pos (by decide : 0 < (2 : ℕ)) (L a)
    omega
  have hstrict (k : ℕ) : 2*(k+3) < 2^(k+3) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show k+1+3=(k+3)+1 by omega,pow_succ]
      omega
  have hL : ∀ a, L a ≤ 2 := by
    intro a
    by_contra ha
    have hh := hstrict (L a-3)
    rw [show L a-3+3=L a by omega] at hh
    have hh' : 2*L a < (2^(L a)-1)+1 := by omega
    have hlt := Finset.sum_lt_sum (s:=Finset.univ) (fun a _ ↦ hpoint a)
      ⟨a,Finset.mem_univ a,hh'⟩
    simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one,hsize,← hsum] at hlt
    change 2*n < W+Fintype.card β at hlt
    omega
  obtain ⟨s,hsp,hsone,hssum⟩ := exists_two_level_ranks_of_short_actual_forest L g E x b hchain hL
  have hno := not_four_fibre_growth_saturation_of_ranks_le_one g hg b z s hsp hsone hfour
  rw [hssum,← hsum] at hno
  exact hno hboundary

end MinModulus
