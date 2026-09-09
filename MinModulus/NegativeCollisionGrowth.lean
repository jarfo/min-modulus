import MinModulus.UnitGapEscapeDensity

namespace MinModulus
open Finset
open scoped Classical

/-- All ranked predecessor growth on the smaller side of a collision
must stop strictly before the cardinality of its larger side. -/
theorem negative_side_ranked_growth_lt_positive_card
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) : (∑ i ∈ V, 2^(r i)) < U.card := by
  classical
  by_contra hnot
  have hW : U.card ≤ (V.val.map (fun i ↦ 2^(r i))).sum := by
    change U.card ≤ ∑ i ∈ V, 2^(r i)
    omega
  obtain ⟨t,ht,hvalue,hweight⟩ := exists_multiset_refinement_on_finite_ranked_doubling
    (fun i ↦ g i+b) r hp V.val (K := U.card-1) (by change V.card ≤ _; omega) (by omega)
  have hpos : ∃ j ∈ t, 0 < r j := by
    by_contra h
    push Not at h
    have hall : ∀ j ∈ t, (2 : ℕ)^(r j)=1 := by
      intro j hj
      have hz : r j=0 := by have := h j hj; omega
      rw [hz,pow_zero]
    have hw : (t.map (fun j ↦ 2^(r j))).sum=t.card := by
      calc
        _ = (t.map (fun _ ↦ (1 : ℕ))).sum := congrArg Multiset.sum (Multiset.map_congr rfl hall)
        _ = t.card := by simp
    omega
  obtain ⟨j,hjt,hjr⟩ := hpos
  obtain ⟨i,_,hij⟩ := hp j hjr
  have hc : (t.erase j).card+2=U.card := by
    have h := Multiset.card_erase_add_one hjt
    omega
  have he' : ((j ::ₘ t.erase j).map (fun a ↦ g a+b)).sum=∑ a ∈ U, (g a+b) := by
    rw [Multiset.cons_erase hjt,hvalue]
    exact he.symm
  apply no_affine_predecessor_of_one_short_representation g hg b U (t.erase j) j hc he' i
  apply add_right_cancel (b := b)
  calc
    g j+b = 2 • (g i+b) := hij
    _ = (2 • g i+b)+b := by simp only [two_nsmul]; abel

/-- The sum of all excess predecessor weights on the smaller side is
strictly less than the collision's cardinality gap. -/
theorem negative_side_ranked_growth_tax_lt_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) : (∑ i ∈ V, (2^(r i)-1)) < U.card-V.card := by
  have h := negative_side_ranked_growth_lt_positive_card g hg b r hp U V he hlt
  have hs : (∑ i ∈ V, (2^(r i)-1))+V.card=∑ i ∈ V, 2^(r i) := by
    rw [Finset.card_eq_sum_ones,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have := Nat.one_le_two_pow (n := r i)
    omega
  omega

/-- A coordinate of predecessor rank k can occur on the smaller side
only when the cardinality gap is at least 2^k. -/
theorem negative_side_predecessor_rank_power_le_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) (j : Fin n) (hj : j ∈ V) : 2^(r j) ≤ U.card-V.card := by
  have h := negative_side_ranked_growth_tax_lt_gap g hg b r hp U V he hlt
  have hsingle := Finset.single_le_sum (s := V) (f := fun i ↦ 2^(r i)-1) (fun _ _ ↦ Nat.zero_le _) hj
  have := Nat.one_le_two_pow (n := r j)
  omega

/-- The smaller side of any unequal collision avoids every set closed
under affine doubling predecessors, even when the larger side meets that set. -/
theorem negative_side_disjoint_predecessor_closed_set
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V C : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card)
    (hC : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j+b) : Disjoint V C := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjV hjC
  have hp : ∀ i : C, ∃ k : C, g i.val+b=2 • (g k.val+b) := by
    intro i
    obtain ⟨k,hk,he⟩ := hC i.val i.property
    refine ⟨⟨k,hk⟩,?_⟩
    rw [he,two_nsmul,two_nsmul]
    abel
  let jc : C := ⟨j,hjC⟩
  obtain ⟨t,ht,hvalue⟩ := exists_multiset_card_ge_of_doubling_predecessors
    (fun i : C ↦ g i.val+b) hp ({jc} : Multiset C) (by simp)
    (K := U.card-V.card) (by simp; omega)
  have hdecomp : t=0 ∨ ∃ a R, t=a ::ₘ R :=
    Multiset.induction_on t (Or.inl rfl) (fun a R _ ↦ Or.inr ⟨a,R,rfl⟩)
  rcases hdecomp with hz | ⟨a,R,rfl⟩
  · simp only [hz,Multiset.card_zero] at ht
    omega
  · let R' := R.map Subtype.val+V.val.erase j
    have hc : R'.card+2=U.card := by
      have h := Multiset.card_erase_add_one hjV
      simp only [R',Multiset.card_add,Multiset.card_map,Multiset.card_cons] at *
      change (V.val.erase j).card+1=V.card at h
      omega
    have hvalue' : g a.val+b+(R.map (fun i : C ↦ g i.val+b)).sum=g j+b := by
      simpa only [Multiset.map_cons,Multiset.sum_cons,Multiset.map_singleton,Multiset.sum_singleton,jc] using hvalue
    have hVsum : (g j+b)+((V.val.erase j).map (fun i ↦ g i+b)).sum=∑ i ∈ V, (g i+b) := by
      have h := congrArg (fun t : Multiset (Fin n) ↦ (t.map (fun i ↦ g i+b)).sum) (Multiset.cons_erase hjV)
      simpa only [Multiset.map_cons,Multiset.sum_cons,Finset.sum_eq_multiset_sum] using h
    have he' : ((a.val ::ₘ R').map (fun i ↦ g i+b)).sum=∑ i ∈ U, (g i+b) := by
      simp only [R',Multiset.map_cons,Multiset.sum_cons,Multiset.map_add,Multiset.sum_add,Multiset.map_map]
      change (g a.val+b)+((R.map (fun i : C ↦ g i.val+b)).sum+
        ((V.val.erase j).map (fun i ↦ g i+b)).sum)=_
      rw [← add_assoc,hvalue',hVsum]
      exact he.symm
    obtain ⟨k,hk,hak⟩ := hC a.val a.property
    exact no_affine_predecessor_of_one_short_representation g hg b U R' a.val hc he' k hak

/-- No smaller-side coordinate of an unequal collision lies in an
embedded affine doubling cycle or a permutation-invariant union of cycles. -/
theorem negative_side_disjoint_affine_cycle_image
    {n m : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) (e : Fin m ↪ Fin n) (P : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (P i))=2 • g (e i)+b) : Disjoint V (Finset.univ.map e) := by
  apply negative_side_disjoint_predecessor_closed_set g hg b U V (Finset.univ.map e) he hlt
  intro j hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
  refine ⟨e (P.symm i),Finset.mem_map.mpr ⟨P.symm i,Finset.mem_univ _,rfl⟩,?_⟩
  simpa only [P.apply_symm_apply] using hcycle (P.symm i)

/-- Every heavier collision side contains every predecessor-closed set.
Padding a missing coordinate on both sides would violate the negative-side exclusion. -/
theorem predecessor_closed_set_subset_positive_side
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V C : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card)
    (hC : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j+b) : C ⊆ U := by
  classical
  have hd := negative_side_disjoint_predecessor_closed_set g hg b U V C he hlt hC
  intro j hjC
  by_contra hjU
  have hjV : j ∉ V := fun h ↦ Finset.disjoint_left.mp hd h hjC
  have he' : (∑ i ∈ insert j U, (g i+b))=(∑ i ∈ insert j V, (g i+b)) := by
    rw [Finset.sum_insert hjU,Finset.sum_insert hjV,he]
  have hlt' : (insert j V).card < (insert j U).card := by
    rw [Finset.card_insert_of_notMem hjU,Finset.card_insert_of_notMem hjV]
    omega
  have hd' := negative_side_disjoint_predecessor_closed_set g hg b (insert j U) (insert j V) C he' hlt' hC
  exact Finset.disjoint_left.mp hd' (Finset.mem_insert_self _ _) hjC

/-- Every heavier collision side contains the full image of every
embedded affine doubling cycle or permutation-invariant union of cycles. -/
theorem affine_cycle_image_subset_positive_side
    {n m : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) (e : Fin m ↪ Fin n) (P : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (P i))=2 • g (e i)+b) : Finset.univ.map e ⊆ U := by
  apply predecessor_closed_set_subset_positive_side g hg b U V (Finset.univ.map e) he hlt
  intro j hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
  refine ⟨e (P.symm i),Finset.mem_map.mpr ⟨P.symm i,Finset.mem_univ _,rfl⟩,?_⟩
  simpa only [P.apply_symm_apply] using hcycle (P.symm i)

end MinModulus
