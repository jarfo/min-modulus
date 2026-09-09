import MinModulus.ExactProfileOverlap
import MinModulus.G1OddPrimaryCycleLayer

namespace MinModulus
open Finset
open scoped Classical

/-- Once the two disjoint difference sets are fixed, a subset pair is
freely determined by its common subset of the complementary coordinates. -/
theorem subset_pair_difference_fibre_card
    {n : ℕ} (U V : Finset (Fin n)) (hUV : Disjoint U V) :
    (Finset.univ.filter (fun pq : Finset (Fin n) × Finset (Fin n) ↦
      pq.1 \ pq.2=U ∧ pq.2 \ pq.1=V)).card=2^(n-(U ∪ V).card) := by
  classical
  let S := (Finset.univ \ (U ∪ V)).powerset
  let f : Finset (Fin n) → Finset (Fin n) × Finset (Fin n) := fun W ↦ (U ∪ W,V ∪ W)
  have hWU (W : Finset (Fin n)) (hW : W ∈ S) : Disjoint W U := by
    apply Finset.disjoint_left.mpr
    intro i hi hu
    have hh := Finset.mem_powerset.mp hW hi
    exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_union_left _ hu)
  have hWV (W : Finset (Fin n)) (hW : W ∈ S) : Disjoint W V := by
    apply Finset.disjoint_left.mpr
    intro i hi hv
    have hh := Finset.mem_powerset.mp hW hi
    exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_union_right _ hv)
  have hf : Set.InjOn f S := by
    intro W hW R hR he
    have he1 := congrArg Prod.fst he
    change U ∪ W=U ∪ R at he1
    ext i
    have hw : i ∈ W → i ∈ U → False := fun hw hu ↦ Finset.disjoint_left.mp (hWU W hW) hw hu
    have hr : i ∈ R → i ∈ U → False := fun hr hu ↦ Finset.disjoint_left.mp (hWU R hR) hr hu
    have hi := Finset.ext_iff.mp he1 i
    simp only [Finset.mem_union] at hi
    tauto
  have himage : S.image f=Finset.univ.filter (fun pq : Finset (Fin n) × Finset (Fin n) ↦
      pq.1 \ pq.2=U ∧ pq.2 \ pq.1=V) := by
    ext pq
    constructor
    · intro hpq
      obtain ⟨W,hW,rfl⟩ := Finset.mem_image.mp hpq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · ext i
        have hd : i ∈ U → i ∈ V → False := fun hu hv ↦ Finset.disjoint_left.mp hUV hu hv
        have hw : i ∈ W → i ∈ U → False := fun hw hu ↦ Finset.disjoint_left.mp (hWU W hW) hw hu
        simp only [f,Finset.mem_sdiff,Finset.mem_union]
        tauto
      · ext i
        have hd : i ∈ U → i ∈ V → False := fun hu hv ↦ Finset.disjoint_left.mp hUV hu hv
        have hw : i ∈ W → i ∈ V → False := fun hw hv ↦ Finset.disjoint_left.mp (hWV W hW) hw hv
        simp only [f,Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro hpq
      have hh := (Finset.mem_filter.mp hpq).2
      refine Finset.mem_image.mpr ⟨pq.1 ∩ pq.2,?_,?_⟩
      · apply Finset.mem_powerset.mpr
        intro i hi
        have hip := (Finset.mem_inter.mp hi).1
        have hiq := (Finset.mem_inter.mp hi).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro hiuv
        rcases Finset.mem_union.mp hiuv with hiu | hiv
        · rw [← hh.1] at hiu
          exact (Finset.mem_sdiff.mp hiu).2 hiq
        · rw [← hh.2] at hiv
          exact (Finset.mem_sdiff.mp hiv).2 hip
      · apply Prod.ext
        · change U ∪ (pq.1 ∩ pq.2)=pq.1
          rw [← hh.1,Finset.sdiff_union_inter]
        · change V ∪ (pq.1 ∩ pq.2)=pq.2
          rw [← hh.2,Finset.inter_comm,Finset.sdiff_union_inter]
  rw [← himage,Finset.card_image_iff.mpr hf]
  simp only [S,Finset.card_powerset,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]

/-- Disjoint shifted binary relations oriented by strict cardinality.
The common coordinates of any collision are excluded from this core. -/
noncomputable def tupleBinaryCollisionCores
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun uv ↦ Disjoint uv.1 uv.2 ∧
    (∑ i ∈ uv.1, (g i+b))=(∑ i ∈ uv.2, (g i+b)) ∧ uv.2.card < uv.1.card)

/-- Equal-sum subset pairs oriented by the larger subset cardinality. -/
noncomputable def tupleOrderedBinaryCollisions
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun pq ↦
    (∑ i ∈ pq.1, (g i+b))=(∑ i ∈ pq.2, (g i+b)) ∧ pq.2.card < pq.1.card)

/-- Every oriented collision cancels to a unique disjoint relation core. -/
theorem ordered_binary_collision_core_mem
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (pq : Finset (Fin n) × Finset (Fin n)) (hpq : pq ∈ tupleOrderedBinaryCollisions g b) :
    (pq.1 \ pq.2,pq.2 \ pq.1) ∈ tupleBinaryCollisionCores g b := by
  classical
  have hh := (Finset.mem_filter.mp hpq).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,Finset.sum_sdiff_eq_sum_sdiff_iff.mpr hh.1,?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  · have h1 := Finset.card_sdiff_add_card_inter pq.1 pq.2
    have h2 := Finset.card_sdiff_add_card_inter pq.2 pq.1
    rw [Finset.inter_comm pq.2 pq.1] at h2
    change (pq.2 \ pq.1).card < (pq.1 \ pq.2).card
    omega

/-- The ordered collision count is a sum of complementary cube sizes,
one for each actual disjoint relation core. No validity is assumed. -/
theorem ordered_binary_collision_card_eq_core_cube_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    (tupleOrderedBinaryCollisions g b).card=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  let c : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) × Finset (Fin n) :=
    fun pq ↦ (pq.1 \ pq.2,pq.2 \ pq.1)
  have hpart := Finset.card_eq_sum_card_fiberwise (s:=tupleOrderedBinaryCollisions g b)
    (t:=tupleBinaryCollisionCores g b) (f:=c)
    (fun pq hpq ↦ ordered_binary_collision_core_mem g b pq hpq)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro uv huv
  have hu := (Finset.mem_filter.mp huv).2
  have hfilt : (tupleOrderedBinaryCollisions g b).filter (fun pq ↦ c pq=uv)=
      Finset.univ.filter (fun pq : Finset (Fin n) × Finset (Fin n) ↦
        pq.1 \ pq.2=uv.1 ∧ pq.2 \ pq.1=uv.2) := by
    ext pq
    constructor
    · intro hpq
      have hc := (Finset.mem_filter.mp hpq).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst hc,congrArg Prod.snd hc⟩
    · intro hpq
      have hh := (Finset.mem_filter.mp hpq).2
      apply Finset.mem_filter.mpr
      refine ⟨?_,Prod.ext hh.1 hh.2⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · apply Finset.sum_sdiff_eq_sum_sdiff_iff.mp
        rw [hh.1,hh.2]
        exact hu.2.1
      · have h1 := Finset.card_sdiff_add_card_inter pq.1 pq.2
        have h2 := Finset.card_sdiff_add_card_inter pq.2 pq.1
        rw [Finset.inter_comm pq.2 pq.1,hh.2] at h2
        rw [hh.1] at h1
        have := hu.2.2
        omega
  rw [hfilt]
  exact subset_pair_difference_fibre_card uv.1 uv.2 hu.1

/-- Validity makes subset cardinality injective within every shifted
sum fibre, so it orients every distinct binary collision. -/
theorem tuple_subset_fibre_cardinality_injective
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G) :
    Set.InjOn (fun U : Finset (Fin n) ↦ U.card)
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)) := by
  classical
  intro U hU V hV hc
  change U.card=V.card at hc
  apply validTuple_subsetSum_eq_of_card_eq g hg (Function.Embedding.refl _) hc
  have he := (Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm
  simp only [Finset.sum_add_distrib,Finset.sum_const] at he
  rw [hc] at he
  exact add_right_cancel he

/-- Summed actual profile volume is the dyadic support charge of the
original shifted tuple's disjoint relation cores. -/
theorem profile_volume_eq_binary_core_cube_sum
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have hp := twice_ordered_collision_card_eq_fibre_moment
    (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b)) (fun U ↦ U.card)
    (tuple_subset_fibre_cardinality_injective g hg b)
  have hm := twice_profile_volume_eq_intrinsic_fibre_moment L hL g hg E x b hchain
  have he : 2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      2*(tupleOrderedBinaryCollisions g b).card := hm.trans hp.symm
  have hv : (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      (tupleOrderedBinaryCollisions g b).card := by omega
  exact hv.trans (ordered_binary_collision_card_eq_core_cube_sum g b)

/-- When a valid tuple has no triple fibres, its intrinsic loss is exactly
the sum of complementary cube sizes of its actual disjoint relation cores. -/
theorem intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  have hp := twice_ordered_collision_card_eq_fibre_moment
    (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b)) (fun U ↦ U.card)
    (tuple_subset_fibre_cardinality_injective g hg b)
  have hl := finite_map_loss_eq_sum_fibre_excess (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b))
  simp only [Fintype.card_finset,Fintype.card_fin] at hl
  change tupleBinaryCollisionLoss g b=
    ∑ z ∈ tupleBinarySumImage g b,
      ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) at hl
  have he : 2*(tupleOrderedBinaryCollisions g b).card=2*tupleBinaryCollisionLoss g b := by
    rw [hl,Finset.mul_sum]
    apply hp.trans
    apply Finset.sum_congr rfl
    intro z _
    let r := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
    have hr : r ≤ 2 := hcap z
    change r*(r-1)=2*(r-1)
    interval_cases r <;> norm_num
  have hc : (tupleOrderedBinaryCollisions g b).card=tupleBinaryCollisionLoss g b := by omega
  exact hc.symm.trans (ordered_binary_collision_card_eq_core_cube_sum g b)

/-- Small intrinsic loss supplies the no-triple-fibre hypothesis for the
exact dyadic decomposition, with no chosen forest encoding. -/
theorem intrinsic_loss_eq_binary_core_cube_sum_of_small_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (tuple_subset_fibre_card_le_two_of_small_intrinsic_loss g b hsmall)

end MinModulus
