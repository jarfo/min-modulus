import MinModulus.BinaryCoreProfileMap

namespace MinModulus
open Finset
open scoped Classical

/-- Cancelling common original coordinates preserves every actual
binary digit difference. -/
theorem forest_subset_digit_difference_identity
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (P Q : Finset (Fin n)) (a : β) :
    (forestSubsetDigits L E P a).val+(forestSubsetDigits L E (Q \ P) a).val=
      (forestSubsetDigits L E Q a).val+(forestSubsetDigits L E (P \ Q) a).val := by
  classical
  have hd (U V : Finset (Fin n)) : Disjoint (U \ V) (U ∩ V) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  have hP := forest_subset_digits_add_of_disjoint L E (P \ Q) (P ∩ Q) (hd P Q) a
  have hQ := forest_subset_digits_add_of_disjoint L E (Q \ P) (Q ∩ P) (hd Q P) a
  rw [Finset.sdiff_union_inter] at hP hQ
  rw [Finset.inter_comm Q P] at hQ
  omega

/-- A subset pair has a profile's coordinate difference exactly when its
cancelled binary core has that same coordinate difference. -/
theorem profile_coordinate_eq_iff_on_binary_difference
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (P Q : Finset (Fin n))
    (w : ∀ a, Fin (2*(2^(L a)-1)+1)) :
    (∀ a, (forestSubsetDigits L E P a).val+(w a).val=
      2^(L a)-1+(forestSubsetDigits L E Q a).val) ↔
    (∀ a, (forestSubsetDigits L E (P \ Q) a).val+(w a).val=
      2^(L a)-1+(forestSubsetDigits L E (Q \ P) a).val) := by
  constructor <;> intro h a
  all_goals
    have hd := forest_subset_digit_difference_identity L E P Q a
    have ha := h a
    omega

/-- The lower rectangle of a fixed actual profile counts exactly the
ordered original subset collisions with its coordinate difference. -/
theorem profile_lower_box_card_eq_ordered_binary_pair_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (w : ∀ a, Fin (2*(2^(L a)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    (forestProfileLowerBox L w).card=
      ((tupleOrderedBinaryCollisions g b).filter (fun pq ↦
        ∀ a, (forestSubsetDigits L E pq.1 a).val+(w a).val=
          2^(L a)-1+(forestSubsetDigits L E pq.2 a).val)).card := by
  classical
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ a, (2^(L a)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro a _
    have hh := Nat.lt_two_pow_self (n:=L a)
    omega
  symm
  apply Finset.card_bij (fun pq _ ↦ forestSubsetDigits L E pq.2)
  · intro pq hpq
    have hid := (Finset.mem_filter.mp hpq).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro a
    have ha := hid a
    have hb := (forestSubsetDigits L E pq.1 a).isLt
    omega
  · intro pq hpq st hst he
    have hp := (Finset.mem_filter.mp hpq).2
    have hs := (Finset.mem_filter.mp hst).2
    apply Prod.ext
    · apply forest_subset_digits_injective L E
      funext a
      apply Fin.ext
      have hq := congrArg (fun p ↦ (p a).val) he
      have hpa := hp a
      have hsa := hs a
      omega
    · exact forest_subset_digits_injective L E he
  · intro q hq
    obtain ⟨p,⟨hid,he,hlt⟩,_⟩ := exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w hw q hq
    obtain ⟨U,hU⟩ := (forest_subset_digits_bijective L E).2 p
    obtain ⟨V,hV⟩ := (forest_subset_digits_bijective L E).2 q
    have heUV : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)) := by
      rw [← forest_subset_digits_sum_eq L g E x b hchain U,
        ← forest_subset_digits_sum_eq L g E x b hchain V,hU,hV]
      exact he
    have hboundU := forest_subset_digit_weight_bounds L E U
    have hboundV := forest_subset_digit_weight_bounds L E V
    rw [hU] at hboundU
    rw [hV] at hboundV
    have hsmall := (Finset.mem_filter.mp hw).2.1
    have hsum : (∑ a, (p a).val)+(∑ a, (w a).val)=
        (∑ a, (2^(L a)-1))+(∑ a, (q a).val) := by
      simp only [← Finset.sum_add_distrib,hid]
    have hcard : V.card < U.card := by omega
    refine ⟨(U,V),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,heUV,hcard⟩,?_⟩,hV⟩
    simpa only [hU,hV] using hid

/-- Each actual profile rectangle has the sum of the complementary cube
charges of precisely the binary cores with its coordinate difference. -/
theorem profile_lower_box_card_eq_core_charge_sum
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (w : ∀ a, Fin (2*(2^(L a)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    (forestProfileLowerBox L w).card=
      ∑ uv ∈ (tupleBinaryCollisionCores g b).filter (fun uv ↦
        ∀ a, (forestSubsetDigits L E uv.1 a).val+(w a).val=
          2^(L a)-1+(forestSubsetDigits L E uv.2 a).val), 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  let H := fun pq : Finset (Fin n) × Finset (Fin n) ↦
    ∀ a, (forestSubsetDigits L E pq.1 a).val+(w a).val=
      2^(L a)-1+(forestSubsetDigits L E pq.2 a).val
  let S := (tupleOrderedBinaryCollisions g b).filter H
  let T := (tupleBinaryCollisionCores g b).filter H
  let c := fun pq : Finset (Fin n) × Finset (Fin n) ↦ (pq.1 \ pq.2,pq.2 \ pq.1)
  have hmaps : ∀ pq ∈ S, c pq ∈ T := by
    intro pq hpq
    obtain ⟨hord,hid⟩ := Finset.mem_filter.mp hpq
    apply Finset.mem_filter.mpr
    refine ⟨ordered_binary_collision_core_mem g b pq hord,?_⟩
    exact (profile_coordinate_eq_iff_on_binary_difference L E pq.1 pq.2 w).mp hid
  have hpart := Finset.card_eq_sum_card_fiberwise (s:=S) (t:=T) (f:=c) hmaps
  rw [profile_lower_box_card_eq_ordered_binary_pair_card L g E x b hchain w hw]
  change S.card=∑ uv ∈ T, 2^(n-(uv.1 ∪ uv.2).card)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro uv huv
  obtain ⟨hcore,hid⟩ := Finset.mem_filter.mp huv
  have hu := (Finset.mem_filter.mp hcore).2
  have hfilt : S.filter (fun pq ↦ c pq=uv)=
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
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,Prod.ext hh.1 hh.2⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_,?_⟩
        · apply Finset.sum_sdiff_eq_sum_sdiff_iff.mp
          rw [hh.1,hh.2]
          exact hu.2.1
        · have h1 := Finset.card_sdiff_add_card_inter pq.1 pq.2
          have h2 := Finset.card_sdiff_add_card_inter pq.2 pq.1
          rw [Finset.inter_comm pq.2 pq.1,hh.2] at h2
          rw [hh.1] at h1
          have hc := hu.2.2
          omega
      · apply (profile_coordinate_eq_iff_on_binary_difference L E pq.1 pq.2 w).mpr
        rw [hh.1,hh.2]
        exact hid
  rw [hfilt]
  exact subset_pair_difference_fibre_card uv.1 uv.2 hu.1

/-- The boundary core-to-profile bijection makes the rectangle of each
actual core exactly its complementary binary cube charge. -/
theorem boundary_profile_lower_box_card_eq_core_charge
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (uv : tupleBinaryCollisionCores g b) :
    (forestProfileLowerBox L (binaryCoreForestProfile L hL g hg E x b hchain uv).val).card=
      2^(n-(uv.val.1 ∪ uv.val.2).card) := by
  classical
  let w := binaryCoreForestProfile L hL g hg E x b hchain uv
  have hmap := binary_core_forest_profile_bijective_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hfilter : (tupleBinaryCollisionCores g b).filter (fun st ↦
      ∀ a, (forestSubsetDigits L E st.1 a).val+(w.val a).val=
        2^(L a)-1+(forestSubsetDigits L E st.2 a).val)={uv.val} := by
    ext st
    constructor
    · intro hst
      obtain ⟨hc,hid⟩ := Finset.mem_filter.mp hst
      let v : tupleBinaryCollisionCores g b := ⟨st,hc⟩
      have he : binaryCoreForestProfile L hL g hg E x b hchain v=w := by
        apply Subtype.ext
        funext a
        apply Fin.ext
        have hv := binary_core_forest_profile_coordinate_eq L hL g hg E x b hchain v a
        have hw := hid a
        change (forestSubsetDigits L E st.1 a).val+
          ((binaryCoreForestProfile L hL g hg E x b hchain v).val a).val=
            2^(L a)-1+(forestSubsetDigits L E st.2 a).val at hv
        omega
      exact Finset.mem_singleton.mpr (congrArg Subtype.val (hmap.1 he))
    · intro hst
      have he := Finset.mem_singleton.mp hst
      subst st
      exact Finset.mem_filter.mpr ⟨uv.property,binary_core_forest_profile_coordinate_eq L hL g hg E x b hchain uv⟩
  have hc := profile_lower_box_card_eq_core_charge_sum L g E x b hchain w.val w.property
  rw [hfilter,Finset.sum_singleton] at hc
  exact hc

/-- Every actual rectangle at the valid sharp midpoint boundary has
cardinality a power of two with exponent at most the dimension. -/
theorem profile_lower_box_card_is_two_pow_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (w : ∀ a, Fin (2*(2^(L a)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    ∃ k ≤ n, (forestProfileLowerBox L w).card=2^k := by
  classical
  obtain ⟨uv,he⟩ := binary_core_forest_profile_surjective L hL g hg E x b hchain ⟨w,hw⟩
  refine ⟨n-(uv.val.1 ∪ uv.val.2).card,by omega,?_⟩
  have hc := boundary_profile_lower_box_card_eq_core_charge hn L hL g hg E x b z hchain hmid hlarge hboundary uv
  rw [he] at hc
  exact hc

end MinModulus
