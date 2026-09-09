import MinModulus.BoundaryCoreSupportCounts

namespace MinModulus
open Finset
open scoped Classical

/-- Counting a weight value can be split over any finite set of levels
containing all level values attained by the source. -/
theorem filter_card_eq_sum_level_counts
    {α X Y : Type*} (S : Finset α) (T : Finset X) (level : α → X) (weight : X → Y)
    (hlevel : ∀ a ∈ S, level a ∈ T) (k : Y) :
    (S.filter (fun a ↦ weight (level a)=k)).card=
      ∑ t ∈ T, if weight t=k then (S.filter (fun a ↦ level a=t)).card else 0 := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s:=S.filter (fun a ↦ weight (level a)=k)) (t:=T) (f:=level) (by
      intro a ha
      exact hlevel a (Finset.mem_filter.mp ha).1)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : weight t=k
  · rw [if_pos ht]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha,_⟩,he⟩
      exact ⟨ha,he⟩
    · rintro ⟨ha,he⟩
      exact ⟨⟨ha,by rw [he,ht]⟩,he⟩
  · rw [if_neg ht]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha he
    have hh := (Finset.mem_filter.mp ha).2
    rw [he] at hh
    exact ht hh

/-- A bijection of finite families preserving weights preserves every
weight multiplicity, expressed on the original finite sets. -/
theorem card_filter_eq_of_bijective_weight
    {α β Y : Type*} (P : Finset α) (Q : Finset β) (f : P → Q) (hf : Function.Bijective f)
    (a : α → Y) (b : β → Y) (hweight : ∀ p : P, b (f p).val=a p.val) (k : Y) :
    (Q.filter (fun q ↦ b q=k)).card=(P.filter (fun p ↦ a p=k)).card := by
  classical
  have hs := (Equiv.ofBijective f hf).sum_comp (fun q : Q ↦ if b q.val=k then (1 : ℕ) else 0)
  change (∑ p : P, if b (f p).val=k then (1 : ℕ) else 0)=
    ∑ q : Q, if b q.val=k then (1 : ℕ) else 0 at hs
  simp_rw [hweight] at hs
  rw [Finset.sum_coe_sort P (fun p ↦ if a p=k then (1 : ℕ) else 0),
    Finset.sum_coe_sort Q (fun q ↦ if b q=k then (1 : ℕ) else 0)] at hs
  simpa using hs.symm

/-- The boundary bijection identifies every rectangle-size multiplicity
with the multiplicity of the corresponding actual core cube charge. -/
theorem boundary_rectangle_card_count_eq_core_charge_count
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) :
    ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card=k)).card=
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ 2^(n-(uv.1 ∪ uv.2).card)=k)).card := by
  classical
  have hh := card_filter_eq_of_bijective_weight (tupleBinaryCollisionCores g b) (forestCollisionProfiles n L x)
    (binaryCoreForestProfile L hL g hg E x b hchain)
    (binary_core_forest_profile_bijective_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary)
    (fun uv ↦ 2^(n-(uv.1 ∪ uv.2).card)) (fun w ↦ (forestProfileLowerBox L w).card)
    (by
      intro uv
      exact boundary_profile_lower_box_card_eq_core_charge hn L hL g hg E x b z hchain hmid hlarge hboundary uv) k
  convert hh using 1 <;> congr

/-- The four boundary core charges have the exact multiplicity pattern
one, one, and the two balanced complementary cube sizes. -/
theorem boundary_binary_core_charge_count
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ 2^(n-(uv.1 ∪ uv.2).card)=k)).card=
      (if k=1 then 2 else 0)+(if k=2^(n/2) then 1 else 0)+(if k=2^(n-n/2) then 1 else 0) := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hcS,hcT,hfull,hclass⟩ :=
    exists_boundary_binary_core_support_distribution hn g hg b z hmid hlarge hboundary
  have hdim : S.card+T.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hcover]
    simp
  have hSne : S ≠ Finset.univ := by
    intro he
    rw [he] at hcS
    omega
  have hTne : T ≠ Finset.univ := by
    intro he
    rw [he] at hcT
    omega
  have hST : S ≠ T := by
    intro he
    have hh : S=∅ := (Finset.disjoint_self_iff_empty S).mp (by simpa only [← he] using hd)
    have hc : S.card=0 := by rw [hh]; simp
    omega
  have hp := filter_card_eq_sum_level_counts (tupleBinaryCollisionCores g b)
    ({S,T,Finset.univ} : Finset (Finset (Fin n))) (fun uv ↦ uv.1 ∪ uv.2)
    (fun A : Finset (Fin n) ↦ 2^(n-A.card)) (by
      intro uv huv
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hclass uv huv) k
  simp only [Finset.sum_insert (by simp [hST,hSne] : S ∉ ({T,Finset.univ} : Finset (Finset (Fin n)))),
    Finset.sum_insert (by simpa using hTne : T ∉ ({Finset.univ} : Finset (Finset (Fin n)))),
    Finset.sum_singleton,Finset.card_univ,Fintype.card_fin,Nat.sub_self,pow_zero] at hp
  have hp' : ((tupleBinaryCollisionCores g b).filter (fun uv ↦ 2^(n-(uv.1 ∪ uv.2).card)=k)).card=
      (if 2^(n-S.card)=k then ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=S)).card else 0)+
      ((if 2^(n-T.card)=k then ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=T)).card else 0)+
      (if 1=k then ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card else 0)) := by
    convert hp using 1 <;> congr
  rw [hcS,hcT,hfull] at hp'
  have hcompS : n-S.card=T.card := by omega
  have hcompT : n-T.card=S.card := by omega
  rw [hcompS,hcompT] at hp'
  have hsizes : (S.card=n/2 ∧ T.card=n-n/2) ∨ (S.card=n-n/2 ∧ T.card=n/2) := by omega
  rcases hsizes with ⟨hS,hT⟩ | ⟨hS,hT⟩
  · rw [hS,hT] at hp'
    simpa only [eq_comm,add_comm,add_left_comm,add_assoc] using hp'
  · rw [hS,hT] at hp'
    simpa only [eq_comm,add_comm,add_left_comm,add_assoc] using hp'

/-- Every valid positive boundary forest has the exact rectangle-size
multiset one, one, and the two balanced powers of two. Equal large sizes
in even dimension contribute twice to the same multiplicity. -/
theorem boundary_profile_rectangle_card_count
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) :
    ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card=k)).card=
      (if k=1 then 2 else 0)+(if k=2^(n/2) then 1 else 0)+(if k=2^(n-n/2) then 1 else 0) := by
  rw [boundary_rectangle_card_count_eq_core_charge_count hn L hL g hg E x b z hchain hmid hlarge hboundary,
    boundary_binary_core_charge_count hn g hg b z hmid hlarge hboundary]

/-- Exactly two actual profile rectangles are singletons at the valid
sharp midpoint boundary. -/
theorem boundary_singleton_profile_rectangle_card_eq_two
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card=1)).card=2 := by
  have hc := boundary_profile_rectangle_card_count hn L hL g hg E x b z hchain hmid hlarge hboundary 1
  have hpow1 : 1 < (2 : ℕ)^(n/2) := Nat.one_lt_pow (by omega) (by decide)
  have hpow2 : 1 < (2 : ℕ)^(n-n/2) := Nat.one_lt_pow (by omega) (by decide)
  have hne1 : 1 ≠ (2 : ℕ)^(n/2) := by omega
  have hne2 : 1 ≠ (2 : ℕ)^(n-n/2) := by omega
  simpa [hne1,hne2] using hc

/-- The remaining two actual boundary rectangles have non-singleton
balanced power-of-two sizes. -/
theorem boundary_nonsingleton_profile_rectangle_card_eq_two
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card ≠ 1)).card=2 := by
  classical
  have htotal := profile_card_eq_four_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hone := boundary_singleton_profile_rectangle_card_eq_two hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hpart := Finset.card_filter_add_card_filter_not (s:=forestCollisionProfiles n L x)
    (fun w ↦ (forestProfileLowerBox L w).card=1)
  have hpart' : ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card=1)).card+
      ((forestCollisionProfiles n L x).filter (fun w ↦ (forestProfileLowerBox L w).card ≠ 1)).card=
      (forestCollisionProfiles n L x).card := by
    convert hpart using 1
  rw [hone,htotal] at hpart'
  omega

end MinModulus
