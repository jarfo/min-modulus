import MinModulus.LossOneDoublingParts

namespace MinModulus
open Finset
open scoped Classical

/-- A set closed under shifted doubling contains an entire supplied
chain as soon as it contains that chain's first coordinate. -/
theorem whole_chain_mem_of_doubling_closed_set
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (S : Finset (Fin n)) (hclosed : ∀ u ∈ S, ∀ v, 2 • (g u+b)=g v+b → v ∈ S)
    (a : β) (hfirst : E ⟨a,⟨0,hL a⟩⟩ ∈ S) : ∀ j : Fin (L a), E ⟨a,j⟩ ∈ S := by
  have hall : ∀ k (hk : k < L a), E ⟨a,⟨k,hk⟩⟩ ∈ S := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      exact hclosed (E ⟨a,⟨k,by omega⟩⟩) (ih (by omega)) (E ⟨a,⟨k+1,hk⟩⟩) (by
        simp only [hchain,smul_smul,pow_succ,mul_comm])
  intro j
  exact hall j.val j.isLt

/-- A coordinate block made of exactly a selected family of complete
chains has cardinality equal to the sum of those chain lengths. -/
theorem whole_chain_block_card_eq_sum_lengths
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (S : Finset (Fin n)) (J : Finset β)
    (hmem : ∀ a (j : Fin (L a)), E ⟨a,j⟩ ∈ S ↔ a ∈ J) :
    S.card=∑ a ∈ J, L a := by
  classical
  have himage : (J.sigma (fun a ↦ (Finset.univ : Finset (Fin (L a))))).image E=S := by
    ext v
    constructor
    · rintro hv
      obtain ⟨⟨a,j⟩,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (hmem a j).mpr (Finset.mem_sigma.mp hp).1
    · intro hv
      obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective v
      exact Finset.mem_image.mpr ⟨⟨a,j⟩,Finset.mem_sigma.mpr ⟨(hmem a j).mp hv,Finset.mem_univ _⟩,rfl⟩
  rw [← himage,Finset.card_image_of_injective _ E.injective,Finset.card_sigma]
  simp only [Finset.card_univ,Fintype.card_fin]

/-- Boundary whole-chain containment does not require tuple validity:
the balanced blocks contain every supplied chain in its entirety. -/
theorem exists_boundary_whole_chain_blocks_without_validity
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      (∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ S) ∨ (∀ j : Fin (L a), E ⟨a,j⟩ ∈ T)) := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,_,_,hcross⟩ :=
    exists_boundary_balanced_blocks_without_cross_doubling hn g b z hmid hlarge hboundary
  have hclosedS : ∀ u ∈ S, ∀ v, 2 • (g u+b)=g v+b → v ∈ S := by
    intro u hu v he
    have hv : v ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hv
    · exact False.elim ((hcross u hu v hv).1 he)
  have hclosedT : ∀ u ∈ T, ∀ v, 2 • (g u+b)=g v+b → v ∈ T := by
    intro u hu v he
    have hv : v ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hv with hv | hv
    · exact False.elim ((hcross v hv u hu).2 he)
    · exact hv
  refine ⟨S,T,hd,hcover,hsizeS,hsizeT,?_⟩
  intro a
  have hv : E ⟨a,⟨0,hL a⟩⟩ ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
  rcases Finset.mem_union.mp hv with hs | ht
  · exact Or.inl (whole_chain_mem_of_doubling_closed_set L hL g E x b hchain S hclosedS a hs)
  · exact Or.inr (whole_chain_mem_of_doubling_closed_set L hL g E x b hchain T hclosedT a ht)

/-- A block in a partition respected by all chains is exactly the
union of a subfamily of complete chains, as witnessed by its cardinality. -/
theorem exists_chain_subfamily_counting_whole_block
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (S T : Finset (Fin n)) (hd : Disjoint S T)
    (hwhole : ∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ S) ∨ (∀ j : Fin (L a), E ⟨a,j⟩ ∈ T)) :
    ∃ J : Finset β, S.card=∑ a ∈ J, L a := by
  classical
  let J := Finset.univ.filter (fun a ↦ ∀ j : Fin (L a), E ⟨a,j⟩ ∈ S)
  refine ⟨J,whole_chain_block_card_eq_sum_lengths L E S J ?_⟩
  intro a j
  constructor
  · intro hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hwhole a with hs | ht
    · exact hs
    · exact False.elim (Finset.disjoint_left.mp hd hj (ht j))
  · intro ha
    exact (Finset.mem_filter.mp ha).2 j

/-- Sharp midpoint boundary equality requires a subfamily of supplied
positive chains whose lengths sum to the smaller balanced block size. -/
theorem exists_balanced_chain_length_subfamily_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ J : Finset β, (∑ a ∈ J, L a)=n/2 := by
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hwhole⟩ :=
    exists_boundary_whole_chain_blocks_without_validity hn L hL g E x b z hchain hmid hlarge hboundary
  have hdim : S.card+T.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hcover]
    simp
  have hsmall : S.card=n/2 ∨ T.card=n/2 := by omega
  rcases hsmall with hs | ht
  · obtain ⟨J,hJ⟩ := exists_chain_subfamily_counting_whole_block L E S T hd hwhole
    exact ⟨J,hJ.symm.trans hs⟩
  · obtain ⟨J,hJ⟩ := exists_chain_subfamily_counting_whole_block L E T S hd.symm
      (fun a ↦ (hwhole a).symm)
    exact ⟨J,hJ.symm.trans ht⟩

/-- No supplied positive chain at the sharp midpoint boundary can be
longer than the larger balanced block. -/
theorem chain_length_le_balanced_half_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∀ a, L a ≤ n-n/2 := by
  classical
  obtain ⟨J,hJ⟩ := exists_balanced_chain_length_subfamily_at_midpoint_boundary hn L hL g E x b z hchain hmid hlarge hboundary
  have htotal : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hsplit : (∑ a ∈ J, L a)+(∑ a ∈ Finset.univ \ J, L a)=n := by
    convert (Finset.sum_add_sum_compl J L).trans htotal using 1
    congr
  rw [hJ] at hsplit
  intro a
  by_cases ha : a ∈ J
  · have hh := Finset.single_le_sum (f:=L) (fun _ _ ↦ Nat.zero_le _) ha
    omega
  · have hamem : a ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩
    have hh := Finset.single_le_sum (f:=L) (fun _ _ ↦ Nat.zero_le _) hamem
    omega

/-- If the supplied chain lengths admit no balanced subfamily, a large
midpoint fibre forces loss strictly above the balanced threshold.
Neither validity nor cyclicity is required. -/
theorem balanced_threshold_lt_loss_of_no_balanced_chain_subfamily
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hno : ∀ J : Finset β, (∑ a ∈ J, L a) ≠ n/2) :
    2^(n/2)+2^(n-n/2) < tupleBinaryCollisionLoss g b+1 := by
  have hge : 2^(n/2)+2^(n-n/2) ≤ tupleBinaryCollisionLoss g b+1 := by
    by_contra h
    have hc := midpoint_fibre_card_le_two_of_balanced_loss_bound g b z (by omega) hmid
    omega
  have hne : tupleBinaryCollisionLoss g b+1 ≠ 2^(n/2)+2^(n-n/2) := by
    intro he
    obtain ⟨J,hJ⟩ := exists_balanced_chain_length_subfamily_at_midpoint_boundary hn L hL g E x b z hchain hmid hlarge he
    exact hno J hJ
  omega

end MinModulus
