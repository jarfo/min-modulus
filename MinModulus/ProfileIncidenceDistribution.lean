import MinModulus.ProfileIncidenceRanks

namespace MinModulus
open Finset
open scoped Classical

/-- Exact and next-higher incidence levels partition an upper level. -/
theorem finset_card_eq_level_add_card_ge_succ
    {α : Type*} (S : Finset α) (c : α → ℕ) (k : ℕ) :
    (S.filter (fun q ↦ c q=k)).card+(S.filter (fun q ↦ k+1 ≤ c q)).card=
      (S.filter (fun q ↦ k ≤ c q)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s:=S.filter (fun q ↦ k ≤ c q)) (fun q ↦ c q=k)
  have he : (S.filter (fun q ↦ k ≤ c q)).filter (fun q ↦ c q=k)=S.filter (fun q ↦ c q=k) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq,_⟩,he⟩
      exact ⟨hq,he⟩
    · rintro ⟨hq,he⟩
      exact ⟨⟨hq,by omega⟩,he⟩
  have hg : (S.filter (fun q ↦ k ≤ c q)).filter (fun q ↦ ¬ c q=k)=S.filter (fun q ↦ k+1 ≤ c q) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq,hge⟩,hne⟩
      exact ⟨hq,by omega⟩
    · rintro ⟨hq,hge⟩
      exact ⟨⟨hq,by omega⟩,by omega⟩
  rw [he,hg] at h
  exact h

/-- Within each valid actual forest fibre, there is exactly one point
at every incidence level below the fibre size and none at higher levels. -/
theorem forest_fibre_profile_incidence_eq_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) (k : ℕ) :
    ((forestBoxFibre L x z).filter (fun q ↦
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=k)).card=
      if k < (forestBoxFibre L x z).card then 1 else 0 := by
  have h := finset_card_eq_level_add_card_ge_succ (forestBoxFibre L x z)
    (fun q ↦ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card) k
  have hk := forest_fibre_profile_incidence_ge_card L hL g hg E x b hchain z k
  have hs := forest_fibre_profile_incidence_ge_card L hL g hg E x b hchain z (k+1)
  split_ifs <;> omega

/-- The global upper incidence level is the sum of truncated fibre ranks. -/
theorem profile_incidence_ge_card_eq_sum_fibre_ranks
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (k : ℕ) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)).card=
      ∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
        ((forestBoxFibre L x z).card-k) := by
  classical
  let A := Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
    k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)
  have hp := Finset.card_eq_sum_card_fiberwise (s:=A)
    (t:=Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i))
    (f:=fun p ↦ ∑ i, (p i).val • x i)
    (by intro p _; exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
  change A.card=_
  rw [hp]
  apply Finset.sum_congr rfl
  intro z _
  have he : A.filter (fun p ↦ (∑ i, (p i).val • x i)=z)=
      (forestBoxFibre L x z).filter (fun q ↦
        k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card) := by
    ext p
    simp only [A,forestBoxFibre,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [he]
  exact forest_fibre_profile_incidence_ge_card L hL g hg E x b hchain z k

/-- Exactly k profile rectangles contain as many box points as there
are attained fibres larger than k. -/
theorem profile_incidence_eq_card_eq_large_fibre_count
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (k : ℕ) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=k)).card=
      ((Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i)).filter
        (fun z ↦ k < (forestBoxFibre L x z).card)).card := by
  classical
  let A := Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
    ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=k)
  have hp := Finset.card_eq_sum_card_fiberwise (s:=A)
    (t:=Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i))
    (f:=fun p ↦ ∑ i, (p i).val • x i)
    (by intro p _; exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
  change A.card=_
  rw [hp]
  have heach (z : G) : (A.filter (fun p ↦ (∑ i, (p i).val • x i)=z)).card=
      if k < (forestBoxFibre L x z).card then 1 else 0 := by
    have he : A.filter (fun p ↦ (∑ i, (p i).val • x i)=z)=
        (forestBoxFibre L x z).filter (fun q ↦
          ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=k) := by
      ext p
      simp only [A,forestBoxFibre,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    rw [he]
    exact forest_fibre_profile_incidence_eq_card L hL g hg E x b hchain z k
  simp_rw [heach]
  simp

/-- The first upper incidence level counts the exact intrinsic loss. -/
theorem profile_incidence_ge_one_card_eq_intrinsic_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      1 ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)).card=
      tupleBinaryCollisionLoss g b := by
  rw [profile_incidence_ge_card_eq_sum_fibre_ranks L hL g hg E x b hchain 1]
  exact (intrinsic_loss_eq_sum_forest_fibre_excess L g E x b hchain).symm

/-- At the sharp midpoint boundary, exactly 4-k points are covered at
least k times for every incidence level k at least two. -/
theorem profile_incidence_ge_card_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)).card=4-k := by
  classical
  obtain ⟨hf,ho⟩ := forest_boundary_fibre_four_and_other_fibres_le_two L g E x b z hchain hmid hlarge hboundary
  have hz : z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (forestBoxFibre L x z).card)
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
  rw [profile_incidence_ge_card_eq_sum_fibre_ranks L hL g hg E x b hchain k,Finset.sum_eq_single z]
  · rw [hf]
  · intro w _ hw
    have h := ho w hw
    omega
  · exact fun h ↦ (h hz).elim

/-- The sharp midpoint boundary has one point of exact incidence two,
one of exact incidence three, and none of any larger exact incidence. -/
theorem profile_incidence_eq_card_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=k)).card=
      if k < 4 then 1 else 0 := by
  have hp := finset_card_eq_level_add_card_ge_succ Finset.univ
    (fun q : ∀ i, Fin (2^(L i)) ↦ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card) k
  have hh := profile_incidence_ge_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary k hk
  have hs := profile_incidence_ge_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary (k+1) (by omega)
  split_ifs <;> omega

/-- All but two covered points have incidence exactly one at the sharp
midpoint boundary. -/
theorem profile_incidence_one_card_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=1)).card=
      tupleBinaryCollisionLoss g b-2 := by
  have hp := finset_card_eq_level_add_card_ge_succ Finset.univ
    (fun q : ∀ i, Fin (2^(L i)) ↦ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card) 1
  norm_num only at hp
  have h1 := profile_incidence_ge_one_card_eq_intrinsic_loss L hL g hg E x b hchain
  have h2 := profile_incidence_ge_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 2 (by decide)
  omega

end MinModulus
