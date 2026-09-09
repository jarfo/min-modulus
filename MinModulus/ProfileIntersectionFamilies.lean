import MinModulus.ProfileBoundaryIntersections

namespace MinModulus
open Finset
open scoped Classical

/-- A subfamily of at least two sets with singleton pair intersections
has at most one common point, and hence a unique point when attained. -/
theorem exists_unique_common_point_of_pair_intersection_cap
    {α X : Type*} (P Q : Finset α) (R : α → Finset X) (hQP : Q ⊆ P) (hQ : 2 ≤ Q.card)
    (hpair : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → (R a ∩ R b).card ≤ 1)
    (hne : ∃ q, ∀ a ∈ Q, q ∈ R a) : ∃! q, ∀ a ∈ Q, q ∈ R a := by
  classical
  obtain ⟨q,hq⟩ := hne
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  refine ⟨q,hq,?_⟩
  intro r hr
  exact Finset.card_le_one.mp (hpair a (hQP ha) b (hQP hb) hab) _
    (Finset.mem_inter.mpr ⟨hr a ha,hr b hb⟩) _ (Finset.mem_inter.mpr ⟨hq a ha,hq b hb⟩)

/-- Singleton pair intersections make the number of intersecting
k-subfamilies the sum of the binomial incidence counts over actual points. -/
theorem intersecting_subfamily_card_eq_sum_incidence_choose
    {α X : Type*} [Fintype X] (P : Finset α) (R : α → Finset X)
    (hpair : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → (R a ∩ R b).card ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    ((P.powersetCard k).filter (fun Q ↦ ∃ q : X, ∀ a ∈ Q, q ∈ R a)).card=
      ∑ q : X, Nat.choose ((P.filter (fun a ↦ q ∈ R a)).card) k := by
  classical
  let A := fun q : X ↦ (P.filter (fun a ↦ q ∈ R a)).powersetCard k
  have hunion : Finset.univ.biUnion A=(P.powersetCard k).filter (fun Q ↦ ∃ q : X, ∀ a ∈ Q, q ∈ R a) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hQ
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,hcard⟩,q,?_⟩
      · intro a ha
        exact (Finset.mem_filter.mp (hsub ha)).1
      · intro a ha
        exact (Finset.mem_filter.mp (hsub ha)).2
    · intro hQ
      obtain ⟨hQ,⟨q,hq⟩⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hQ
      refine Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,hcard⟩⟩
      intro a ha
      exact Finset.mem_filter.mpr ⟨hsub ha,hq a ha⟩
  have hdis : (↑(Finset.univ : Finset X) : Set X).PairwiseDisjoint A := by
    intro q _ r _ hqr
    apply Finset.disjoint_left.mpr
    intro Q hQ hQ'
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hQ
    obtain ⟨hsub',_⟩ := Finset.mem_powersetCard.mp hQ'
    have hQP : Q ⊆ P := fun a ha ↦ (Finset.mem_filter.mp (hsub ha)).1
    have hq : ∀ a ∈ Q, q ∈ R a := fun a ha ↦ (Finset.mem_filter.mp (hsub ha)).2
    have hr : ∀ a ∈ Q, r ∈ R a := fun a ha ↦ (Finset.mem_filter.mp (hsub' ha)).2
    obtain ⟨s,_,hs⟩ := exists_unique_common_point_of_pair_intersection_cap P Q R hQP (by omega) hpair ⟨q,hq⟩
    exact hqr ((hs q hq).trans (hs r hr).symm)
  rw [← hunion,Finset.card_biUnion hdis]
  simp only [A,Finset.card_powersetCard]

/-- With exactly one point of incidence two and one of incidence three,
all higher binomial incidence sums are determined. -/
theorem sum_incidence_choose_of_two_and_three_levels
    {X : Type*} [Fintype X] (c : X → ℕ) (hcap : ∀ q, c q ≤ 3)
    (h2 : (Finset.univ.filter (fun q ↦ c q=2)).card=1)
    (h3 : (Finset.univ.filter (fun q ↦ c q=3)).card=1) (k : ℕ) (hk : 2 ≤ k) :
    (∑ q, Nat.choose (c q) k)=Nat.choose 2 k+Nat.choose 3 k := by
  classical
  have he (q : X) : Nat.choose (c q) k=
      (if c q=2 then Nat.choose 2 k else 0)+(if c q=3 then Nat.choose 3 k else 0) := by
    have hh := hcap q
    have hc : c q=0 ∨ c q=1 ∨ c q=2 ∨ c q=3 := by omega
    rcases hc with h | h | h | h <;>
      simp [h,Nat.choose_eq_zero_of_lt (by omega : 0 < k),Nat.choose_eq_zero_of_lt (by omega : 1 < k)]
  have hsum2 : (∑ q, if c q=2 then Nat.choose 2 k else 0)=
      (Finset.univ.filter (fun q ↦ c q=2)).card*Nat.choose 2 k := by
    rw [← Finset.sum_filter]
    simp
  have hsum3 : (∑ q, if c q=3 then Nat.choose 3 k else 0)=
      (Finset.univ.filter (fun q ↦ c q=3)).card*Nat.choose 3 k := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [he]
  rw [Finset.sum_add_distrib,hsum2,hsum3,h2,h3]
  simp

/-- Intersecting actual profile subfamilies at the sharp midpoint
boundary have the binomial count contributed by incidences two and three. -/
theorem intersecting_profile_subfamily_card_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (k : ℕ) (hk : 2 ≤ k) :
    (((forestCollisionProfiles n L x).powersetCard k).filter
      (fun Q ↦ ∃ q : ∀ i, Fin (2^(L i)), ∀ w ∈ Q, q ∈ forestProfileLowerBox L w)).card=
      Nat.choose 2 k+Nat.choose 3 k := by
  classical
  have hpair : ∀ w ∈ forestCollisionProfiles n L x, ∀ v ∈ forestCollisionProfiles n L x, w ≠ v →
      (forestProfileLowerBox L w ∩ forestProfileLowerBox L v).card ≤ 1 := by
    intro w hw v hv hne
    exact profile_pair_intersection_card_le_one_at_midpoint_boundary hn L hL g E x b z
      hchain hmid hlarge hboundary w v hw hv hne
  have hcount :
      (((forestCollisionProfiles n L x).powersetCard k).filter
        (fun Q ↦ ∃ q : ∀ i, Fin (2^(L i)), ∀ w ∈ Q, q ∈ forestProfileLowerBox L w)).card=
      ∑ q : ∀ i, Fin (2^(L i)), Nat.choose
        (((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card) k := by
    convert intersecting_subfamily_card_eq_sum_incidence_choose
      (forestCollisionProfiles n L x) (forestProfileLowerBox L) (by
        intro w hw v hv hne
        convert hpair w hw v hv hne using 1
        congr
        exact Subsingleton.elim _ _) k hk using 1
    congr
    apply Finset.sum_congr rfl
    intro q _
    congr
  rw [hcount]
  refine sum_incidence_choose_of_two_and_three_levels _ ?_ ?_ ?_ k hk
  · intro q
    have hzero := profile_incidence_ge_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 4 (by decide)
    by_contra h
    have hp : 0 < (Finset.univ.filter (fun q : ∀ i, Fin (2^(L i)) ↦
        4 ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)).card :=
      Finset.card_pos.mpr ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩⟩
    omega
  · simpa using profile_incidence_eq_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 2 (by decide)
  · simpa using profile_incidence_eq_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 3 (by decide)

/-- Exactly four unordered pairs of actual profiles intersect at the
sharp midpoint boundary. -/
theorem intersecting_profile_pair_card_eq_four_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (((forestCollisionProfiles n L x).powersetCard 2).filter
      (fun Q ↦ ∃ q : ∀ i, Fin (2^(L i)), ∀ w ∈ Q, q ∈ forestProfileLowerBox L w)).card=4 := by
  simpa using intersecting_profile_subfamily_card_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary 2 (by decide)

/-- The sharp midpoint boundary selects a unique actual triple of
profiles sharing a common box point. -/
theorem exists_unique_intersecting_profile_triple_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃! Q : Finset (∀ i, Fin (2*(2^(L i)-1)+1)),
      Q ⊆ forestCollisionProfiles n L x ∧ Q.card=3 ∧
        ∃ q : ∀ i, Fin (2^(L i)), ∀ w ∈ Q, q ∈ forestProfileLowerBox L w := by
  classical
  have hc : (((forestCollisionProfiles n L x).powersetCard 3).filter
      (fun Q ↦ ∃ q : ∀ i, Fin (2^(L i)), ∀ w ∈ Q, q ∈ forestProfileLowerBox L w)).card=1 := by
    simpa using intersecting_profile_subfamily_card_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary 3 (by decide)
  have h := Finset.card_eq_one_iff_existsUnique.mp hc
  simpa only [Finset.mem_filter,Finset.mem_powersetCard,and_assoc] using h

end MinModulus
