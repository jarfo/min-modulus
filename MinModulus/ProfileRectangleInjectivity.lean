import MinModulus.BoundaryRectangleDistribution
import MinModulus.BoundaryProfileIncidencePattern

namespace MinModulus
open Finset
open scoped Classical

/-- Every bounded profile rectangle contains its two coordinate extrema. -/
theorem exists_profile_lower_box_extreme_points
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    ∃ q r : ∀ i, Fin (2^(L i)), q ∈ forestProfileLowerBox L w ∧
      r ∈ forestProfileLowerBox L w ∧
      (∀ i, (q i).val=(w i).val-(2^(L i)-1)) ∧
      (∀ i, (r i).val=min (2^(L i)-1) (w i).val) := by
  classical
  let q : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨(w i).val-(2^(L i)-1),by
    have := (w i).isLt
    have : 0 < 2^(L i) := by positivity
    omega⟩
  let r : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨min (2^(L i)-1) (w i).val,by
    have : 0 < 2^(L i) := by positivity
    omega⟩
  refine ⟨q,r,?_,?_,fun _ ↦ rfl,fun _ ↦ rfl⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun i ↦ ?_⟩
    have := (w i).isLt
    dsimp only [q]
    omega
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun i ↦ ?_⟩
    have := (w i).isLt
    dsimp only [r]
    omega

/-- The coordinate rectangle determines the entire bounded profile,
without any tuple validity, evaluation, or smallness hypothesis. -/
theorem forest_profile_lower_box_injective
    {β : Type*} [Fintype β] (L : β → ℕ) :
    Function.Injective (forestProfileLowerBox L) := by
  intro w v he
  obtain ⟨q,r,hq,hr,hqval,hrval⟩ := exists_profile_lower_box_extreme_points L w
  obtain ⟨s,t,hs,ht,hsval,htval⟩ := exists_profile_lower_box_extreme_points L v
  have hqv := hq
  have hrv := hr
  have hsw := hs
  have htw := ht
  rw [he] at hqv hrv
  rw [← he] at hsw htw
  funext i
  apply Fin.ext
  have hqvi := (Finset.mem_filter.mp hqv).2 i
  have hrvi := (Finset.mem_filter.mp hrv).2 i
  have hswi := (Finset.mem_filter.mp hsw).2 i
  have htwi := (Finset.mem_filter.mp htw).2 i
  rw [hqval] at hqvi
  rw [hrval] at hrvi
  rw [hsval] at hswi
  rw [htval] at htwi
  omega

/-- A singleton rectangle forces the profile to be twice its only box
point in every coordinate. -/
theorem singleton_profile_lower_box_coordinate_eq_double
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hcard : (forestProfileLowerBox L w).card=1)
    (q : ∀ i, Fin (2^(L i))) (hq : q ∈ forestProfileLowerBox L w) :
    ∀ i, (w i).val=2*(q i).val := by
  obtain ⟨s,t,hs,ht,hsval,htval⟩ := exists_profile_lower_box_extreme_points L w
  have hsq : s=q := Finset.card_le_one.mp hcard.le _ hs _ hq
  have htq : t=q := Finset.card_le_one.mp hcard.le _ ht _ hq
  intro i
  have hsi := hsval i
  have hti := htval i
  rw [hsq] at hsi
  rw [htq] at hti
  omega

/-- Two singleton rectangles containing the same point have the same
profile. -/
theorem singleton_profile_lower_box_unique_at_point
    {β : Type*} [Fintype β] (L : β → ℕ) (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : (forestProfileLowerBox L w).card=1) (hv : (forestProfileLowerBox L v).card=1)
    (q : ∀ i, Fin (2^(L i))) (hqw : q ∈ forestProfileLowerBox L w)
    (hqv : q ∈ forestProfileLowerBox L v) : w=v := by
  have hh := singleton_profile_lower_box_coordinate_eq_double L w hw q hqw
  have hi := singleton_profile_lower_box_coordinate_eq_double L v hv q hqv
  funext i
  apply Fin.ext
  exact (hh i).trans (hi i).symm

/-- For an injective family covering two points, two singleton members
must occur once at each point. -/
theorem singleton_members_at_two_covering_points
    {α X : Type*} (P : Finset α) (R : α → Finset X) (hR : Function.Injective R)
    (q r : X) (hcover : ∀ a ∈ P, q ∈ R a ∨ r ∈ R a)
    (htwo : (P.filter (fun a ↦ (R a).card=1)).card=2) :
    (∃! a, a ∈ P ∧ R a={q}) ∧ (∃! a, a ∈ P ∧ R a={r}) := by
  classical
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (P.filter (fun a ↦ (R a).card=1)).card)
  obtain ⟨haP,hac⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP,hbc⟩ := Finset.mem_filter.mp hb
  have singleton (a : α) (hc : (R a).card=1) (s : X) (hs : s ∈ R a) : R a={s} := by
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hs,fun t ht ↦ Finset.card_le_one.mp hc.le _ ht _ hs⟩
  have unique (a : α) (ha : a ∈ P) (s : X) (he : R a={s}) : ∃! b, b ∈ P ∧ R b={s} := by
    refine ⟨a,⟨ha,he⟩,?_⟩
    intro b hb
    exact hR (hb.2.trans he.symm)
  rcases hcover a haP with haq | har <;> rcases hcover b hbP with hbq | hbr
  · exact False.elim (hab (hR ((singleton a hac q haq).trans (singleton b hbc q hbq).symm)))
  · exact ⟨unique a haP q (singleton a hac q haq),unique b hbP r (singleton b hbc r hbr)⟩
  · exact ⟨unique b hbP q (singleton b hbc q hbq),unique a haP r (singleton a hac r har)⟩
  · exact False.elim (hab (hR ((singleton a hac r har).trans (singleton b hbc r hbr).symm)))

/-- The two singleton boundary rectangles occur at the distinct points
of incidence three and two, with a unique profile at each point. -/
theorem exists_boundary_singleton_rectangle_locations
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ q r : ∀ i, Fin (2^(L i)), q ≠ r ∧
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=3 ∧
      ((forestCollisionProfiles n L x).filter (fun w ↦ r ∈ forestProfileLowerBox L w)).card=2 ∧
      (∃! w, w ∈ forestCollisionProfiles n L x ∧ forestProfileLowerBox L w={q}) ∧
      (∃! w, w ∈ forestCollisionProfiles n L x ∧ forestProfileLowerBox L w={r}) := by
  classical
  obtain ⟨q,r,hqr,hA,hB,_,hcover,_,_,_⟩ :=
    exists_boundary_profile_incidence_partition hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hcover' : ∀ w ∈ forestCollisionProfiles n L x,
      q ∈ forestProfileLowerBox L w ∨ r ∈ forestProfileLowerBox L w := by
    intro w hw
    rw [← hcover] at hw
    rcases Finset.mem_union.mp hw with hq | hr
    · exact Or.inl (Finset.mem_filter.mp hq).2
    · exact Or.inr (Finset.mem_filter.mp hr).2
  have hsingle := singleton_members_at_two_covering_points (forestCollisionProfiles n L x)
    (forestProfileLowerBox L) (forest_profile_lower_box_injective L) q r hcover'
    (by
      convert boundary_singleton_profile_rectangle_card_eq_two hn L hL g hg E x b z hchain hmid hlarge hboundary using 1)
  refine ⟨q,r,hqr,hA,hB,?_,?_⟩
  · convert hsingle.1 using 1
  · convert hsingle.2 using 1

end MinModulus
