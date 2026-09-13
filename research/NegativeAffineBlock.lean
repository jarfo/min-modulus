import MinModulus.TriplingClosure

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A negative affine doubling map on a valid tuple cannot take a
nonfixed coordinate back into its own domain. -/
theorem negative_affine_image_mem_domain_iff_fixed
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (S : Finset (Fin n))
    (f : Fin n → Fin n) (t : G)
    (hd : ∀ i ∈ S, g (f i)+2 • g i=t)
    (i : Fin n) (hi : i ∈ S) : f i ∈ S ↔ f i=i := by
  constructor
  · intro hj
    have he : g (f (f i))+g (f i)=g i+g i := by
      apply add_right_cancel (b := g (f i))
      calc
        _ = g (f (f i))+2 • g (f i) := by rw [two_nsmul]; abel
        _ = t := hd (f i) hj
        _ = g (f i)+2 • g i := (hd i hi).symm
        _ = _ := by rw [two_nsmul]; abel
    rcases pair_sum_eq_or_diagonal_of_validTuple g hg (f (f i)) (f i) i i he with
      (⟨_,h⟩ | ⟨_,h⟩) | ⟨h,_⟩
    · exact h
    · exact h
    · rw [h] at he
      exact validTuple_injective g hg (hinj _ _ he)
  · intro h
    simpa only [h] using hi

/-- Negative affine doubling maps are injective on their domain whenever
doubling is injective and the tuple is valid. -/
theorem negative_affine_map_injOn
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (S : Finset (Fin n))
    (f : Fin n → Fin n) (t : G)
    (hd : ∀ i ∈ S, g (f i)+2 • g i=t) :
    Set.InjOn f S := by
  intro i hi j hj he
  have hsum := (hd i hi).trans (hd j hj).symm
  rw [he] at hsum
  have hh := add_left_cancel hsum
  rw [two_nsmul,two_nsmul] at hh
  exact validTuple_injective g hg (hinj _ _ hh)

/-- The nonfixed part of a negative affine block injects outside the
whole domain. Fixed points remain explicit in this cardinality bound. -/
theorem negative_affine_domain_twice_card_le_add_fixed
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (S : Finset (Fin n))
    (f : Fin n → Fin n) (t : G)
    (hd : ∀ i ∈ S, g (f i)+2 • g i=t) :
    2*S.card ≤ n+(S.filter (fun i ↦ f i=i)).card := by
  classical
  let F := S.filter (fun i ↦ f i=i)
  let T := S \ F
  have hmap : ∀ i ∈ T, f i ∈ (Finset.univ : Finset (Fin n)) \ S := by
    intro i hi
    obtain ⟨hiS,hiF⟩ := Finset.mem_sdiff.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hf
    have he := (negative_affine_image_mem_domain_iff_fixed hinj g hg S f t hd i hiS).mp hf
    exact hiF (Finset.mem_filter.mpr ⟨hiS,he⟩)
  have hcard : T.card ≤ ((Finset.univ : Finset (Fin n)) \ S).card := by
    apply Finset.card_le_card_of_injOn f hmap
    intro i hi j hj he
    exact negative_affine_map_injOn hinj g hg S f t hd
      (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 he
  have hFS : F ⊆ S := Finset.filter_subset _ _
  have hT : T.card=S.card-F.card := Finset.card_sdiff_of_subset hFS
  have hF := Finset.card_le_card hFS
  have hS := Finset.card_le_univ S
  simp only [Fintype.card_fin] at hS
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ,Fintype.card_fin] at hcard
  change 2*S.card ≤ n+F.card
  omega

end MinModulus.Research
