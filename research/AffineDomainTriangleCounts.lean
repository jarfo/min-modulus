import research.PositiveAffinePropagation
import research.CyclicNegativeAffineBlock
import research.LinearBlockTriangleCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The full coordinate domain of positive affine doubling at offset t. -/
noncomputable def positiveAffineDomain
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (t : G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ j, g j+t=2 • g i)

/-- The full coordinate domain of negative affine doubling at offset t. -/
noncomputable def negativeAffineDomain
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (t : G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ j, g j+2 • g i=t)

/-- Two negative affine offsets that both map two distinct coordinates
into the tuple are equal. -/
theorem negative_affine_offsets_eq_of_two_coordinates
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (x y p q r s : Fin n) (hxy : x≠y) (t u : G)
    (hpx : g p+2 • g x=t) (hqx : g q+2 • g x=u)
    (hry : g r+2 • g y=t) (hsy : g s+2 • g y=u) : t=u := by
  have hdiff (a b c : Fin n) (ha : g a+2 • g c=t) (hb : g b+2 • g c=u) :
      g a-g b=t-u := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    rw [← ha,← hb]
    abel
  have hpq := hdiff p q x hpx hqx
  have hrs := hdiff r s y hry hsy
  by_contra htu
  have hpq' : p≠q := by
    intro h
    apply htu
    exact sub_eq_zero.mp (by simpa only [h,sub_self] using hpq.symm)
  obtain ⟨hpr,_⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg p q r s hpq'
    (hpq.trans hrs.symm)
  have hh := hpx.trans hry.symm
  rw [hpr] at hh
  have he := add_left_cancel hh
  exact hxy (validTuple_injective g hg (hinj _ _ (by simpa only [two_nsmul] using he)))

/-- Distinct positive affine offsets give full domains meeting in at
most one coordinate. -/
theorem positive_affine_domains_inter_card_le_one
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (t u : G) (htu : t≠u) :
    (positiveAffineDomain g t ∩ positiveAffineDomain g u).card ≤ 1 := by
  classical
  by_contra hcard
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hcard)
  obtain ⟨hxt,hxu⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyt,hyu⟩ := Finset.mem_inter.mp hy
  obtain ⟨p,hp⟩ : ∃ p, g p+t=2 • g x := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hxt
  obtain ⟨q,hq⟩ : ∃ q, g q+u=2 • g x := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hxu
  obtain ⟨r,hr⟩ : ∃ r, g r+t=2 • g y := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hyt
  obtain ⟨s,hs⟩ : ∃ s, g s+u=2 • g y := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hyu
  exact htu (positive_affine_offsets_eq_of_two_coordinates hinj g hg x y p q r s hxy t u hp hq hr hs)

/-- Distinct negative affine offsets give full domains meeting in at
most one coordinate. -/
theorem negative_affine_domains_inter_card_le_one
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (t u : G) (htu : t≠u) :
    (negativeAffineDomain g t ∩ negativeAffineDomain g u).card ≤ 1 := by
  classical
  by_contra hcard
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hcard)
  obtain ⟨hxt,hxu⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyt,hyu⟩ := Finset.mem_inter.mp hy
  obtain ⟨p,hp⟩ : ∃ p, g p+2 • g x=t := by
    simpa only [negativeAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hxt
  obtain ⟨q,hq⟩ : ∃ q, g q+2 • g x=u := by
    simpa only [negativeAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hxu
  obtain ⟨r,hr⟩ : ∃ r, g r+2 • g y=t := by
    simpa only [negativeAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hyt
  obtain ⟨s,hs⟩ : ∃ s, g s+2 • g y=u := by
    simpa only [negativeAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hyu
  exact htu (negative_affine_offsets_eq_of_two_coordinates hinj g hg x y p q r s hxy t u hp hq hr hs)

/-- Every full negative affine domain of a valid cyclic tuple has at
most floor((n+2)/2) coordinates when doubling is injective. -/
theorem cyclic_negative_affine_full_domain_card_le
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N) :
    (negativeAffineDomain g t).card ≤ (n+2)/2 := by
  classical
  let f : Fin n → Fin n := fun i ↦ if h : ∃ j, g j+2 • g i=t then Classical.choose h else i
  have hf : ∀ i ∈ negativeAffineDomain g t, g (f i)+2 • g i=t := by
    intro i hi
    have h : ∃ j, g j+2 • g i=t := by
      simpa only [negativeAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    dsimp only [f]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hc := cyclic_negative_affine_domain_twice_card_le_add_two hinj g hg
    (negativeAffineDomain g t) f t hf
  omega

/-- For any finite set of positive offsets with domains bounded by M,
the total triangle count of the distinct full domains has the linear
block-family bound. -/
theorem positive_affine_domain_family_triangle_count_le
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (F : Finset G) (M : ℕ)
    (hM : ∀ t ∈ F, (positiveAffineDomain g t).card ≤ M) :
    3*(∑ S ∈ F.image (positiveAffineDomain g), S.card.choose 3) ≤
      (M-2)*n.choose 2 := by
  classical
  apply linear_block_family_sum_choose_three_le
  · intro S hS T hT hST
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hT
    have htu : t≠u := by intro h; subst u; exact hST rfl
    exact positive_affine_domains_inter_card_le_one hinj g hg t u htu
  · intro S hS
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hS
    exact hM t ht

/-- The total triangle count of distinct full negative affine domains
in a cyclic tuple is bounded without a separate largest-domain premise. -/
theorem negative_affine_domain_family_triangle_count_le
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (F : Finset (ZMod N)) :
    6*(∑ S ∈ F.image (negativeAffineDomain g), S.card.choose 3) ≤
      (n-2)*n.choose 2 := by
  classical
  have hF : ∀ S ∈ F.image (negativeAffineDomain g),
      ∀ T ∈ F.image (negativeAffineDomain g), S≠T → (S∩T).card ≤ 1 := by
    intro S hS T hT hST
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hT
    have htu : t≠u := by intro h; subst u; exact hST rfl
    exact negative_affine_domains_inter_card_le_one hinj g hg t u htu
  have hM : ∀ S ∈ F.image (negativeAffineDomain g), S.card ≤ (n+2)/2 := by
    intro S hS
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hS
    exact cyclic_negative_affine_full_domain_card_le hinj g hg t
  have hc := linear_block_family_sum_choose_three_le (F.image (negativeAffineDomain g)) ((n+2)/2) hF hM
  have hscalar : 2*((n+2)/2-2) ≤ n-2 := by omega
  calc
    _ = 2*(3*(∑ S ∈ F.image (negativeAffineDomain g), S.card.choose 3)) := by omega
    _ ≤ 2*(((n+2)/2-2)*n.choose 2) := Nat.mul_le_mul_left 2 hc
    _ = (2*((n+2)/2-2))*n.choose 2 := by rw [Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hscalar

end MinModulus.Research
