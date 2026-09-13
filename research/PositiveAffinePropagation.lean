import research.QuadraticTranslateRigidity
import MinModulus.TriplingClosure

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- In an indexed two-coin family with one coordinate varying injectively,
a fixed translated coordinate can occur at most twice. -/
theorem two_coin_family_fibre_card_le_two
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (S : Finset (Fin n))
    (p f q : Fin n → Fin n) (t : G) (hfi : Set.InjOn f S)
    (he : ∀ i ∈ S, g (p i)+g (f i)=g (q i)+t) (j : Fin n) :
    (S.filter (fun i ↦ q i=j)).card ≤ 2 := by
  classical
  let H := S.filter (fun i ↦ q i=j)
  by_cases hH : H.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hH
    have hi₀S := (Finset.mem_filter.mp hi₀).1
    have hi₀q := (Finset.mem_filter.mp hi₀).2
    have hmap : ∀ i ∈ H, f i ∈ ({p i₀,f i₀} : Finset (Fin n)) := by
      intro i hi
      obtain ⟨hiS,hiq⟩ := Finset.mem_filter.mp hi
      have hsum : g (p i)+g (f i)=g (p i₀)+g (f i₀) := by
        rw [he i hiS,he i₀ hi₀S,hiq,hi₀q]
      rcases pair_sum_eq_or_diagonal_of_validTuple g hg (p i) (f i) (p i₀) (f i₀) hsum with
        (⟨_,h⟩ | ⟨_,h⟩) | ⟨ha,hb⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr h
      · simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inl h
      · rw [ha,hb] at hsum
        have h := validTuple_injective g hg (hinj _ _ hsum)
        simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr h
    have hcard := Finset.card_le_card_of_injOn f hmap
      (fun i hi j hj hij ↦ hfi (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij)
    exact hcard.trans Finset.card_le_two
  · have hz : H=∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    change H.card ≤ 2
    simp only [hz,Finset.card_empty,Nat.zero_le]

/-- Two positive affine offsets that both map two distinct coordinates
into the tuple must coincide. -/
theorem positive_affine_offsets_eq_of_two_coordinates
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (x y p q r s : Fin n) (hxy : x ≠ y) (t u : G)
    (hpx : g p+t=2 • g x) (hqx : g q+u=2 • g x)
    (hry : g r+t=2 • g y) (hsy : g s+u=2 • g y) : t=u := by
  have hdiff (a b c : Fin n) (ha : g a+t=2 • g c) (hb : g b+u=2 • g c) :
      g a-g b=u-t := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using ha.trans hb.symm
  have hpq := hdiff p q x hpx hqx
  have hrs := hdiff r s y hry hsy
  by_contra htu
  have hpq' : p ≠ q := by
    intro h
    have hh : u=t := sub_eq_zero.mp (by simpa only [h,sub_self] using hpq.symm)
    exact htu hh.symm
  obtain ⟨hpr,_⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg p q r s hpq'
    (hpq.trans hrs.symm)
  have he : 2 • g x=2 • g y := by
    rw [← hpx,← hry,hpr]
  apply hxy
  apply validTuple_injective g hg
  apply hinj
  simpa only [two_nsmul] using he

/-- Seven represented neighbors of a coordinate outside a positive
affine extension force a new positive affine map on their images. -/
theorem positive_affine_neighbor_propagation
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S : Finset (Fin n))
    (hS : 7 ≤ S.card) (f p q : Fin n → Fin n) (t : ZMod N) (a : Fin n)
    (hf : ∀ i ∈ S, g (f i)+t=2 • g i)
    (hout : ∀ j, 2 • g a-t ≠ g j)
    (hd : ∀ i ∈ S, 2 • (g a-g i)=g (p i)-g (q i)) :
    ∀ i ∈ S, g (q i)+(2 • g a-t)=2 • g (f i) := by
  classical
  let h := 2 • g a-t
  have hfi : Set.InjOn f S := by
    intro i hi j hj he
    have hh := (hf i hi).symm.trans (by simpa only [he] using hf j hj)
    exact validTuple_injective g hg (hinj _ _ (by simpa only [two_nsmul] using hh))
  have hv (i : Fin n) (hi : i ∈ S) : g (p i)+g (f i)=g (q i)+h := by
    have hi' := hf i hi
    have hr := hd i hi
    dsimp only [h]
    simp only [nsmul_eq_mul,Nat.cast_ofNat] at hi' hr ⊢
    linear_combination hi' - hr
  have hcount : S.card ≤ 2*(S.image q).card :=
    Finset.card_le_mul_card_image S 2 (fun j _ ↦
      two_coin_family_fibre_card_le_two hinj g hg S p f q h hfi hv j)
  have hmem (i : Fin n) (hi : i ∈ S) : g (q i)+h ∈ actualFibreCoinCover g 2 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,p i ::ₘ ({f i} : Multiset (Fin n)),by simp,?_⟩
    simpa only [Multiset.map_cons,Multiset.map_singleton,Multiset.sum_cons,
      Multiset.sum_singleton] using hv i hi
  have hsub : S.image q ⊆ quadraticTranslateHits g h := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem i hi⟩
  have hfour : 4 ≤ (quadraticTranslateHits g h).card := by
    have hc := Finset.card_le_card hsub
    omega
  intro i hi
  obtain ⟨b,hb⟩ := quadratic_translate_hit_is_double_of_four_hits g hg h hout hfour
    (q i) (hmem i hi)
  have he : g (p i)+g (f i)=g b+g b := by
    simpa only [two_nsmul] using (hv i hi).trans hb
  have hpf : p i=f i := by
    by_contra hn
    rcases pair_sum_eq_of_validTuple g hg (p i) (f i) b b hn he with hh | hh
    · exact hn (hh.1.trans hh.2.symm)
    · exact hn (hh.1.trans hh.2.symm)
  have hh := (hv i hi).symm
  simpa only [h,hpf,two_nsmul] using hh

/-- Two distinct outside coordinates with seven represented neighbors
in a positive affine domain have at most one common neighbor there. -/
theorem positive_affine_rich_neighbor_intersection_card_le_one
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S A B : Finset (Fin n))
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hA : 7 ≤ A.card) (hB : 7 ≤ B.card)
    (f p q r s : Fin n → Fin n) (t : ZMod N) (a b : Fin n) (hab : a ≠ b)
    (hf : ∀ i ∈ S, g (f i)+t=2 • g i)
    (haout : ∀ j, 2 • g a-t ≠ g j) (hbout : ∀ j, 2 • g b-t ≠ g j)
    (hda : ∀ i ∈ A, 2 • (g a-g i)=g (p i)-g (q i))
    (hdb : ∀ i ∈ B, 2 • (g b-g i)=g (r i)-g (s i)) :
    (A ∩ B).card ≤ 1 := by
  have hpa := positive_affine_neighbor_propagation hinj g hg A hA f p q t a
    (fun i hi ↦ hf i (hAS hi)) haout hda
  have hpb := positive_affine_neighbor_propagation hinj g hg B hB f r s t b
    (fun i hi ↦ hf i (hBS hi)) hbout hdb
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiA,hiB⟩ := Finset.mem_inter.mp hi
  obtain ⟨hjA,hjB⟩ := Finset.mem_inter.mp hj
  by_contra hij
  have hfij : f i ≠ f j := by
    intro he
    have hh := (hf i (hAS hiA)).symm.trans (by simpa only [he] using hf j (hAS hjA))
    exact hij (validTuple_injective g hg (hinj _ _ (by simpa only [two_nsmul] using hh)))
  have ho := positive_affine_offsets_eq_of_two_coordinates hinj g hg (f i) (f j)
    (q i) (s i) (q j) (s j) hfij (2 • g a-t) (2 • g b-t)
    (hpa i hiA) (hpb i hiB) (hpa j hjA) (hpb j hjB)
  have he : g a+g a=g b+g b := by
    simpa only [sub_add_cancel,two_nsmul] using congrArg (fun z ↦ z+t) ho
  exact hab (validTuple_injective g hg (hinj _ _ he))

/-- A rich outside neighbor set and its original positive affine domain
have total cardinality at most n+1. This limits neighbors of large domains. -/
theorem positive_affine_rich_neighbors_add_domain_card_le
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S A : Finset (Fin n))
    (hAS : A ⊆ S) (hA : 7 ≤ A.card) (f p q : Fin n → Fin n)
    (t : ZMod N) (a : Fin n)
    (hf : ∀ i ∈ S, g (f i)+t=2 • g i)
    (hout : ∀ j, 2 • g a-t ≠ g j)
    (hd : ∀ i ∈ A, 2 • (g a-g i)=g (p i)-g (q i)) :
    A.card+S.card ≤ n+1 := by
  classical
  have hp := positive_affine_neighbor_propagation hinj g hg A hA f p q t a
    (fun i hi ↦ hf i (hAS hi)) hout hd
  have hfi : Set.InjOn f A := by
    intro i hi j hj he
    have hh := (hf i (hAS hi)).symm.trans (by simpa only [he] using hf j (hAS hj))
    exact validTuple_injective g hg (hinj _ _ (by simpa only [two_nsmul] using hh))
  have hsmall : ((A.image f) ∩ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxI,hxS⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyI,hyS⟩ := Finset.mem_inter.mp hy
    obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hxI
    obtain ⟨j,hj,hjy⟩ := Finset.mem_image.mp hyI
    by_contra hxy
    have hpix : g (q i)+(2 • g a-t)=2 • g x := by simpa only [hix] using hp i hi
    have hpjy : g (q j)+(2 • g a-t)=2 • g y := by simpa only [hjy] using hp j hj
    have ho := positive_affine_offsets_eq_of_two_coordinates hinj g hg x y
      (f x) (q i) (f y) (q j) hxy t (2 • g a-t)
      (hf x hxS) hpix (hf y hyS) hpjy
    have hh : t+t=g a+g a := by
      simpa only [sub_add_cancel,two_nsmul] using congrArg (fun z ↦ z+t) ho
    have hta : t=g a := hinj _ _ hh
    apply hout a
    simpa only [hta,two_nsmul,add_sub_cancel_right] using ho.symm
  have hc := Finset.card_union_add_card_inter (A.image f) S
  have hu := Finset.card_le_univ ((A.image f) ∪ S)
  simp only [Fintype.card_fin] at hu
  rw [Finset.card_image_of_injOn hfi] at hc
  omega

end MinModulus.Research
