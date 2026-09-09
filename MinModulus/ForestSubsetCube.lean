import MinModulus.ProfileCollisionPairs

namespace MinModulus
open Finset
open scoped Classical

/-- Binary weights of a subset of Fin m stay below the full chain width. -/
theorem finset_fin_binary_weight_lt (m : ℕ) (S : Finset (Fin m)) :
    (∑ i ∈ S, 2^i.val) < 2^m := by
  have h := Finset.sum_le_sum_of_subset (Finset.subset_univ S) (f:=fun i : Fin m ↦ 2^i.val)
  have hsum : (∑ i : Fin m, 2^i.val)=2^m-1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_two_pow m
  rw [hsum] at h
  have hp : 0 < 2^m := by positivity
  omega

/-- Distinct subsets of a finite chain have distinct binary weights. -/
theorem finset_fin_binary_weight_injective (m : ℕ) :
    Function.Injective (fun S : Finset (Fin m) ↦ ∑ i ∈ S, 2^i.val) := by
  classical
  intro S T h
  have hmap : S.image Fin.val=T.image Fin.val := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
    simpa only [Finset.sum_image,Fin.val_injective.injOn] using h
  exact Finset.image_injective Fin.val_injective hmap

/-- Every complete affine chain forest is exactly the binary subset cube
of the shifted original coordinates, including its full multiplicities. -/
theorem exists_subset_forest_box_equiv
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    ∃ e : Finset (Fin n) ≃ (∀ a, Fin (2^(L a))),
      ∀ S, (∑ a, (e S a).val • x a)=∑ i ∈ S, (g i+b) := by
  classical
  let part := fun (S : Finset (Fin n)) a ↦ Finset.univ.filter (fun i : Fin (L a) ↦ E ⟨a,i⟩ ∈ S)
  let f : Finset (Fin n) → (∀ a, Fin (2^(L a))) := fun S a ↦
    ⟨∑ i ∈ part S a, 2^i.val,finset_fin_binary_weight_lt (L a) (part S a)⟩
  have hf : Function.Injective f := by
    intro S T he
    have hpart : ∀ a, part S a=part T a := by
      intro a
      apply finset_fin_binary_weight_injective (L a)
      exact congrArg (fun p ↦ (p a).val) he
    ext v
    obtain ⟨⟨a,i⟩,rfl⟩ := E.surjective v
    have h := Finset.ext_iff.mp (hpart a) i
    simpa only [part,Finset.mem_filter,Finset.mem_univ,true_and] using h
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hcard : Fintype.card (Finset (Fin n))=Fintype.card (∀ a, Fin (2^(L a))) := by
    simp only [Fintype.card_finset,Fintype.card_fin,Fintype.card_pi,Finset.prod_pow_eq_pow_sum,hsize]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩)
  refine ⟨e,?_⟩
  intro S
  change (∑ a, (∑ i ∈ part S a, 2^i.val) • x a)=_
  calc
    _=∑ a, ∑ i ∈ part S a, (g (E ⟨a,i⟩)+b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_nsmul_assoc]
      exact Finset.sum_congr rfl (fun i _ ↦ (hchain a i).symm)
    _=∑ t : (Σ a : β, Fin (L a)), if E t ∈ S then g (E t)+b else 0 := by
      rw [Fintype.sum_sigma]
      simp only [part,Finset.sum_filter]
    _=∑ v : Fin n, if v ∈ S then g v+b else 0 := E.sum_comp (fun v ↦ if v ∈ S then g v+b else 0)
    _=∑ i ∈ S, (g i+b) := by simp

/-- All binary subset sums of the tuple after a fixed translation. -/
noncomputable def tupleBinarySumImage
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : Finset G :=
  Finset.univ.image (fun S : Finset (Fin n) ↦ ∑ i ∈ S, (g i+b))

/-- The exact loss of distinct shifted subset sums, independent of any
choice of complete chain forest. -/
noncomputable def tupleBinaryCollisionLoss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : ℕ :=
  2^n-(tupleBinarySumImage g b).card

/-- The intrinsic image and loss partition the full subset cube. -/
theorem tuple_binary_image_card_add_loss_eq_two_pow
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    (tupleBinarySumImage g b).card+tupleBinaryCollisionLoss g b=2^n := by
  classical
  have h : (tupleBinarySumImage g b).card ≤ 2^n := by
    simpa only [tupleBinarySumImage,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
      using Finset.card_image_le (s:=Finset.univ) (f:=fun S : Finset (Fin n) ↦ ∑ i ∈ S, (g i+b))
  exact Nat.add_sub_of_le h

/-- A complete forest has exactly the intrinsic shifted subset-sum image. -/
theorem forest_box_image_eq_tuple_binary_image
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    Finset.univ.image (fun p : (∀ a, Fin (2^(L a))) ↦ ∑ a, (p a).val • x a)=
      tupleBinarySumImage g b := by
  classical
  obtain ⟨e,he⟩ := exists_subset_forest_box_equiv L g E x b hchain
  ext z
  constructor
  · intro hz
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨e.symm p,Finset.mem_univ _,?_⟩
    simpa only [Equiv.apply_symm_apply] using (he (e.symm p)).symm
  · intro hz
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨e S,Finset.mem_univ _,he S⟩

/-- Actual profile-union loss is intrinsic: every positive complete chain
forest of the same valid tuple at the same shift has this identical loss. -/
theorem forest_collision_loss_eq_tuple_binary_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    forestCollisionLoss n L x=tupleBinaryCollisionLoss g b := by
  have h := forest_box_image_card_add_collision_loss_eq_two_pow L hL g hg E x b hchain
  rw [forest_box_image_eq_tuple_binary_image L g E x b hchain] at h
  have ht := tuple_binary_image_card_add_loss_eq_two_pow g b
  omega

end MinModulus
