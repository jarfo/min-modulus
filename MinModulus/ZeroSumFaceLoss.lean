import MinModulus.IntrinsicFibreLoss

namespace MinModulus
open Finset
open scoped Classical

/-- If every point has a retained representative with the same image,
the removed points provide a lower bound on collision loss in every target
predicate. No injectivity of the retained map is needed. -/
theorem image_filter_card_add_discarded_le
    {α G : Type*} [Fintype α] (f : α → G) (D : Finset α)
    (hsurj : ∀ a, ∃ b, b ∉ D ∧ f b=f a) (P : G → Prop) :
    ((Finset.univ.image f).filter P).card+(D.filter (fun a ↦ P (f a))).card ≤
      (Finset.univ.filter (fun a ↦ P (f a))).card := by
  classical
  let S := Finset.univ.filter (fun a ↦ P (f a))
  let R := S.filter (fun a ↦ a ∉ D)
  have himage : R.image f=(Finset.univ.image f).filter P := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      have haP := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,haP⟩
    · intro hz
      obtain ⟨ha,hP⟩ := Finset.mem_filter.mp hz
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b,hb,hbe⟩ := hsurj a
      refine Finset.mem_image.mpr ⟨b,?_,hbe⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [hbe]⟩,hb⟩
  have hcard : ((Finset.univ.image f).filter P).card ≤ R.card := by
    rw [← himage]
    exact Finset.card_image_le
  have hpart := Finset.card_filter_add_card_filter_not (s:=S) (fun a ↦ a ∈ D)
  have hD : S.filter (fun a ↦ a ∈ D)=D.filter (fun a ↦ P (f a)) := by
    ext a
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [hD] at hpart
  change _+R.card=S.card at hpart
  change _+_ ≤ S.card
  omega

/-- The face consisting of subsets disjoint from a nonempty zero-sum
set is lost from every target image. This uses no validity assumption. -/
theorem zero_sum_disjoint_face_card_le_intrinsic_fibre_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : ∑ i ∈ C, (g i+b)=0)
    (P : G → Prop) :
    (Finset.univ.filter (fun S : Finset (Fin n) ↦ Disjoint S C ∧ P (∑ i ∈ S, (g i+b)))).card ≤
      tupleBinaryFibreLoss g b P := by
  classical
  let f := fun S : Finset (Fin n) ↦ ∑ i ∈ S, (g i+b)
  let D := Finset.univ.filter (fun S : Finset (Fin n) ↦ Disjoint S C)
  have hrep : ∀ S, ∃ T, T ∉ D ∧ f T=f S := by
    intro S
    by_cases hdis : Disjoint S C
    · refine ⟨S ∪ C,?_,?_⟩
      · intro h
        have hd := (Finset.mem_filter.mp h).2
        obtain ⟨i,hi⟩ := hne
        exact Finset.disjoint_left.mp hd (Finset.mem_union_right S hi) hi
      · dsimp only [f]
        rw [Finset.sum_union hdis,hz,add_zero]
    · exact ⟨S,by simpa only [D,Finset.mem_filter,Finset.mem_univ,true_and] using hdis,rfl⟩
  have h := image_filter_card_add_discarded_le f D hrep P
  have hface : (D.filter (fun S ↦ P (f S)))=
      Finset.univ.filter (fun S : Finset (Fin n) ↦ Disjoint S C ∧ P (∑ i ∈ S, (g i+b))) := by
    ext S
    simp only [D,f,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hface] at h
  change ((tupleBinarySumImage g b).filter P).card+_ ≤ _ at h
  unfold tupleBinaryFibreLoss
  exact Nat.le_sub_of_add_le' h

/-- The subsets disjoint from C are exactly the binary cube on its
complement, with all shifted sums and target predicates retained. -/
theorem exists_complement_embedding_with_subset_face_card
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (C : Finset (Fin n)) :
    ∃ e : Fin (n-C.card) ↪ Fin n,
      (∀ i, e i ∉ C) ∧ (∀ v, v ∉ C → ∃ i, e i=v) ∧
      ∀ P : G → Prop,
        (Finset.univ.filter (fun S : Finset (Fin n) ↦ Disjoint S C ∧ P (∑ i ∈ S, (g i+b)))).card=
        (Finset.univ.filter (fun S : Finset (Fin (n-C.card)) ↦ P (∑ i ∈ S, (g (e i)+b)))).card := by
  classical
  let B := {i : Fin n // i ∉ C}
  have hcard : Fintype.card B=n-C.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      Fintype.card_subtype_compl (fun i : Fin n ↦ i ∈ C)
  let e' : Fin (n-C.card) ≃ B := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let e : Fin (n-C.card) ↪ Fin n :=
    ⟨fun i ↦ (e' i).val,by intro i j h; exact e'.injective (Subtype.ext h)⟩
  have hout : ∀ i, e i ∉ C := fun i ↦ (e' i).property
  have hsurj : ∀ v, v ∉ C → ∃ i, e i=v := by
    intro v hv
    obtain ⟨i,hi⟩ := e'.surjective ⟨v,hv⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  refine ⟨e,hout,hsurj,?_⟩
  intro P
  symm
  apply Finset.card_bij (fun S _ ↦ S.map e)
  · intro S hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hC
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
      exact hout i hC
    · simpa only [Finset.sum_map] using (Finset.mem_filter.mp hS).2
  · intro S _ T _ h
    exact Finset.map_injective e h
  · intro T hT
    have hdis := (Finset.mem_filter.mp hT).2.1
    let S := T.preimage e e.injective.injOn
    have hmap : S.map e=T := by
      ext v
      constructor
      · intro hv
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hv
        exact Finset.mem_preimage.mp hi
      · intro hv
        have houtv : v ∉ C := fun hC ↦ Finset.disjoint_left.mp hdis hv hC
        obtain ⟨i,rfl⟩ := hsurj v houtv
        exact Finset.mem_map.mpr ⟨i,Finset.mem_preimage.mpr hv,rfl⟩
    refine ⟨S,?_,hmap⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hp := (Finset.mem_filter.mp hT).2.2
    rw [← hmap,Finset.sum_map] at hp
    exact hp

/-- A nonempty zero-sum coordinate set forces its entire complementary
cube as intrinsic loss, for arbitrary tuples and additive groups. -/
theorem two_pow_complement_le_intrinsic_loss_of_zero_sum_face
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : ∑ i ∈ C, (g i+b)=0) :
    2^(n-C.card) ≤ tupleBinaryCollisionLoss g b := by
  obtain ⟨e,_,_,hcard⟩ := exists_complement_embedding_with_subset_face_card g b C
  have h := zero_sum_disjoint_face_card_le_intrinsic_fibre_loss g b C hne hz (fun _ ↦ True)
  rw [hcard (fun _ ↦ True)] at h
  simpa only [tupleBinaryFibreLoss,tupleBinaryCollisionLoss,Finset.filter_true,
    Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using h

/-- If one complementary coordinate is odd, a zero-sum face contributes
half of its cube to each intrinsic parity loss. Validity is not assumed. -/
theorem two_pow_complement_le_twice_intrinsic_parity_loss_of_zero_sum
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : ∑ i ∈ C, (g i+b)=0)
    (hodd : ∃ j, j ∉ C ∧ Odd (g j+b).val) (v : Bool) :
    2^(n-C.card) ≤ 2*tupleBinaryParityLoss g b v := by
  classical
  obtain ⟨e,_,hsurj,hcard⟩ := exists_complement_embedding_with_subset_face_card g b C
  have hodd' : ∃ i, Odd (g (e i)+b).val := by
    obtain ⟨j,hj,ho⟩ := hodd
    obtain ⟨i,rfl⟩ := hsurj j hj
    exact ⟨i,ho⟩
  have hb := twice_subset_parity_card_eq_two_pow hN (fun i ↦ g (e i)) b hodd' v
  have he := hcard (fun z ↦ decide (Even z.val)=v)
  have he' : (Finset.univ.filter (fun S : Finset (Fin n) ↦
      Disjoint S C ∧ decide (Even (∑ i ∈ S, (g i+b)).val)=v)).card=
      (Finset.univ.filter (fun S : Finset (Fin (n-C.card)) ↦
        decide (Even (∑ i ∈ S, (g (e i)+b)).val)=v)).card := by
    convert he using 1 <;> congr
  have hl : (Finset.univ.filter (fun S : Finset (Fin n) ↦
      Disjoint S C ∧ decide (Even (∑ i ∈ S, (g i+b)).val)=v)).card ≤
      tupleBinaryParityLoss g b v := by
    unfold tupleBinaryParityLoss
    convert zero_sum_disjoint_face_card_le_intrinsic_fibre_loss g b C hne hz
      (fun z ↦ decide (Even z.val)=v) using 1
    congr
  rw [he'] at hl
  omega

/-- Every actual cycle at a subbinary even modulus contributes at least
half of its complementary cube to each intrinsic parity loss. -/
theorem two_pow_outside_le_twice_intrinsic_parity_loss_of_affine_cycle
    {n c N : ℕ} [NeZero N] (hc : 0 < c) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (E : Fin c ↪ Fin n) (b : ZMod N) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (v : Bool) :
    2^(n-c) ≤ 2*tupleBinaryParityLoss g b v := by
  classical
  have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ E.injective
  let C := Finset.univ.map E
  have hcard : C.card=c := by simp [C]
  have hne : C.Nonempty :=
    ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
  have hshift : ∀ i, g (E (R i))+b=2 • (g (E i)+b) := by
    intro i
    rw [hd]
    simp only [two_nsmul]
    abel
  have hz : (∑ i ∈ C, (g i+b))=0 := by
    simp only [C,Finset.sum_map]
    exact sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E i)+b) hshift Finset.univ (by simp)
  have heven : ∀ i, Even (g (E i)+b).val := by
    intro i
    have he := hshift (R.symm i)
    rw [R.apply_symm_apply] at he
    rw [he]
    exact even_val_of_even_nsmul hN (by decide : Even (2 : ℕ)) _
  obtain ⟨j,hj⟩ := exists_odd_shifted_coordinate_of_subbinary_even_tuple (by omega) hN g hg b hsub
  have hjout : j ∉ C := by
    intro h
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp h
    exact (Nat.not_even_iff_odd.mpr hj) (heven i)
  simpa only [hcard] using two_pow_complement_le_twice_intrinsic_parity_loss_of_zero_sum
    hN g b C hne hz ⟨j,hjout,hj⟩ v

/-- A parity loss budget 2^k leaves at most k+1 coordinates outside
any actual cycle of a subbinary valid tuple at even modulus. -/
theorem dimension_le_cycle_add_parity_loss_exponent
    {n c k N : ℕ} [NeZero N] (hc : 0 < c) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (E : Fin c ↪ Fin n) (b : ZMod N) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (v : Bool)
    (hloss : tupleBinaryParityLoss g b v ≤ 2^k) :
    n ≤ c+k+1 := by
  have h := (two_pow_outside_le_twice_intrinsic_parity_loss_of_affine_cycle hc hN g hg hsub E b R hd v).trans
    (Nat.mul_le_mul_left 2 hloss)
  rw [← pow_succ'] at h
  have he := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h
  omega

end MinModulus
