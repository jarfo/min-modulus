import MinModulus.IntrinsicChainContinuation

namespace MinModulus
open Finset
open scoped Classical

/-- The exact loss of shifted subset sums restricted to any target
predicate. The original tuple and fixed shift determine it completely. -/
noncomputable def tupleBinaryFibreLoss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (P : G → Prop) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin n) ↦ P (∑ i ∈ S, (g i+b)))).card-
    ((tupleBinarySumImage g b).filter P).card

/-- Counting a target image and its lost multiplicities recovers every
original subset point in that target predicate, even without validity. -/
theorem tuple_binary_fibre_image_card_add_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (P : G → Prop) :
    ((tupleBinarySumImage g b).filter P).card+tupleBinaryFibreLoss g b P=
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ P (∑ i ∈ S, (g i+b)))).card := by
  classical
  have h : ((tupleBinarySumImage g b).filter P).card ≤
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ P (∑ i ∈ S, (g i+b)))).card := by
    unfold tupleBinarySumImage
    rw [Finset.filter_image]
    exact Finset.card_image_le
  unfold tupleBinaryFibreLoss
  omega

/-- Restricting intrinsic loss to a predicate and its complement
partitions total intrinsic loss exactly. -/
theorem tuple_binary_fibre_loss_add_complement
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (P : G → Prop) :
    tupleBinaryFibreLoss g b P+tupleBinaryFibreLoss g b (fun z ↦ ¬ P z)=
      tupleBinaryCollisionLoss g b := by
  classical
  have hp := tuple_binary_fibre_image_card_add_loss g b P
  have hn := tuple_binary_fibre_image_card_add_loss g b (fun z ↦ ¬ P z)
  have ht := tuple_binary_image_card_add_loss_eq_two_pow g b
  have him := Finset.card_filter_add_card_filter_not (s:=tupleBinarySumImage g b) P
  have hbox := Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Finset (Fin n))))
    (fun S ↦ P (∑ i ∈ S, (g i+b)))
  have hnot : ((tupleBinarySumImage g b).filter (fun z ↦ ¬ P z)).card+
      tupleBinaryFibreLoss g b (fun z ↦ ¬ P z)=
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ ¬ P (∑ i ∈ S, (g i+b)))).card := by
    convert hn using 1 <;> congr
  have hbox' : (Finset.univ.filter (fun S : Finset (Fin n) ↦ P (∑ i ∈ S, (g i+b)))).card+
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ ¬ P (∑ i ∈ S, (g i+b)))).card=2^n := by
    simpa only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using hbox
  omega

/-- Sum-preserving subset encoding retains the number of points inside
any target predicate, before any collisions are removed. -/
theorem forest_box_filter_card_eq_subset_filter_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (P : G → Prop) :
    (Finset.univ.filter (fun p : (∀ a, Fin (2^(L a))) ↦ P (∑ a, (p a).val • x a))).card=
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ P (∑ i ∈ S, (g i+b)))).card := by
  classical
  obtain ⟨e,he⟩ := exists_subset_forest_box_equiv L g E x b hchain
  symm
  apply Finset.card_bij (fun S _ ↦ e S)
  · intro S hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he]; exact (Finset.mem_filter.mp hS).2⟩
  · intro S _ T _ h
    exact e.injective h
  · intro p hp
    refine ⟨e.symm p,?_,e.apply_symm_apply p⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← he,e.apply_symm_apply]
    exact (Finset.mem_filter.mp hp).2

/-- Removing actual profiles loses exactly the intrinsic number of
subset sums in every target predicate, independently of regrouping. -/
theorem forest_filtered_collision_loss_eq_intrinsic_fibre_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (P : G → Prop) :
    (((forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)).filter
      (fun p ↦ P (∑ i, (p i).val • x i))).card=tupleBinaryFibreLoss g b P := by
  classical
  have h := forest_box_image_filter_card_add_collision_loss L hL g hg E x b hchain P
  rw [forest_box_image_eq_tuple_binary_image L g E x b hchain,
    forest_box_filter_card_eq_subset_filter_card L g E x b hchain P] at h
  unfold tupleBinaryFibreLoss
  omega

/-- Intrinsic loss restricted to one parity class of the shifted sum. -/
noncomputable def tupleBinaryParityLoss
    {n N : ℕ} (g : Fin n → ZMod N) (b : ZMod N) (v : Bool) : ℕ :=
  tupleBinaryFibreLoss g b (fun z ↦ decide (Even z.val)=v)

/-- Each actual parity loss is preserved under every complete valid
chain regrouping at the same shift, without a width or parity premise. -/
theorem forest_parity_collision_loss_eq_intrinsic_parity_loss
    {n N : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (v : Bool) :
    forestCollisionParityLoss n L x v=tupleBinaryParityLoss g b v := by
  unfold forestCollisionParityLoss tupleBinaryParityLoss
  convert forest_filtered_collision_loss_eq_intrinsic_fibre_loss L hL g hg E x b hchain
    (fun z ↦ decide (Even z.val)=v) using 1
  congr

/-- The two intrinsic parity losses add to total loss, including at odd
moduli and for tuples for which the subset cube is not balanced. -/
theorem tuple_binary_parity_loss_add
    {n N : ℕ} (g : Fin n → ZMod N) (b : ZMod N) :
    tupleBinaryParityLoss g b true+tupleBinaryParityLoss g b false=tupleBinaryCollisionLoss g b := by
  simpa only [tupleBinaryParityLoss,decide_eq_true_eq,decide_eq_false_iff_not] using
    tuple_binary_fibre_loss_add_complement g b (fun z ↦ Even z.val)

/-- One odd shifted coordinate balances the original subset cube
between parity classes at any nonzero even cyclic modulus. -/
theorem twice_subset_parity_card_eq_two_pow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N)
    (hodd : ∃ i, Odd (g i+b).val) (v : Bool) :
    2*(Finset.univ.filter (fun S : Finset (Fin n) ↦
      decide (Even (∑ i ∈ S, (g i+b)).val)=v)).card=2^n := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  let L : Fin n → ℕ := fun _ ↦ 1
  let x := fun i ↦ g i+b
  let E : (Σ i : Fin n, Fin (L i)) ≃ Fin n :=
    { toFun := Sigma.fst
      invFun := fun i ↦ ⟨i,0⟩
      left_inv := by intro ⟨i,j⟩; have : j=0 := Fin.eq_zero j; subst j; rfl
      right_inv := fun _ ↦ rfl }
  have hc : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a := by
    intro a i
    have : i=0 := Fin.eq_zero i
    subst i
    simp [E,x]
  have hb := twice_parity_box_card_eq_two_pow (n:=n) hN L (fun _ ↦ by decide)
    (by simp [L]) x hodd v
  have hbNat : 2*(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card=2^n := by exact_mod_cast hb
  have he := forest_box_filter_card_eq_subset_filter_card L g E x b hc
    (fun z ↦ decide (Even z.val)=v)
  have he' : (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card=
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ decide (Even (∑ i ∈ S, (g i+b)).val)=v)).card := by
    convert he using 1 <;> congr
  rw [he'] at hbNat
  exact hbNat

/-- In either parity class the exact image plus intrinsic loss fills
half of the binary cube, provided one shifted coordinate is odd. -/
theorem twice_intrinsic_parity_image_add_loss_eq_two_pow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N)
    (hodd : ∃ i, Odd (g i+b).val) (v : Bool) :
    2*((tupleBinarySumImage g b).filter (fun z ↦ decide (Even z.val)=v)).card+
      2*tupleBinaryParityLoss g b v=2^n := by
  have h := tuple_binary_fibre_image_card_add_loss g b (fun z ↦ decide (Even z.val)=v)
  have h' : ((tupleBinarySumImage g b).filter (fun z ↦ decide (Even z.val)=v)).card+
      tupleBinaryParityLoss g b v=
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ decide (Even (∑ i ∈ S, (g i+b)).val)=v)).card := by
    unfold tupleBinaryParityLoss
    convert h using 1 <;> congr
  have hb := twice_subset_parity_card_eq_two_pow hN g b hodd v
  omega

/-- Subbinary validity supplies an odd shifted coordinate at every
shift in an even cyclic group; no half-deletion hypothesis is required. -/
theorem exists_odd_shifted_coordinate_of_subbinary_even_tuple
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsub : N < 2^n) : ∃ i, Odd (g i+b).val := by
  by_contra h
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  exact not_all_even_values_of_valid_subbinary_tuple hn (even_iff_two_dvd.mpr hN)
    (fun i ↦ g i+b) hv hsub (fun i ↦ Nat.not_odd_iff_even.mp (fun hi ↦ h ⟨i,hi⟩))

end MinModulus
