import MinModulus.SubsetLossRecurrence

namespace MinModulus
open Finset
open scoped Classical

/-- Exact loss in a target predicate on an actual finite coordinate set. -/
noncomputable def subsetFibreLossOn
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (P : G → Prop) : ℕ :=
  (S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card-((subsetSumImageOn x S).filter P).card

/-- Target image and loss recover all subset points in that predicate. -/
theorem subset_fibre_image_card_add_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (P : G → Prop) :
    ((subsetSumImageOn x S).filter P).card+subsetFibreLossOn x S P=
      (S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card := by
  have h : ((subsetSumImageOn x S).filter P).card ≤
      (S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card := by
    unfold subsetSumImageOn
    rw [Finset.filter_image]
    exact Finset.card_image_le
  unfold subsetFibreLossOn
  omega

/-- Fresh insertion splits the target-restricted subset cube into the
old target and its translate by the actual inserted coordinate. -/
theorem subset_filter_card_on_insert
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (a : α) (ha : a ∉ S)
    (P : G → Prop) :
    ((insert a S).powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card=
      (S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card+
      (S.powerset.filter (fun T ↦ P (x a+∑ i ∈ T, x i))).card := by
  classical
  let A := S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))
  let B := S.powerset.filter (fun T ↦ P (x a+∑ i ∈ T, x i))
  have hfilter : (insert a S).powerset.filter (fun T ↦ P (∑ i ∈ T, x i))=
      A ∪ B.image (insert a) := by
    dsimp only [A,B]
    rw [Finset.powerset_insert,Finset.filter_union,Finset.filter_image]
    congr 1
    apply congrArg (Finset.image (insert a))
    apply Finset.filter_congr
    intro T hT
    rw [Finset.sum_insert (fun h ↦ ha (Finset.mem_powerset.mp hT h))]
  have hdis : Disjoint A (B.image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro T hT hB
    obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hB
    exact ha (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 (Finset.mem_insert_self a U))
  have hi : Set.InjOn (fun T : Finset α ↦ insert a T) B := by
    intro T hT U hU he
    have haT : a ∉ T := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 h)
    have haU : a ∉ U := fun h ↦ ha (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 h)
    have hh := congrArg (fun V : Finset α ↦ V.erase a) he
    simpa [haT,haU] using hh
  rw [hfilter,Finset.card_union_of_disjoint hdis,Finset.card_image_iff.mpr hi]

/-- In each target predicate, insertion adds the two old losses and
exactly the actual overlap of the old image with its coordinate translate. -/
theorem subset_fibre_loss_on_insert
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (a : α) (ha : a ∉ S)
    (P : G → Prop) :
    subsetFibreLossOn x (insert a S) P=subsetFibreLossOn x S P+
      subsetFibreLossOn x S (fun z ↦ P (x a+z))+
      ((subsetSumImageOn x S ∩ (subsetSumImageOn x S).image (fun z ↦ x a+z)).filter P).card := by
  classical
  let A := subsetSumImageOn x S
  let B := A.image (fun z ↦ x a+z)
  have hfull := subset_fibre_image_card_add_loss x (insert a S) P
  have hleft := subset_fibre_image_card_add_loss x S P
  have hright := subset_fibre_image_card_add_loss x S (fun z ↦ P (x a+z))
  rw [subset_sum_image_on_insert x S a ha,subset_filter_card_on_insert x S a ha P] at hfull
  have hU : (A ∪ B).filter P=A.filter P ∪ B.filter P := by ext z; simp; tauto
  have hI : (A ∩ B).filter P=A.filter P ∩ B.filter P := by ext z; simp; tauto
  have hunion : ((A ∪ B).filter P).card+((A ∩ B).filter P).card=
      (A.filter P).card+(B.filter P).card := by
    rw [hU,hI]
    exact Finset.card_union_add_card_inter _ _
  have htranslate : (B.filter P).card=(A.filter (fun z ↦ P (x a+z))).card := by
    dsimp only [B]
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h)
  rw [htranslate] at hunion
  change ((A ∪ B).filter P).card+_= _ at hfull
  change (A.filter P).card+_=_ at hleft
  change (A.filter (fun z ↦ P (x a+z))).card+_=_ at hright
  change _=_+_+((A ∩ B).filter P).card
  omega

/-- A target predicate and its complement partition the finite-coordinate
loss exactly, for arbitrary tuples and additive groups. -/
theorem subset_fibre_loss_add_complement
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (P : G → Prop) :
    subsetFibreLossOn x S P+subsetFibreLossOn x S (fun z ↦ ¬ P z)=subsetCollisionLossOn x S := by
  have hp := subset_fibre_image_card_add_loss x S P
  have hn := subset_fibre_image_card_add_loss x S (fun z ↦ ¬ P z)
  have ht := subset_sum_image_card_add_loss x S
  have him := Finset.card_filter_add_card_filter_not (s:=subsetSumImageOn x S) P
  have hbox := Finset.card_filter_add_card_filter_not (s:=S.powerset) (fun T ↦ P (∑ i ∈ T, x i))
  have hnot : ((subsetSumImageOn x S).filter (fun z ↦ ¬ P z)).card+
      subsetFibreLossOn x S (fun z ↦ ¬ P z)=
      (S.powerset.filter (fun T ↦ ¬ P (∑ i ∈ T, x i))).card := by
    convert hn using 1 <;> congr
  have hbox' : (S.powerset.filter (fun T ↦ P (∑ i ∈ T, x i))).card+
      (S.powerset.filter (fun T ↦ ¬ P (∑ i ∈ T, x i))).card=2^S.card := by
    simpa only [Finset.card_powerset] using hbox
  omega

/-- Finite-coordinate fibre loss on the entire tuple is intrinsic fibre loss. -/
theorem subset_fibre_loss_on_univ_eq_tuple_fibre_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (P : G → Prop) :
    subsetFibreLossOn (fun i ↦ g i+b) Finset.univ P=tupleBinaryFibreLoss g b P := by
  simp only [subsetFibreLossOn,Finset.powerset_univ,subset_sum_image_on_univ_eq_tuple_image,
    tupleBinaryFibreLoss]

/-- Even translation preserves residue parity at nonzero even modulus. -/
theorem even_val_add_iff_of_even_left
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) (x : ZMod N) (hx : Even x.val) (z : ZMod N) :
    Even (x+z).val ↔ Even z.val := by
  simp only [Nat.even_iff,ZMod.val_add,Nat.mod_mod_of_dvd _ hN,Nat.add_mod,
    Nat.even_iff.mp hx,zero_add,Nat.mod_mod]

/-- Odd translation exchanges residue parity at nonzero even modulus. -/
theorem even_val_add_iff_of_odd_left
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) (x : ZMod N) (hx : Odd x.val) (z : ZMod N) :
    Even (x+z).val ↔ ¬ Even z.val := by
  rw [Nat.even_iff,ZMod.val_add,Nat.mod_mod_of_dvd _ hN,Nat.add_mod,Nat.odd_iff.mp hx,Nat.even_iff]
  have h := Nat.mod_lt z.val (by decide : 0 < (2 : ℕ))
  omega

/-- Adding an even coordinate doubles the old loss in each parity class,
then adds exactly the actual overlap in that class. -/
theorem subset_parity_fibre_loss_on_insert_of_even
    {α : Type*} {N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (x : α → ZMod N) (S : Finset α) (a : α) (ha : a ∉ S) (hx : Even (x a).val) (v : Bool) :
    subsetFibreLossOn x (insert a S) (fun z ↦ decide (Even z.val)=v)=
      2*subsetFibreLossOn x S (fun z ↦ decide (Even z.val)=v)+
      ((subsetSumImageOn x S ∩ (subsetSumImageOn x S).image (fun z ↦ x a+z)).filter
        (fun z ↦ decide (Even z.val)=v)).card := by
  let P := fun z : ZMod N ↦ decide (Even z.val)=v
  have hshift : (fun z ↦ P (x a+z))=P := by
    funext z
    apply propext
    cases v <;> simp only [P,decide_eq_true_eq,decide_eq_false_iff_not,even_val_add_iff_of_even_left hN (x a) hx]
  have h := subset_fibre_loss_on_insert x S a ha P
  rw [hshift] at h
  simp only [P,two_mul] at h ⊢
  convert h using 1
  congr <;> exact Subsingleton.elim _ _

/-- Adding an odd coordinate contributes the entire old collision loss
to each parity class, plus its actual overlap in that class. -/
theorem subset_parity_fibre_loss_on_insert_of_odd
    {α : Type*} {N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (x : α → ZMod N) (S : Finset α) (a : α) (ha : a ∉ S) (hx : Odd (x a).val) (v : Bool) :
    subsetFibreLossOn x (insert a S) (fun z ↦ decide (Even z.val)=v)=
      subsetCollisionLossOn x S+
      ((subsetSumImageOn x S ∩ (subsetSumImageOn x S).image (fun z ↦ x a+z)).filter
        (fun z ↦ decide (Even z.val)=v)).card := by
  let P := fun z : ZMod N ↦ decide (Even z.val)=v
  have hshift : (fun z ↦ P (x a+z))=(fun z ↦ ¬ P z) := by
    funext z
    apply propext
    cases v <;> simp only [P,decide_eq_true_eq,decide_eq_false_iff_not,even_val_add_iff_of_odd_left hN (x a) hx]
  have h := subset_fibre_loss_on_insert x S a ha P
  rw [hshift,subset_fibre_loss_add_complement] at h
  convert h using 1
  congr <;> exact Subsingleton.elim _ _

/-- Deleting an odd shifted coordinate leaves its entire collision
loss in each full-tuple parity loss, with exact actual overlap remainder. -/
theorem tuple_parity_loss_eq_deleted_loss_add_overlap_of_odd
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N) (a : Fin n) (ha : Odd (g a+b).val) (v : Bool) :
    tupleBinaryParityLoss g b v=subsetCollisionLossOn (fun i ↦ g i+b) (Finset.univ.erase a)+
      ((subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a) ∩
        (subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a)).image (fun z ↦ (g a+b)+z)).filter
          (fun z ↦ decide (Even z.val)=v)).card := by
  have h := subset_parity_fibre_loss_on_insert_of_odd hN (fun i ↦ g i+b) (Finset.univ.erase a) a
    (by simp) ha v
  convert h using 1
  rw [tupleBinaryParityLoss,← subset_fibre_loss_on_univ_eq_tuple_fibre_loss g b]
  congr 1
  ext i
  simp
  tauto

/-- Deleting an even shifted coordinate leaves twice the old loss in
that parity class, with the exact actual overlap remainder. -/
theorem tuple_parity_loss_eq_twice_deleted_parity_loss_add_overlap_of_even
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N) (a : Fin n) (ha : Even (g a+b).val) (v : Bool) :
    tupleBinaryParityLoss g b v=
      2*subsetFibreLossOn (fun i ↦ g i+b) (Finset.univ.erase a) (fun z ↦ decide (Even z.val)=v)+
      ((subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a) ∩
        (subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a)).image (fun z ↦ (g a+b)+z)).filter
          (fun z ↦ decide (Even z.val)=v)).card := by
  have h := subset_parity_fibre_loss_on_insert_of_even hN (fun i ↦ g i+b) (Finset.univ.erase a) a
    (by simp) ha v
  convert h using 1
  rw [tupleBinaryParityLoss,← subset_fibre_loss_on_univ_eq_tuple_fibre_loss g b]
  congr 1
  ext i
  simp
  tauto

/-- Each full-tuple parity loss bounds the total intrinsic loss after
deleting any odd shifted coordinate, without assuming tuple validity. -/
theorem deleted_loss_le_tuple_parity_loss_of_odd
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N) (a : Fin n) (ha : Odd (g a+b).val) (v : Bool) :
    subsetCollisionLossOn (fun i ↦ g i+b) (Finset.univ.erase a) ≤ tupleBinaryParityLoss g b v := by
  rw [tuple_parity_loss_eq_deleted_loss_add_overlap_of_odd hN g b a ha v]
  omega

end MinModulus
