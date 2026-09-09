import MinModulus.ParityIntrinsicChainContinuation

namespace MinModulus
open Finset
open scoped Classical

/-- The subset-sum image on an actual finite set of coordinates. -/
noncomputable def subsetSumImageOn
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) : Finset G :=
  S.powerset.image (fun T ↦ ∑ i ∈ T, x i)

/-- Exact loss of distinct subset sums on an actual coordinate set. -/
noncomputable def subsetCollisionLossOn
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) : ℕ :=
  2^S.card-(subsetSumImageOn x S).card

/-- Image size plus exact loss recovers the coordinate subset cube. -/
theorem subset_sum_image_card_add_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) :
    (subsetSumImageOn x S).card+subsetCollisionLossOn x S=2^S.card := by
  have h : (subsetSumImageOn x S).card ≤ 2^S.card := by
    simpa only [subsetSumImageOn,Finset.card_powerset] using
      Finset.card_image_le (s:=S.powerset) (f:=fun T ↦ ∑ i ∈ T, x i)
  unfold subsetCollisionLossOn
  omega

/-- Inserting a fresh coordinate adds precisely a translate of the
previous subset-sum image, with the original coordinate value retained. -/
theorem subset_sum_image_on_insert
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (a : α) (ha : a ∉ S) :
    subsetSumImageOn x (insert a S)=subsetSumImageOn x S ∪
      (subsetSumImageOn x S).image (fun z ↦ x a+z) := by
  classical
  unfold subsetSumImageOn
  rw [Finset.powerset_insert,Finset.image_union]
  simp only [Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro T hT
  exact Finset.sum_insert (fun h ↦ ha (Finset.mem_powerset.mp hT h))

/-- Exact loss under insertion is twice the previous loss plus the
actual intersection of the old image with its new translate. -/
theorem subset_collision_loss_on_insert
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (a : α) (ha : a ∉ S) :
    subsetCollisionLossOn x (insert a S)=2*subsetCollisionLossOn x S+
      (subsetSumImageOn x S ∩ (subsetSumImageOn x S).image (fun z ↦ x a+z)).card := by
  classical
  let A := subsetSumImageOn x S
  have hfull := subset_sum_image_card_add_loss x (insert a S)
  rw [subset_sum_image_on_insert x S a ha,Finset.card_insert_of_notMem ha,pow_succ] at hfull
  have hbase := subset_sum_image_card_add_loss x S
  have htranslate : (A.image (fun z ↦ x a+z)).card=A.card :=
    Finset.card_image_of_injective A (fun _ _ h ↦ add_left_cancel h)
  have hunion := Finset.card_union_add_card_inter A (A.image (fun z ↦ x a+z))
  rw [htranslate] at hunion
  change (A ∪ A.image (fun z ↦ x a+z)).card+_=2^S.card*2 at hfull
  change A.card+_=2^S.card at hbase
  change _=2*_+(A ∩ A.image (fun z ↦ x a+z)).card
  omega

/-- The finite-coordinate image on all indices is the original shifted
binary subset image. -/
theorem subset_sum_image_on_univ_eq_tuple_image
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    subsetSumImageOn (fun i ↦ g i+b) Finset.univ=tupleBinarySumImage g b := by
  simp only [subsetSumImageOn,Finset.powerset_univ,tupleBinarySumImage]

/-- The finite-coordinate loss on all indices is the intrinsic tuple loss. -/
theorem subset_collision_loss_on_univ_eq_tuple_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    subsetCollisionLossOn (fun i ↦ g i+b) Finset.univ=tupleBinaryCollisionLoss g b := by
  simp only [subsetCollisionLossOn,subset_sum_image_on_univ_eq_tuple_image,
    Finset.card_univ,Fintype.card_fin,tupleBinaryCollisionLoss]

/-- Deleting any actual coordinate gives an exact intrinsic loss
recurrence, including the overlap with translation by that shifted entry. -/
theorem tuple_binary_loss_eq_twice_deleted_loss_add_overlap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (a : Fin n) :
    tupleBinaryCollisionLoss g b=2*subsetCollisionLossOn (fun i ↦ g i+b) (Finset.univ.erase a)+
      (subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a) ∩
        (subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a)).image (fun z ↦ (g a+b)+z)).card := by
  have h := subset_collision_loss_on_insert (fun i ↦ g i+b) (Finset.univ.erase a) a
    (by simp)
  convert h using 1
  rw [← subset_collision_loss_on_univ_eq_tuple_loss g b]
  congr 1
  ext i
  simp
  tauto


/-- Enlarging an actual coordinate set by r indices multiplies its
existing collision loss by at least 2^r. This holds without validity. -/
theorem subset_collision_loss_growth_of_subset
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hST : S ⊆ T) :
    2^(T.card-S.card)*subsetCollisionLossOn x S ≤ subsetCollisionLossOn x T := by
  classical
  have growth : ∀ R : Finset α, Disjoint S R →
      2^R.card*subsetCollisionLossOn x S ≤ subsetCollisionLossOn x (S ∪ R) := by
    intro R
    induction R using Finset.induction_on with
    | empty => intro _; simp
    | @insert a R ha ih =>
      intro hdis
      have hdisR : Disjoint S R := Finset.disjoint_left.mpr (fun i hiS hiR ↦
        Finset.disjoint_left.mp hdis hiS (Finset.mem_insert_of_mem hiR))
      have haS : a ∉ S := fun h ↦ Finset.disjoint_left.mp hdis h (Finset.mem_insert_self a R)
      have hfresh : a ∉ S ∪ R := by simpa only [Finset.mem_union,not_or] using And.intro haS ha
      have hrec := subset_collision_loss_on_insert x (S ∪ R) a hfresh
      have hi := ih hdisR
      rw [Finset.card_insert_of_notMem ha,pow_succ,Finset.union_insert]
      calc
        2^R.card*2*subsetCollisionLossOn x S=2*(2^R.card*subsetCollisionLossOn x S) := by ring
        _ ≤ 2*subsetCollisionLossOn x (S ∪ R) := Nat.mul_le_mul_left 2 hi
        _ ≤ subsetCollisionLossOn x (insert a (S ∪ R)) := by omega
  have hdis : Disjoint S (T \ S) := Finset.disjoint_left.mpr (fun _ hiS hiR ↦ (Finset.mem_sdiff.mp hiR).2 hiS)
  have h := growth (T \ S) hdis
  have hunion : S ∪ (T \ S)=T := by
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (hi | ⟨hi,_⟩)
      · exact hST hi
      · exact hi
    · intro hi
      by_cases hs : i ∈ S
      · exact Or.inl hs
      · exact Or.inr ⟨hi,hs⟩
  rw [hunion,Finset.card_sdiff_of_subset hST] at h
  exact h

end MinModulus
