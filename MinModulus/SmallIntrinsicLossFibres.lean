import MinModulus.IntrinsicCollisionSupport

namespace MinModulus
open Finset
open scoped Classical

/-- Across three binary subsets, each coordinate contributes either zero
or two to the sum of their pairwise symmetric-difference distances. -/
theorem three_subset_support_sum_le_twice_dimension
    {n : ℕ} (U V W : Finset (Fin n)) :
    ((U \ V) ∪ (V \ U)).card+((V \ W) ∪ (W \ V)).card+
      ((W \ U) ∪ (U \ W)).card ≤ 2*n := by
  classical
  have hcard (S : Finset (Fin n)) : S.card=∑ i : Fin n, if i ∈ S then 1 else 0 := by simp
  rw [hcard _,hcard _,hcard _,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin n, 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;> by_cases hW : i ∈ W <;>
        simp [Finset.mem_union,Finset.mem_sdiff,hU,hV,hW]
    _ = 2*n := by simp [Nat.mul_comm]

/-- Three distinct subsets with one shifted sum force logarithmic
intrinsic loss at least one third of the full dimension. -/
theorem dimension_le_three_log_loss_of_triple_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U V W : Finset (Fin n)) (hUV : U ≠ V) (hUW : U ≠ W) (hVW : V ≠ W)
    (heUV : (∑ i ∈ U, (g i+b))=∑ i ∈ V, (g i+b))
    (heVW : (∑ i ∈ V, (g i+b))=∑ i ∈ W, (g i+b)) :
    n ≤ 3*Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  have h1 := dimension_le_collision_support_add_log_loss g b U V hUV heUV
  have h2 := dimension_le_collision_support_add_log_loss g b V W hVW heVW
  have h3 := dimension_le_collision_support_add_log_loss g b W U (fun h ↦ hUW h.symm) (heUV.trans heVW).symm
  have htri := three_subset_support_sum_le_twice_dimension U V W
  omega

/-- If the dimension exceeds three times the logarithm of intrinsic
loss, every shifted subset-sum fibre contains at most two points. -/
theorem tuple_subset_fibre_card_le_two_of_small_intrinsic_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨U,V,W,hU,hV,hW,hUV,hUW,hVW⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
  have heU := (Finset.mem_filter.mp hU).2
  have heV := (Finset.mem_filter.mp hV).2
  have heW := (Finset.mem_filter.mp hW).2
  have hh := dimension_le_three_log_loss_of_triple_collision g b U V W hUV hUW hVW
    (heU.trans heV.symm) (heV.trans heW.symm)
  omega

/-- Every complete forest encoding inherits the intrinsic two-point
fibre bound, including encodings with only short arms. -/
theorem forest_fibre_card_le_two_of_small_intrinsic_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) (z : G) :
    (forestBoxFibre L x z).card ≤ 2 := by
  change (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦ (∑ i, (p i).val • x i)=z)).card ≤ 2
  rw [forest_box_filter_card_eq_subset_filter_card L g E x b hchain (fun t ↦ t=z)]
  exact tuple_subset_fibre_card_le_two_of_small_intrinsic_loss g b hsmall z

/-- At small intrinsic loss, two distinct profiles cannot share a lower
point: their heavier partners would produce a three-point fibre. -/
theorem forest_profile_rectangles_pairwise_disjoint_of_small_intrinsic_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    (↑(forestCollisionProfiles n L x) : Set _).PairwiseDisjoint (forestProfileLowerBox L) := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n:=L i)
    omega
  intro w hw v hv hne
  apply Finset.disjoint_left.mpr
  intro q hqw hqv
  obtain ⟨p,⟨hpi,hpe,hpq⟩,_⟩ := exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w hw q hqw
  obtain ⟨r,⟨hri,hre,hrq⟩⟩ := (exists_unique_heavier_partner_of_profile_lower_point L hdiameter x v hv q hqv).exists
  have hpq' : p ≠ q := by intro he; subst p; omega
  have hrq' : r ≠ q := by intro he; subst r; omega
  have hpr : p ≠ r := by
    intro he
    apply hne
    funext i
    apply Fin.ext
    have h1 := hpi i
    have h2 := hri i
    rw [he] at h1
    omega
  have hthree : 2 < (forestBoxFibre L x (∑ i, (q i).val • x i)).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨p,r,q,?_,?_,?_,hpr,hpq',hrq'⟩ <;>
      simp only [forestBoxFibre,Finset.mem_filter,Finset.mem_univ,true_and]
    · exact hpe
    · exact hre
  have htwo := forest_fibre_card_le_two_of_small_intrinsic_loss L g E x b hchain hsmall (∑ i, (q i).val • x i)
  omega

/-- Small intrinsic loss identifies the profile union cardinality with
summed profile volumes, independently of forest diameter. -/
theorem forest_collision_loss_eq_profile_volume_of_small_intrinsic_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    forestCollisionLoss n L x = ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  have h := Finset.card_biUnion
    (forest_profile_rectangles_pairwise_disjoint_of_small_intrinsic_loss L g E x b hchain hsmall)
  simpa only [forestCollisionLoss,forestProfileLowerBox_card] using h

/-- For a valid tuple of small intrinsic loss, the summed volumes of
its actual profiles equal the same intrinsic loss in every forest encoding. -/
theorem intrinsic_loss_eq_profile_volume_of_small_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    tupleBinaryCollisionLoss g b = ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  rw [← forest_collision_loss_eq_tuple_binary_loss L hL g hg E x b hchain]
  exact forest_collision_loss_eq_profile_volume_of_small_intrinsic_loss L g E x b hchain hsmall

end MinModulus
