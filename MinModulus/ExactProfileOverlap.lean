import MinModulus.ProfileFibreMoments

namespace MinModulus
open Finset
open scoped Classical

/-- The excess of summed profile volume over exact loss is measured
exactly by fibres containing at least three points. -/
theorem twice_profile_volume_eq_twice_loss_add_triple_excess
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      2*tupleBinaryCollisionLoss g b+
        ∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
          ((forestBoxFibre L x z).card-1)*((forestBoxFibre L x z).card-2) := by
  rw [twice_profile_volume_eq_fibre_moment L hL g hg E x b hchain,
    intrinsic_loss_eq_sum_forest_fibre_excess L g E x b hchain,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  let r := (forestBoxFibre L x z).card
  change r*(r-1)=2*(r-1)+(r-1)*(r-2)
  by_cases hr : r ≤ 1
  · have hz : r-1=0 := by omega
    simp [hz]
  · have h1 : r-1=(r-2)+1 := by omega
    have h2 : r=(r-2)+2 := by omega
    generalize r-2=t at h1 h2 ⊢
    rw [h1,h2]
    ring

/-- Summed profile volume equals intrinsic loss exactly when all actual
box fibres have at most two points. No small-loss or diameter premise. -/
theorem profile_volume_eq_intrinsic_loss_iff_fibres_le_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=tupleBinaryCollisionLoss g b ↔
      ∀ z, (forestBoxFibre L x z).card ≤ 2 := by
  classical
  have hm := twice_profile_volume_eq_twice_loss_add_triple_excess L hL g hg E x b hchain
  constructor
  · intro he z
    have hzsum : (∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
        ((forestBoxFibre L x z).card-1)*((forestBoxFibre L x z).card-2))=0 := by omega
    by_cases hz : z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i)
    · have ht := Finset.sum_eq_zero_iff.mp hzsum z hz
      by_contra h
      have hp : 0 < ((forestBoxFibre L x z).card-1)*((forestBoxFibre L x z).card-2) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    · have hzero : (forestBoxFibre L x z).card=0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        apply hz
        exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
      omega
  · intro hcap
    have hzsum : (∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
        ((forestBoxFibre L x z).card-1)*((forestBoxFibre L x z).card-2))=0 := by
      apply Finset.sum_eq_zero
      intro z _
      have hz : (forestBoxFibre L x z).card-2=0 := by have := hcap z; omega
      simp [hz]
    omega

/-- A two-point fibre cap alone excludes profile overlap once the box
has diameter at least n; no tuple validity is required. -/
theorem profile_rectangles_pairwise_disjoint_of_fibre_cap_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G)
    (hcap : ∀ z, (forestBoxFibre L x z).card ≤ 2) :
    (↑(forestCollisionProfiles n L x) : Set _).PairwiseDisjoint (forestProfileLowerBox L) := by
  classical
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
  have htwo := hcap (∑ i, (q i).val • x i)
  omega
/-- Actual profile rectangles are pairwise disjoint if and only if no
box sum fibre contains three points. -/
theorem profile_rectangles_pairwise_disjoint_iff_fibres_le_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (↑(forestCollisionProfiles n L x) : Set _).PairwiseDisjoint (forestProfileLowerBox L) ↔
      ∀ z, (forestBoxFibre L x z).card ≤ 2 := by
  classical
  constructor
  · intro hdis
    apply (profile_volume_eq_intrinsic_loss_iff_fibres_le_two L hL g hg E x b hchain).mp
    have h := Finset.card_biUnion hdis
    have he : forestCollisionLoss n L x=(∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) := by
      simpa only [forestCollisionLoss,forestProfileLowerBox_card] using h
    rw [forest_collision_loss_eq_tuple_binary_loss L hL g hg E x b hchain] at he
    exact he.symm
  · intro hcap
    have hsize : (∑ i, L i)=n := by
      simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
    have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
      rw [← hsize]
      apply Finset.sum_le_sum
      intro i _
      have := Nat.lt_two_pow_self (n:=L i)
      omega
    exact profile_rectangles_pairwise_disjoint_of_fibre_cap_two L hdiameter x hcap

/-- Each fibre containing at least three points contributes at least one
to summed profile volume minus intrinsic loss. -/
theorem triple_fibre_card_le_profile_volume_excess
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    ((Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i)).filter
      (fun z ↦ 3 ≤ (forestBoxFibre L x z).card)).card ≤
      (∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))-tupleBinaryCollisionLoss g b := by
  classical
  let I := Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i)
  have hcount : 2*(I.filter (fun z ↦ 3 ≤ (forestBoxFibre L x z).card)).card ≤
      ∑ z ∈ I, ((forestBoxFibre L x z).card-1)*((forestBoxFibre L x z).card-2) := by
    have hb : (∑ z ∈ I, if 3 ≤ (forestBoxFibre L x z).card then 1 else 0)=
        (I.filter (fun z ↦ 3 ≤ (forestBoxFibre L x z).card)).card := by simp
    rw [← hb,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : 3 ≤ (forestBoxFibre L x z).card
    · rw [if_pos hz]
      have h1 : 2 ≤ (forestBoxFibre L x z).card-1 := by omega
      have h2 : 1 ≤ (forestBoxFibre L x z).card-2 := by omega
      exact Nat.mul_le_mul h1 h2
    · simp only [if_neg hz,Nat.mul_zero,Nat.zero_le]
  have hm := twice_profile_volume_eq_twice_loss_add_triple_excess L hL g hg E x b hchain
  dsimp only [I] at hcount
  omega

end MinModulus
