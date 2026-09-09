import MinModulus.ExactCollisionLoss

namespace MinModulus
open Finset
open scoped Classical

/-- Distinct colliding box points have separated total weights. The spacing
is the full box diameter minus n, plus one, even when some arms are short. -/
theorem box_weight_spacing_of_valid_chain_forest_collision
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : ∀ i, Fin (2^(L i))) (hne : p ≠ q)
    (he : (∑ i, (p i).val • x i)=∑ i, (q i).val • x i) :
    (∑ i, (p i).val)+((∑ i, (2^(L i)-1))+1-n) ≤ (∑ i, (q i).val) ∨
      (∑ i, (q i).val)+((∑ i, (2^(L i)-1))+1-n) ≤ (∑ i, (p i).val) := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  have hp := forest_box_weight_add_distance L (fun i ↦ (p i).val) (fun i ↦ (p i).isLt)
  have hq := forest_box_weight_add_distance L (fun i ↦ (q i).val) (fun i ↦ (q i).isLt)
  have hne' : (fun i ↦ (p i).val) ≠ (fun i ↦ (q i).val) := by
    intro h
    apply hne
    funext i
    exact Fin.ext (congrFun h i)
  rcases box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain
    _ _ (fun i ↦ (p i).isLt) (fun i ↦ (q i).isLt) hne' he with h | h
  · right; omega
  · left; omega

/-- Divide weights into intervals of the proved spacing. At most one box
point per fibre can occupy each interval, giving a diameter-dependent bound. -/
theorem box_fibre_card_le_of_valid_chain_forest_diameter
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) :
    (forestBoxFibre L x z).card ≤
      (∑ i, (2^(L i)-1))/((∑ i, (2^(L i)-1))+1-n)+1 := by
  classical
  let D := ∑ i, (2^(L i)-1)
  let d := D+1-n
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnD : n ≤ D := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  have hd : 0 < d := by dsimp only [d]; omega
  let F := forestBoxFibre L x z
  have hsum : ∀ p : ∀ i, Fin (2^(L i)), (∑ i, (p i).val) ≤ D := by
    intro p
    apply Finset.sum_le_sum
    intro i _
    have h := (p i).isLt
    omega
  let f : F → Fin (D/d+1) := fun p ↦ ⟨(∑ i, (p.val i).val)/d,
    Nat.lt_succ_of_le (Nat.div_le_div_right (hsum p.val))⟩
  have hf : Function.Injective f := by
    intro p q he
    by_contra hpq
    have hne : p.val ≠ q.val := fun h ↦ hpq (Subtype.ext h)
    have hgroup : (∑ i, (p.val i).val • x i)=∑ i, (q.val i).val • x i :=
      (Finset.mem_filter.mp p.property).2.trans (Finset.mem_filter.mp q.property).2.symm
    have heq : (∑ i, (p.val i).val)/d=(∑ i, (q.val i).val)/d := congrArg Fin.val he
    have hpmod := Nat.mod_lt (∑ i, (p.val i).val) hd
    have hqmod := Nat.mod_lt (∑ i, (q.val i).val) hd
    have hpdecomp := Nat.mod_add_div (∑ i, (p.val i).val) d
    have hqdecomp := Nat.mod_add_div (∑ i, (q.val i).val) d
    rcases box_weight_spacing_of_valid_chain_forest_collision L hL g hg E x b hchain p.val q.val hne hgroup with h | h
    · change _+d ≤ _ at h
      rw [heq] at hpdecomp
      omega
    · change _+d ≤ _ at h
      rw [heq] at hpdecomp
      omega
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin,F,D,d] using h

/-- Multiplying the number of gaps in a fibre by the forced spacing never
exceeds the total box diameter. This retains the actual fibre cardinality. -/
theorem box_fibre_card_pred_mul_spacing_le_diameter
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) :
    ((forestBoxFibre L x z).card-1)*((∑ i, (2^(L i)-1))+1-n) ≤ ∑ i, (2^(L i)-1) := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnD : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  have hd : 0 < (∑ i, (2^(L i)-1))+1-n := by omega
  have h := box_fibre_card_le_of_valid_chain_forest_diameter L hL g hg E x b hchain z
  apply (Nat.le_div_iff_mul_le hd).mp
  simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right h 1

/-- A scalar multiple of the spacing covering n bounds every actual fibre,
interpolating below the previous two-point-fibre width threshold. -/
theorem box_fibre_card_le_of_spacing_multiple
    {n k : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hk : n ≤ k*((∑ i, (2^(L i)-1))+1-n)) (z : G) :
    (forestBoxFibre L x z).card ≤ k+1 := by
  let D := ∑ i, (2^(L i)-1)
  let d := D+1-n
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnD : n ≤ D := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  have hd : 0 < d := by dsimp only [d]; omega
  have hid : D+1=n+d := by dsimp only [d]; omega
  have hlt : D < (k+1)*d := by
    change n ≤ k*d at hk
    rw [Nat.add_mul,one_mul]
    omega
  have hdiv := (Nat.div_lt_iff_lt_mul hd).mpr hlt
  have h := box_fibre_card_le_of_valid_chain_forest_diameter L hL g hg E x b hchain z
  change _ ≤ D/d+1 at h
  omega

/-- An actual fibre with at least r points forces a small full profile
diameter. In particular, four-point fibres require 2*D+3 <= 3*n. -/
theorem large_box_fibre_forces_diameter_bound
    {n r : ℕ} (hr : 2 ≤ r) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (z : G) (hlarge : r ≤ (forestBoxFibre L x z).card) :
    (r-2)*(∑ i, (2^(L i)-1))+(r-1) ≤ (r-1)*n := by
  let D := ∑ i, (2^(L i)-1)
  let d := D+1-n
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnD : n ≤ D := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  have hid : D+1=n+d := by dsimp only [d]; omega
  have hgap : (r-1)*d ≤ D := by
    apply (Nat.mul_le_mul_right d (Nat.sub_le_sub_right hlarge 1)).trans
    exact box_fibre_card_pred_mul_spacing_le_diameter L hL g hg E x b hchain z
  have hbalance : (r-1)*D+(r-1)=(r-1)*n+(r-1)*d := by
    simpa only [Nat.mul_add,mul_one] using congrArg (fun k ↦ (r-1)*k) hid
  have hexpand : (r-1)*D=(r-2)*D+D := by
    rw [show r-1=(r-2)+1 by omega,Nat.add_mul,one_mul]
  rw [hexpand] at hbalance
  change (r-2)*D+(r-1) ≤ (r-1)*n
  omega

end MinModulus
