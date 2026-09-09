import MinModulus.SmallIntrinsicLossFibres

namespace MinModulus
open Finset
open scoped Classical

/-- The ordered sum of binary distances is controlled coordinatewise:
each coordinate contributes twice the product of its two class sizes. -/
theorem twice_subset_family_support_sum_le
    {n : ℕ} (F : Finset (Finset (Fin n))) :
    2*(∑ U ∈ F, ∑ V ∈ F, ((U \ V) ∪ (V \ U)).card) ≤ n*F.card^2 := by
  classical
  have hcard (S : Finset (Fin n)) : S.card=∑ i : Fin n, if i ∈ S then 1 else 0 := by simp
  have hi (i : Fin n) :
      2*(∑ U ∈ F, ∑ V ∈ F, if i ∈ ((U \ V) ∪ (V \ U)) then 1 else 0) ≤ F.card^2 := by
    let a := (F.filter (fun U ↦ i ∈ U)).card
    let b := (F.filter (fun U ↦ i ∉ U)).card
    have hab : a+b=F.card := by
      exact Finset.card_filter_add_card_filter_not _
    have hinner (U : Finset (Fin n)) :
        (∑ V ∈ F, if i ∈ ((U \ V) ∪ (V \ U)) then 1 else 0)=if i ∈ U then b else a := by
      by_cases hU : i ∈ U
      · have hb : (∑ V ∈ F, if i ∉ V then 1 else 0)=b := by rw [← Finset.sum_filter]; simp [b]
        simpa [Finset.mem_union,Finset.mem_sdiff,hU,ite_not] using hb
      · simp [Finset.mem_union,Finset.mem_sdiff,hU,a,b]
    simp_rw [hinner]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change 2*(a*b+b*a) ≤ F.card^2
    rcases le_total a b with h | h
    · obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le h
      nlinarith [Nat.zero_le (c*c)]
    · obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le h
      nlinarith [Nat.zero_le (c*c)]
  calc
    _ = ∑ i : Fin n, 2*(∑ U ∈ F, ∑ V ∈ F, if i ∈ ((U \ V) ∪ (V \ U)) then 1 else 0) := by
      simp_rw [hcard]
      simp_rw [Finset.sum_comm (s:=F) (t:=Finset.univ)]
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin n, F.card^2 := Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = n*F.card^2 := by simp

/-- A uniform lower bound on pairwise binary support controls the size
of any finite subset family by coordinate disagreement counting. -/
theorem subset_family_card_support_bound
    {n k : ℕ} (F : Finset (Finset (Fin n)))
    (hsep : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → n ≤ ((U \ V) ∪ (V \ U)).card+k) :
    (F.card-2)*n ≤ 2*(F.card-1)*k := by
  classical
  have hconst (c : ℕ) :
      (∑ U ∈ F, ∑ V ∈ F, if U=V then 0 else c)=F.card*(F.card-1)*c := by
    have hinner (U : Finset (Fin n)) (hU : U ∈ F) :
        (∑ V ∈ F, if U=V then 0 else c)=(F.card-1)*c := by
      rw [Finset.sum_ite]
      simp [Finset.filter_ne,Finset.card_erase_of_mem hU]
    rw [Finset.sum_congr rfl hinner]
    simp [Nat.mul_assoc]
  have hlower : F.card*(F.card-1)*n ≤
      (∑ U ∈ F, ∑ V ∈ F, ((U \ V) ∪ (V \ U)).card)+F.card*(F.card-1)*k := by
    rw [← hconst n,← hconst k,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro U hU
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro V hV
    by_cases he : U=V
    · simp [he]
    · simpa only [if_neg he] using hsep U hU V hV he
  have hupper := twice_subset_family_support_sum_le F
  by_cases hm : F.card ≤ 2
  · have hz : F.card-2=0 := by omega
    simp [hz]
  · have hm0 : 0 < F.card := by omega
    have hid : 2*(F.card*(F.card-1)*n)=F.card*((F.card-2)*n)+n*F.card^2 := by
      have hc : F.card=(F.card-2)+2 := by omega
      generalize F.card-2=t at hc ⊢
      rw [hc]
      have ht : t+2-1=t+1 := by omega
      rw [ht]
      ring
    have hmul : F.card*((F.card-2)*n) ≤ F.card*(2*(F.card-1)*k) := by
      nlinarith only [hlower,hupper,hid]
    exact (Nat.mul_le_mul_left_iff hm0).mp hmul

/-- Every shifted subset-sum fibre satisfies a dimension/loss/cardinality
inequality, without validity or finiteness of the ambient group. -/
theorem tuple_subset_fibre_card_intrinsic_loss_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-2)*n ≤
      2*((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
        Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  classical
  apply subset_family_card_support_bound
  intro U hU V hV hne
  exact dimension_le_collision_support_add_log_loss g b U V hne
    ((Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm)

/-- Every complete forest encoding inherits the same intrinsic bound
on arbitrary fibre cardinality. -/
theorem forest_fibre_card_intrinsic_loss_bound
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) :
    ((forestBoxFibre L x z).card-2)*n ≤
      2*((forestBoxFibre L x z).card-1)*Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  unfold forestBoxFibre
  rw [forest_box_filter_card_eq_subset_filter_card L g E x b hchain (fun t ↦ t=z)]
  exact tuple_subset_fibre_card_intrinsic_loss_bound g b z

/-- Solving the support cardinality inequality gives a finite bound
whenever twice the loss exponent is smaller than the dimension. -/
theorem card_le_quotient_of_support_bound
    {m n k : ℕ} (hbound : (m-2)*n ≤ 2*(m-1)*k) (hsmall : 2*k < n) :
    m ≤ (2*(n-k))/(n-2*k) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < n-2*k)).mpr
  by_cases hm : m ≤ 2
  · calc
      m*(n-2*k) ≤ 2*(n-2*k) := Nat.mul_le_mul_right _ hm
      _ ≤ 2*(n-k) := Nat.mul_le_mul_left _ (by omega)
  · have hm1 : m-1=(m-2)+1 := by omega
    have hm2 : m=(m-2)+2 := by omega
    have hn : n=(n-2*k)+2*k := by omega
    have hnk : n-k=(n-2*k)+k := by omega
    rw [hm1,hn] at hbound
    rw [hm2,hnk]
    nlinarith only [hbound]

/-- Explicit intrinsic fibre-size bound in the sub-half-dimension
loss-exponent regime. Natural division takes the integer part. -/
theorem tuple_subset_fibre_card_le_intrinsic_quotient
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤
      (2*(n-Nat.log 2 (tupleBinaryCollisionLoss g b)))/
        (n-2*Nat.log 2 (tupleBinaryCollisionLoss g b)) := by
  exact card_le_quotient_of_support_bound (tuple_subset_fibre_card_intrinsic_loss_bound g b z) hsmall

/-- The explicit intrinsic quotient bound is unchanged by actual forest
regrouping and requires no wide-arm or tuple-validity assumption. -/
theorem forest_fibre_card_le_intrinsic_quotient
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    (forestBoxFibre L x z).card ≤
      (2*(n-Nat.log 2 (tupleBinaryCollisionLoss g b)))/
        (n-2*Nat.log 2 (tupleBinaryCollisionLoss g b)) := by
  exact card_le_quotient_of_support_bound
    (forest_fibre_card_intrinsic_loss_bound L g E x b hchain z) hsmall

end MinModulus
