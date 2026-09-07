import MinModulus.ChainForestBoundary

/-! Supported genuine endpoints give distinct residues absent from the
whole binary box. Their count is charged to actual packing slack. Every
common relation factor has exact divided-direction order and divides
both modulus and slack. Direct original G1 consumers exclude insufficient
slack without unit, all-odd, or census premises. Larger charged slack,
short arms, and the unrestricted G1/G2/G3 gates remain open. -/

namespace MinModulus
open Finset

/-- Any set of residues avoided by the full binary box is charged
ADDITIVELY to the one-corner packing deficit. This retains arbitrary
arity and arbitrary finite abelian groups. -/
theorem box_card_bound_with_avoided_set_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (F : Finset G) (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) →
      (∑ i, p i • x i) ≠ z) :
    2^n+F.card ≤ Fintype.card G+(∏ i, (2^(L i)-d i)) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ ∀ i, d i ≤ (p i).val
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let CE : {p : B // C p} ≃ (∀ i, Fin (2^(L i)-d i)) :=
    { toFun := fun p i ↦ ⟨(p.val i).val-d i,by have := (p.val i).isLt; have := p.property i; omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+d i,by have := (p i).isLt; have := hd i; omega⟩,
        fun i ↦ Nat.le_add_left _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact Nat.sub_add_cancel (p.property i)
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have hcorner : Fintype.card {p : B // C p}=∏ i, (2^(L i)-d i) := by
    rw [Fintype.card_congr CE,Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hR : Fintype.card R=2^n-(∏ i, (2^(L i)-d i)) := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox,hcorner]
  have hfi : Function.Injective f := by
    have aux (p q : R) (he : f p=f q)
        (hle : ∀ i, (p.val i).val ≤ (q.val i).val) : p=q := by
      by_contra hne
      let u := fun i ↦ (q.val i).val-(p.val i).val
      have hu : ∀ i, u i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (q.val i).isLt
      have hupos : ∃ i, 0 < u i := by
        by_contra hnot
        push Not at hnot
        apply hne
        apply Subtype.ext
        funext i
        apply Fin.ext
        have h0 : (q.val i).val-(p.val i).val ≤ 0 := hnot i
        have := hle i
        omega
      have huzero := zero_relation_of_ordered_box_collision x
        (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val) hle he
      have heq := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
        g hg E x b hchain d u hd hu hdpos hupos hdzero huzero
      apply q.property
      intro i
      have hh := congrFun heq i
      dsimp only [u] at hh
      omega
    intro p q he
    rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain
        (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val)
        (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) he with h | h
    · exact aux p q he h
    · exact (aux q p he.symm h).symm
  let f' : R → {z : G // z ∉ F} := fun p ↦ ⟨f p,by
    intro hp
    exact havoid (f p) hp (fun i ↦ (p.val i).val) (fun i ↦ (p.val i).isLt) rfl⟩
  have hfi' : Function.Injective f' := by
    intro p q he
    exact hfi (congrArg Subtype.val he)
  have hbound := Fintype.card_le_of_injective f' hfi'
  have hremain : Fintype.card {z : G // z ∉ F}=Fintype.card G-F.card := by
    rw [Fintype.card_subtype_compl (fun z : G ↦ z ∈ F)]
    simp only [Fintype.card_coe]
  rw [hR,hremain] at hbound
  have hFcard : F.card ≤ Fintype.card G := Finset.card_le_univ F
  have hcorner_le : (∏ i, (2^(L i)-d i)) ≤ 2^n := by
    rw [← hcorner,← hbox]
    exact Fintype.card_subtype_le C
  omega

/-- A genuinely escaping supported boundary is absent from the
ENTIRE binary box, not just from the retained packing region. Every
representation would give a forbidden actual endpoint rejoin. -/
theorem boundary_not_in_box_of_genuine_supported_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a)
    (hgenuine : ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a := by
  classical
  intro heq
  have hpa := pivot_eq_zero_of_box_boundary_representation L hL hlong hwide g hg E x b hchain
    d hd hdzero a j hda hdj hja p hp heq.symm
  have hpos : ∃ i, 0 < p i := by
    by_contra hnot
    have hz : ∀ i, p i=0 := by intro i; by_contra hi; exact hnot ⟨i,by omega⟩
    have hzero : 2^(L a) • x a=0 := by simpa only [hz,zero_smul,Finset.sum_const_zero] using heq.symm
    exact boundary_ne_zero_of_two_supported_box_relation L hL hlong hwide g hg E x b hchain
      d hd hdzero a j hda hdj hja hzero
  have hcap : n ≤ (2^(L a)-1)+2^(L a) := (hlong a).trans (Nat.le_add_left _ _)
  obtain ⟨k,hka,e,he⟩ := actual_entry_of_valid_positive_forest_boundary L hL g hg E x b hchain a hcap p hp hpa heq.symm hpos
  apply hgenuine (E ⟨k,e⟩)
  have hseed := hchain a ⟨L a-1,by have := hL a; omega⟩
  have ht := hchain k e
  have hdouble : 2 • (2^(L a-1) • x a)=2^(L a) • x a := by
    rw [← mul_nsmul,← pow_succ,show L a-1+1=L a by have := hL a; omega]
  have hh := congrArg (fun v : G ↦ 2 • v) hseed
  rw [hdouble,he,← ht] at hh
  simp only [two_nsmul] at hh ⊢
  apply add_right_cancel (b := b)
  calc
    _=(g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)+
        (g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) := hh.symm
    _=_ := by abel

/-- Actual tuple-level doubling injectivity makes ALL chain boundary
residues distinct. No ambient doubling automorphism is assumed. -/
theorem boundary_map_injective_of_tuple_doubling_injective
    {n : ℕ} {β : Type*} (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    Function.Injective (fun a ↦ 2^(L a) • x a) := by
  let t := fun a ↦ E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩
  have hD : ∀ a, 2 • g (t a)+2 • b=2^(L a) • x a := by
    intro a
    rw [← smul_add]
    change 2 • (g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)=_
    rw [hchain,← mul_nsmul,← pow_succ,show L a-1+1=L a by have := hL a; omega]
  intro a j he
  have hd : 2 • g (t a)=2 • g (t j) := add_right_cancel ((hD a).trans (he.trans (hD j).symm))
  have ht := hinj hd
  have hE := E.injective ht
  exact congrArg (fun p : Σ i : β, Fin (L i) ↦ p.1) hE

/-- Every supported genuine endpoint costs a DISTINCT missing box
residue. Thus slack is at least the number of supported chains, at
arbitrary arity, not merely positive. Actual injectivity is retained. -/
theorem support_charged_box_card_bound_of_genuine_long_chain_forest
    {n : ℕ} (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) :
    2^n+(Finset.univ.filter (fun i ↦ 0 < d i)).card ≤
      Fintype.card G+(∏ i, (2^(L i)-d i)) := by
  classical
  have hwide := box_wide_of_three_le_long_chain_forest hr L hL hlong E
  obtain ⟨a₀,j₀,ha₀,hj₀,hja₀⟩ := exists_two_supported_coordinates_of_long_forest_zero_relation
    hn hr L hL hlong g hg E x b hchain d hd hdpos hdzero
  let S := Finset.univ.filter (fun i ↦ 0 < d i)
  let F := S.image (fun i ↦ 2^(L i) • x i)
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hda : 0 < d a := (Finset.mem_filter.mp ha).2
    obtain ⟨j,hj,hja⟩ : ∃ j, 0 < d j ∧ j ≠ a := by
      by_cases ha : a=a₀
      · exact ⟨j₀,hj₀,by simpa only [ha] using hja₀⟩
      · exact ⟨a₀,ha₀,Ne.symm ha⟩
    exact boundary_not_in_box_of_genuine_supported_long_chain_forest L hL hlong hwide g hg E x b hchain
      d hd hdzero a j hda hj hja (hgenuine a) p hp
  have hFcard : F.card=S.card := Finset.card_image_of_injective S
    (boundary_map_injective_of_tuple_doubling_injective L hL g hinj E x b hchain)
  have hh := box_card_bound_with_avoided_set_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd hdpos hdzero F havoid
  rwa [hFcard] at hh

/-- Dividing the unique actual box relation by ANY common factor
produces an element of exactly that order, in arbitrary arity. A smaller
order would create a second nonzero bounded relation. -/
theorem addOrderOf_divided_chain_forest_relation
    {n D : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    (hD : 0 < D) (r : β → ℕ) (hr : ∃ i, 0 < r i) (hDr : ∀ i, D*r i < 2^(L i))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hzero : (∑ i, (D*r i) • x i)=0) : addOrderOf (∑ i, r i • x i)=D := by
  let z := ∑ i, r i • x i
  have hkill : D • z=0 := by
    simpa only [z,Finset.smul_sum,← mul_nsmul,Nat.mul_comm] using hzero
  have hdvd : addOrderOf z ∣ D := addOrderOf_dvd_of_nsmul_eq_zero hkill
  have ho : 0 < addOrderOf z := by
    by_contra hnot
    have hz : addOrderOf z=0 := by omega
    rw [hz,zero_dvd_iff] at hdvd
    omega
  have hle : addOrderOf z ≤ D := Nat.le_of_dvd hD hdvd
  have hOr : ∀ i, addOrderOf z*r i < 2^(L i) := fun i ↦
    (Nat.mul_le_mul_right (r i) hle).trans_lt (hDr i)
  obtain ⟨a,ha⟩ := hr
  have hDpos : ∃ i, 0 < D*r i := ⟨a,mul_pos hD ha⟩
  have hOpos : ∃ i, 0 < addOrderOf z*r i := ⟨a,mul_pos ho ha⟩
  have hOzero : (∑ i, (addOrderOf z*r i) • x i)=0 := by
    simpa only [z,Finset.smul_sum,← mul_nsmul,Nat.mul_comm] using addOrderOf_nsmul_eq_zero z
  have he := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain (fun i ↦ D*r i) (fun i ↦ addOrderOf z*r i)
    hDr hOr hDpos hOpos hzero hOzero
  have hh := congrFun he a
  change addOrderOf z=D
  nlinarith only [hh,ha]

/-- Every common coefficient factor of the actual forest relation
divides the cyclic modulus. Individual seeds need not be units. -/
theorem common_factor_dvd_modulus_of_valid_long_chain_forest
    {n D N : ℕ} [NeZero N] {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    (hD : 0 < D) (r : β → ℕ) (hr : ∃ i, 0 < r i) (hDr : ∀ i, D*r i < 2^(L i))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hzero : (∑ i, (D*r i) • x i)=0) : D ∣ N := by
  have ho := addOrderOf_divided_chain_forest_relation L hL hlong hwide hD r hr hDr g hg E x b hchain hzero
  have hN : N • (∑ i, r i • x i)=0 := by
    rw [nsmul_eq_mul,(ZMod.natCast_eq_zero_iff N N).mpr (dvd_refl N),zero_mul]
  have hd := addOrderOf_dvd_of_nsmul_eq_zero hN
  rwa [ho] at hd

/-- The same common factor divides the ACTUAL packing slack. This
follows from exact order and product congruence, not a numerical gcd
assumption or a supplied determinant. -/
theorem common_factor_dvd_slack_of_valid_long_chain_forest
    {n D N : ℕ} [NeZero N] {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    (hD : 0 < D) (r : β → ℕ) (hr : ∃ i, 0 < r i) (hDr : ∀ i, D*r i < 2^(L i))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hzero : (∑ i, (D*r i) • x i)=0) :
    D ∣ N+(∏ i, (2^(L i)-D*r i))-2^n := by
  letI : NeZero D := ⟨hD.ne'⟩
  have hDN := common_factor_dvd_modulus_of_valid_long_chain_forest L hL hlong hwide hD r hr hDr
    g hg E x b hchain hzero
  have hNzero : (N : ZMod D)=0 := (ZMod.natCast_eq_zero_iff N D).mpr hDN
  have hDzero : (D : ZMod D)=0 := (ZMod.natCast_eq_zero_iff D D).mpr (dvd_refl D)
  have hp : ∀ i, ((2^(L i)-D*r i : ℕ) : ZMod D)=((2^(L i) : ℕ) : ZMod D) := by
    intro i
    rw [Nat.cast_sub (hDr i).le,Nat.cast_mul,hDzero,zero_mul,sub_zero]
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hprod : ((∏ i, (2^(L i)-D*r i) : ℕ) : ZMod D)=((2^n : ℕ) : ZMod D) := by
    rw [Nat.cast_prod]
    simp only [hp]
    rw [← Nat.cast_prod]
    congr 1
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  obtain ⟨a,ha⟩ := hr
  have hbound := box_card_bound_of_valid_long_chain_forest L hL hlong hwide g hg E x b hchain
    (fun i ↦ D*r i) hDr ⟨a,mul_pos hD ha⟩ hzero
  rw [ZMod.card] at hbound
  apply (ZMod.natCast_eq_zero_iff _ D).mp
  rw [Nat.cast_sub hbound,Nat.cast_add,hNzero,zero_add,hprod,sub_self]

/-- For ANY common divisor of the original relation coefficients,
the divided direction has that exact order, the divisor divides both
modulus and slack, and slack pays at least the MAXIMUM of the divisor
and the supported-boundary count. No gcd or unit normalization is used. -/
theorem common_factor_and_support_charged_forest_slack
    {n N D : ℕ} [NeZero N] (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) (hD : 0 < D) (hdiv : ∀ i, D ∣ d i) :
    addOrderOf (∑ i, (d i/D) • x i)=D ∧ D ∣ N ∧
      D ∣ N+(∏ i, (2^(L i)-d i))-2^n ∧
      max D (Finset.univ.filter (fun i ↦ 0 < d i)).card ≤ N+(∏ i, (2^(L i)-d i))-2^n := by
  classical
  have hwide := box_wide_of_three_le_long_chain_forest hr L hL hlong E
  let r := fun i ↦ d i/D
  have hEq : ∀ i, D*r i=d i := fun i ↦ Nat.mul_div_cancel' (hdiv i)
  have hrpos : ∃ i, 0 < r i := by
    obtain ⟨a,ha⟩ := hdpos
    refine ⟨a,?_⟩
    by_contra hnot
    have hz : r a=0 := by omega
    have hh := hEq a
    rw [hz,mul_zero] at hh
    omega
  have hDr : ∀ i, D*r i < 2^(L i) := by simpa only [hEq] using hd
  have hzero : (∑ i, (D*r i) • x i)=0 := by simpa only [hEq] using hdzero
  have horder := addOrderOf_divided_chain_forest_relation L hL hlong hwide hD r hrpos hDr g hg E x b hchain hzero
  have hDN := common_factor_dvd_modulus_of_valid_long_chain_forest L hL hlong hwide hD r hrpos hDr g hg E x b hchain hzero
  have hDS : D ∣ N+(∏ i, (2^(L i)-d i))-2^n := by
    simpa only [hEq] using common_factor_dvd_slack_of_valid_long_chain_forest L hL hlong hwide hD r hrpos hDr g hg E x b hchain hzero
  have hcharge := support_charged_box_card_bound_of_genuine_long_chain_forest hn hr L hL hlong
    g hg hinj E x b hchain hgenuine d hd hdpos hdzero
  have hstrict := strict_box_card_bound_of_genuine_long_chain_forest hn hr L hL hlong
    g hg E x b hchain hgenuine d hd hdpos hdzero
  rw [ZMod.card] at hcharge hstrict
  have hSpos : 0 < N+(∏ i, (2^(L i)-d i))-2^n := by omega
  have hDle := Nat.le_of_dvd hSpos hDS
  exact ⟨horder,hDN,hDS,max_le hDle (by omega)⟩

/-- Direct ORIGINAL-G1 consumer whenever a long three-chain corner
cannot pay for all its supported endpoint residues. This includes every
one-unit slack and every interior two-unit slack, in ALL dimensions. -/
theorem admitsValidTuple_half_of_critical_insufficient_slack_long_three_chain_forest
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a) (hlong : ∀ a, n+1 ≤ 2^(L a))
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val)
    (d : A → ℕ) (hd : ∀ a, d a < 2^(L a)) (hdpos : ∃ a, 0 < d a)
    (hdzero : (∑ a, d a • x a)=0)
    (hsmall : 2^(s+1)*q+(∏ a, (2^(L a)-d a)) <
      2^(n+1)+(Finset.univ.filter (fun a ↦ 0 < d a)).card) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half hq g hg hc A hA b hclosed hnohalf
  obtain ⟨hinj,_⟩ := injective_and_acyclic_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hr : 3 ≤ Fintype.card A := by simp only [Fintype.card_coe,hcard,le_refl]
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a.val a.property t
  have hh := support_charged_box_card_bound_of_genuine_long_chain_forest (by omega) hr L hL hlong
    g hg hinj E x b hchain hgen d hd hdpos hdzero
  rw [ZMod.card] at hh
  omega

/-- The original three-escape G1 residual supplies a short arm or
actual corner slack charged to EVERY supported endpoint and EVERY common
coefficient divisor. Divided relation orders are exact, not assumed. -/
theorem exists_short_arm_or_charged_slack_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    A.card=3 ∧ ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n+1 ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ Fin (n+1), ∃ x : A → ZMod (2^(s+1)*q),
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
      (∀ a : A, ∀ j, g j ≠ 2 • g a.val+b) ∧
      2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card ∧
      AddSubgroup.closure (Set.range x)=⊤ ∧
      ((∃ a, 2^(L a) < n+1) ∨ ∃ d : A → ℕ, (∀ a, d a < 2^(L a)) ∧
        (∃ a, 0 < d a) ∧ (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+3 ∧
        (∃ a e, 2^(L a)-d a=2^e) ∧
        2^(n+1)+(Finset.univ.filter (fun a ↦ 0 < d a)).card ≤ 2^(s+1)*q+∏ a, (2^(L a)-d a) ∧
        (∀ D : ℕ, 0 < D → (∀ a, D ∣ d a) →
          addOrderOf (∑ a, (d a/D) • x a)=D ∧ D ∣ 2^(s+1)*q ∧
          D ∣ 2^(s+1)*q+(∏ a, (2^(L a)-d a))-2^(n+1) ∧
          max D (Finset.univ.filter (fun a ↦ 0 < d a)).card ≤
            2^(s+1)*q+(∏ a, (2^(L a)-d a))-2^(n+1))) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  obtain ⟨hinj,_⟩ := injective_and_acyclic_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,?_⟩
  by_cases hlong : ∀ a, n+1 ≤ 2^(L a)
  · right
    have hN : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
      rw [ZMod.card]
      exact lt_of_lt_of_le hc (by unfold stratumBound; exact Nat.sub_le _ _)
    obtain ⟨d,hd,hpos,hzero,hcorner⟩ :=
      exists_small_corner_relation_of_valid_subbinary_long_chain_forest L hL hlong g hg E x b hchain hN
    have hAr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
    have hr : 3 ≤ Fintype.card A := by omega
    have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
      intro a t
      have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
      rw [he]
      exact hgenuine a t
    have hp := support_charged_box_card_bound_of_genuine_long_chain_forest (by omega) hr
      L hL hlong g hg hinj E x b hchain hgen d hd hpos hzero
    rw [hAr] at hcorner
    rw [ZMod.card] at hp
    refine ⟨d,hd,hpos,hzero,by omega,
      exists_power_corner_side_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hzero,hp,?_⟩
    intro D hD hdiv
    exact common_factor_and_support_charged_forest_slack (by omega) hr L hL hlong
      g hg hinj E x b hchain hgen d hd hpos hzero hD hdiv
  · left
    simpa only [not_forall,not_le] using hlong

end MinModulus
