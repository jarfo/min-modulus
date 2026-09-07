import MinModulus.ChainForestSlack

/-! Exact parity-resolved one-corner packing, at arbitrary arity.
Supported genuine boundaries are distinct EVEN residues missing from the
whole box. Actual slack S and the explicit corner bias B satisfy S+B ≥ 2m.
An odd number of odd seeds forces B=0. Direct original G1 consumers retain
mixed parities, nonunit seeds, all corner axes, and prior divisor charges.
Larger slack, short arms, and the unrestricted G1/G2/G3 gates remain open. -/

namespace MinModulus
open Finset

/-- The integer sign character records twice the even fibre minus
the whole finite set. This is an exact count, not an asymptotic bound. -/
theorem sign_sum_eq_two_even_card_sub_card
    {α : Type*} (S : Finset α) (f : α → ℕ) :
    (∑ a ∈ S, (-1 : ℤ)^(f a))=
      2*((S.filter (fun a ↦ Even (f a))).card : ℤ)-(S.card : ℤ) := by
  classical
  have hp : ∀ a, (-1 : ℤ)^(f a)=2*(if Even (f a) then 1 else 0)-1 := by
    intro a
    rw [neg_one_pow_eq_ite]
    split_ifs <;> norm_num
  simp only [hp,Finset.sum_sub_distrib,← Finset.mul_sum]
  have hh : (∑ a ∈ S, if Even (f a) then (1 : ℤ) else 0)=((S.filter (fun a ↦ Even (f a))).card : ℤ) := by simp
  rw [hh]
  simp

/-- Exact parity bias of one interval: an even seed contributes the
whole length; an odd seed contributes zero or one according to length. -/
theorem interval_sign_sum_eq_parity_bias (A e : ℕ) :
    (∑ i : Fin A, (-1 : ℤ)^(i.val*e))=
      if Even e then (A : ℤ) else if Even A then 0 else 1 := by
  have hp : ∀ i : Fin A, (-1 : ℤ)^(i.val*e)=((-1 : ℤ)^e)^i.val := by
    intro i
    rw [Nat.mul_comm,pow_mul]
  simp only [hp]
  by_cases he : Even e
  · rw [show (-1 : ℤ)^e=1 by simp only [neg_one_pow_eq_ite,if_pos he],if_pos he]
    simp
  · rw [show (-1 : ℤ)^e=(-1) by simp only [neg_one_pow_eq_ite,if_neg he],if_neg he]
    exact Fin.sum_neg_one_pow ℤ A

/-- The exact parity bias of an arbitrary-dimensional integer box
is the product of its one-coordinate biases. All seed parities remain
explicit; this does not assume that every seed is odd. -/
theorem box_sign_sum_eq_product_parity_bias
    {β : Type*} [Fintype β] [DecidableEq β] (A e : β → ℕ) :
    (∑ p : (∀ i, Fin (A i)), (-1 : ℤ)^(∑ i, (p i).val*e i))=
      ∏ i, (if Even (e i) then (A i : ℤ) else if Even (A i) then 0 else 1) := by
  classical
  have hp := Finset.prod_univ_sum (fun i ↦ (Finset.univ : Finset (Fin (A i))))
    (fun i (j : Fin (A i)) ↦ (-1 : ℤ)^(j.val*e i))
  simp only [Fintype.piFinset_univ] at hp
  calc
    _=∑ p : (∀ i, Fin (A i)), ∏ i, (-1 : ℤ)^((p i).val*e i) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ (p i).val*e i) (-1 : ℤ)).symm
    _=∏ i, ∑ j : Fin (A i), (-1 : ℤ)^(j.val*e i) := hp.symm
    _=_ := by simp only [interval_sign_sum_eq_parity_bias]

/-- Exact even-fibre cardinality of an arbitrary weighted integer
box: twice its even count is its volume plus the explicit parity bias. -/
theorem twice_even_box_card_eq_volume_add_parity_bias
    {β : Type*} [Fintype β] [DecidableEq β] (A e : β → ℕ) :
    2*((Finset.univ.filter (fun p : (∀ i, Fin (A i)) ↦ Even (∑ i, (p i).val*e i))).card : ℤ)=
      ((∏ i, A i : ℕ) : ℤ)+
      ∏ i, (if Even (e i) then (A i : ℤ) else if Even (A i) then 0 else 1) := by
  have hs := sign_sum_eq_two_even_card_sub_card Finset.univ (fun p : (∀ i, Fin (A i)) ↦ ∑ i, (p i).val*e i)
  rw [box_sign_sum_eq_product_parity_bias] at hs
  simp only [Finset.card_univ,Fintype.card_pi,Fintype.card_fin] at hs
  omega

/-- Actual cyclic group parity agrees with the original natural
weighted sum when the modulus is even. No seed is replaced by a unit. -/
theorem parity_val_of_finite_seed_sum
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (c : β → ℕ) (x : β → ZMod N) :
    (∑ i, c i • x i).val % 2=(∑ i, c i*(x i).val) % 2 := by
  have hc : (∑ i, c i • x i)=((∑ i, c i*(x i).val : ℕ) : ZMod N) := by
    simp only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [hc,ZMod.val_natCast,Nat.mod_mod_of_dvd _ hN]

/-- Exact even-fibre size for an actual cyclic seed box. The bias
retains every even-seed side and every odd-seed side parity. -/
theorem twice_even_cyclic_box_card_eq_volume_add_parity_bias
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (A : β → ℕ) (x : β → ZMod N) :
    2*((Finset.univ.filter (fun p : (∀ i, Fin (A i)) ↦ Even (∑ i, (p i).val • x i).val)).card : ℤ)=
      ((∏ i, A i : ℕ) : ℤ)+
      ∏ i, (if Even (x i).val then (A i : ℤ) else if Even (A i) then 0 else 1) := by
  have hp : ∀ p : (∀ i, Fin (A i)), Even (∑ i, (p i).val • x i).val ↔
      Even (∑ i, (p i).val*(x i).val) := by
    intro p
    rw [Nat.even_iff,Nat.even_iff,parity_val_of_finite_seed_sum hN]
  simp only [hp]
  exact twice_even_box_card_eq_volume_add_parity_bias A (fun i ↦ (x i).val)

/-- Packing after removal of one exceptional domain region works
inside ANY target fibre. Avoided residues are charged only in that fibre. -/
theorem fibre_card_bound_with_avoided_set
    {α G : Type*} [Fintype α] [DecidableEq G]
    (f : α → G) (C : α → Prop) [DecidablePred C]
    (hi : Function.Injective (fun p : {p : α // ¬ C p} ↦ f p.val))
    (V F : Finset G) (hFV : F ⊆ V) (havoid : ∀ z ∈ F, ∀ p, f p ≠ z) :
    (Finset.univ.filter (fun p ↦ f p ∈ V)).card+F.card ≤
      V.card+(Finset.univ.filter (fun p ↦ f p ∈ V ∧ C p)).card := by
  classical
  let S := Finset.univ.filter (fun p ↦ f p ∈ V)
  let R := S.filter (fun p ↦ ¬ C p)
  have hRi : Set.InjOn f R := by
    intro p hp q hq he
    have hp' : ¬ C p := (Finset.mem_filter.mp hp).2
    have hq' : ¬ C q := (Finset.mem_filter.mp hq).2
    exact congrArg Subtype.val (hi (a₁ := ⟨p,hp'⟩) (a₂ := ⟨q,hq'⟩) he)
  have hdis : Disjoint (R.image f) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hzF
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
    exact havoid (f p) hzF p rfl
  have hsub : R.image f ∪ F ⊆ V := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    · exact hFV hz
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,Finset.card_image_iff.mpr hRi] at hc
  have hs := Finset.card_filter_add_card_filter_not (s := S) C
  have hC : (S.filter C).card=(Finset.univ.filter (fun p ↦ f p ∈ V ∧ C p)).card := by
    simp only [S,Finset.filter_filter]
  rw [hC] at hs
  change R.card+F.card ≤ V.card at hc
  change _+R.card=S.card at hs
  change S.card+F.card ≤ _
  omega

/-- The even residues occupy exactly half an even cyclic group. -/
theorem twice_even_cyclic_card_eq_modulus
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) :
    2*((Finset.univ.filter (fun z : ZMod N ↦ Even z.val)).card : ℤ)=(N : ℤ) := by
  let e : ZMod N ≃ Fin N :=
    { toFun := fun z ↦ ⟨z.val,z.val_lt⟩
      invFun := fun i ↦ (i.val : ZMod N)
      left_inv := fun z ↦ ZMod.natCast_zmod_val z
      right_inv := fun i ↦ Fin.ext (by simp only [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]) }
  have hs := sign_sum_eq_two_even_card_sub_card Finset.univ (fun z : ZMod N ↦ z.val)
  have ht : (∑ z : ZMod N, (-1 : ℤ)^z.val)=0 := by
    calc
      _=∑ i : Fin N, (-1 : ℤ)^i.val := (e.sum_comp (fun i : Fin N ↦ (-1 : ℤ)^i.val))
      _=0 := by rw [Fin.sum_neg_one_pow,if_pos (even_iff_two_dvd.mpr hN)]
  rw [ht] at hs
  simp only [Finset.card_univ,ZMod.card] at hs
  omega

/-- The actual long-forest one-corner packing bound restricted to
an arbitrary target fibre, with every avoided fibre residue charged. -/
theorem fibre_card_bound_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (V F : Finset G) (hFV : F ⊆ V)
    (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z) :
    (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦ (∑ i, (p i).val • x i) ∈ V)).card+F.card ≤
      V.card+(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
        (∑ i, (p i).val • x i) ∈ V ∧ ∀ i, d i ≤ (p i).val)).card := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ ∀ i, d i ≤ (p i).val
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
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
  exact fibre_card_bound_with_avoided_set (fun p : B ↦ ∑ i, (p i).val • x i) C hfi V F hFV
    (fun z hz p ↦ havoid z hz (fun i ↦ (p i).val) (fun i ↦ (p i).isLt))

/-- Translating the upper corner by its ACTUAL zero relation does
not change group values. Its even count therefore has the same exact
product bias as the smaller box of corner side lengths. -/
theorem twice_even_upper_corner_card_eq_volume_add_parity_bias
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (K d : β → ℕ) (hd : ∀ i, d i < K i) (x : β → ZMod N)
    (hdzero : (∑ i, d i • x i)=0) :
    2*((Finset.univ.filter (fun p : (∀ i, Fin (K i)) ↦
      Even (∑ i, (p i).val • x i).val ∧ ∀ i, d i ≤ (p i).val)).card : ℤ)=
      ((∏ i, (K i-d i) : ℕ) : ℤ)+
      ∏ i, (if Even (x i).val then ((K i-d i : ℕ) : ℤ) else if Even (K i-d i) then 0 else 1) := by
  classical
  let B := ∀ i, Fin (K i)
  let C : B → Prop := fun p ↦ ∀ i, d i ≤ (p i).val
  let Q := ∀ i, Fin (K i-d i)
  let E₀ : {p : B // C p} ≃ Q :=
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
  have hvalue : ∀ p : {p : B // C p}, (∑ i, (p.val i).val • x i)=(∑ i, (E₀ p i).val • x i) := by
    intro p
    calc
      _=∑ i, (((p.val i).val-d i)+d i) • x i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.sub_add_cancel (p.property i)]
      _=_ := by simp only [add_nsmul,Finset.sum_add_distrib,hdzero,add_zero]; rfl
  let E₁ : {p : B // Even (∑ i, (p i).val • x i).val ∧ C p} ≃
      {q : Q // Even (∑ i, (q i).val • x i).val} :=
    { toFun := fun p ↦ ⟨E₀ ⟨p.val,p.property.2⟩,by
        rw [← hvalue]
        exact p.property.1⟩
      invFun := fun q ↦ ⟨(E₀.symm q.val).val,by
        constructor
        · rw [hvalue,E₀.apply_symm_apply]
          exact q.property
        · exact (E₀.symm q.val).property⟩
      left_inv := by
        intro p
        apply Subtype.ext
        change (E₀.symm (E₀ ⟨p.val,p.property.2⟩)).val=p.val
        rw [E₀.symm_apply_apply]
      right_inv := by
        intro q
        apply Subtype.ext
        exact E₀.apply_symm_apply q.val }
  have hc := Fintype.card_congr E₁
  simp only [Fintype.card_subtype] at hc
  rw [hc]
  exact twice_even_cyclic_box_card_eq_volume_add_parity_bias hN (fun i ↦ K i-d i) x

/-- A binary box with one odd seed has exactly balanced parity.
No hypothesis is placed on any other seed's parity or invertibility. -/
theorem twice_even_binary_box_card_eq_two_pow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hsize : (∑ i, L i)=n)
    (x : β → ZMod N) (hodd : ∃ a, Odd (x a).val) :
    2*((Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      Even (∑ i, (p i).val • x i).val)).card : ℤ)=((2^n : ℕ) : ℤ) := by
  classical
  have hh := twice_even_cyclic_box_card_eq_volume_add_parity_bias hN (fun i ↦ 2^(L i)) x
  have hb : (∏ i, (if Even (x i).val then ((2^(L i) : ℕ) : ℤ) else if Even (2^(L i)) then 0 else 1))=0 := by
    obtain ⟨a,ha⟩ := hodd
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    have he : Even (2^(L a)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL a; omega))
    rw [if_neg (Nat.not_even_iff_odd.mpr ha),if_pos he]
  rw [hb,add_zero,Finset.prod_pow_eq_pow_sum,hsize] at hh
  exact hh

/-- Even scalar multiples are actual even residues at even modulus. -/
theorem even_val_of_even_nsmul
    {N k : ℕ} [NeZero N] (hN : 2 ∣ N) (hk : Even k) (z : ZMod N) :
    Even (k • z).val := by
  have hc : k • z=((k*z.val : ℕ) : ZMod N) := by
    simp only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [hc,ZMod.val_natCast,Nat.even_iff,Nat.mod_mod_of_dvd _ hN,Nat.mul_mod,Nat.even_iff.mp hk]
  simp

/-- Every avoided EVEN residue costs two units in the parity-resolved
packing inequality. The only correction is the exact corner bias. -/
theorem even_avoided_box_card_bound_of_valid_long_chain_forest
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (F : Finset (ZMod N)) (heven : ∀ z ∈ F, Even z.val)
    (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z) :
    ((2^n : ℕ) : ℤ)+2*(F.card : ℤ) ≤ (N : ℤ)+((∏ i, (2^(L i)-d i) : ℕ) : ℤ)+
      ∏ i, (if Even (x i).val then ((2^(L i)-d i : ℕ) : ℤ) else if Even (2^(L i)-d i) then 0 else 1) := by
  classical
  let V := Finset.univ.filter (fun z : ZMod N ↦ Even z.val)
  have hFV : F ⊆ V := fun z hz ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,heven z hz⟩
  have hh := fibre_card_bound_of_valid_long_chain_forest L hL hlong hwide g hg E x b hchain
    d hd hdpos hdzero V F hFV havoid
  simp only [V,Finset.mem_filter,Finset.mem_univ,true_and] at hh
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hB := twice_even_binary_box_card_eq_two_pow hN L hL hsize x hodd
  have hC := twice_even_upper_corner_card_eq_volume_add_parity_bias hN (fun i ↦ 2^(L i)) d hd x hdzero
  have hV := twice_even_cyclic_card_eq_modulus hN
  omega

/-- Actual distinct supported boundaries are all EVEN and absent
from the entire box. The parity fibre therefore forces S+bias ≥ 2*support,
at arbitrary arity and with every seed parity retained. -/
theorem parity_charged_box_card_bound_of_genuine_long_chain_forest
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) (hn : 2 ≤ n) {β : Type*} [Fintype β] [DecidableEq β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hodd : ∃ a, Odd (x a).val)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) :
    ((2^n : ℕ) : ℤ)+2*((Finset.univ.filter (fun i ↦ 0 < d i)).card : ℤ) ≤
      (N : ℤ)+((∏ i, (2^(L i)-d i) : ℕ) : ℤ)+
      ∏ i, (if Even (x i).val then ((2^(L i)-d i : ℕ) : ℤ) else if Even (2^(L i)-d i) then 0 else 1) := by
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
  have heven : ∀ z ∈ F, Even z.val := by
    intro z hz
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hz
    exact even_val_of_even_nsmul hN
      (even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL a; omega))) (x a)
  have hh := even_avoided_box_card_bound_of_valid_long_chain_forest hN L hL hlong hwide
    g hg E x b hchain hodd d hd hdpos hdzero F heven havoid
  rwa [hFcard] at hh

/-- Direct ORIGINAL-G1 half descent whenever the actual corner
cannot pay the EVEN-fibre boundary charge. Odd seeds are extracted from
failed descent, not supplied as an extra normalization. -/
theorem admitsValidTuple_half_of_critical_insufficient_parity_slack_long_three_chain_forest
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
    (hsmall : ((2^(s+1)*q : ℕ) : ℤ)+((∏ a, (2^(L a)-d a) : ℕ) : ℤ)+
      (∏ a, (if Even (x a).val then ((2^(L a)-d a : ℕ) : ℤ) else if Even (2^(L a)-d a) then 0 else 1)) <
      ((2^(n+1) : ℕ) : ℤ)+2*((Finset.univ.filter (fun a ↦ 0 < d a)).card : ℤ)) :
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
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hNeven : 2 ∣ 2^(s+1)*q := by rw [hN]; exact dvd_mul_right 2 _
  have ho := two_le_odd_seed_card_of_chain_forest_without_half hN hNeven L hL g hg E x b hchain hnohalf
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a ↦ ZMod.castHom hNeven (ZMod 2) (x a)=1)).card)
  have hodd : ∃ a, Odd (x a).val := ⟨a,odd_val_of_parity_eq_one hNeven (x a) (Finset.mem_filter.mp ha).2⟩
  have hh := parity_charged_box_card_bound_of_genuine_long_chain_forest hNeven (by omega) hr L hL hlong
    g hg hinj E x b hchain hgen hodd d hd hdpos hdzero
  omega

/-- The original critical residual retains all previous support and
exact-order charges AND the stronger exact even-fibre charge, on the
same actual corner. No new global gate or all-odd premise is introduced. -/
theorem exists_short_arm_or_parity_charged_slack_of_critical_three_escape_without_half
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
        (((2^(n+1) : ℕ) : ℤ)+2*((Finset.univ.filter (fun a ↦ 0 < d a)).card : ℤ) ≤
          ((2^(s+1)*q : ℕ) : ℤ)+((∏ a, (2^(L a)-d a) : ℕ) : ℤ)+
          ∏ a, (if Even (x a).val then ((2^(L a)-d a : ℕ) : ℤ) else if Even (2^(L a)-d a) then 0 else 1)) ∧
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
    have hNeven : 2 ∣ 2^(s+1)*q := by rw [pow_succ',mul_assoc]; exact dvd_mul_right 2 _
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a ↦ Odd (x a).val)).card)
    have ho : ∃ a, Odd (x a).val := ⟨a,(Finset.mem_filter.mp ha).2⟩
    have hparity := parity_charged_box_card_bound_of_genuine_long_chain_forest hNeven (by omega) hr L hL hlong
      g hg hinj E x b hchain hgen ho d hd hpos hzero
    refine ⟨d,hd,hpos,hzero,by omega,
      exists_power_corner_side_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hzero,hp,hparity,?_⟩
    intro D hD hdiv
    exact common_factor_and_support_charged_forest_slack (by omega) hr L hL hlong
      g hg hinj E x b hchain hgen d hd hpos hzero hD hdiv
  · left
    simpa only [not_forall,not_le] using hlong

/-- A zero relation forces ZERO corner bias when the number of odd
seeds is odd. Otherwise every odd seed would have an odd coefficient,
making the actual zero relation odd. This applies at arbitrary arity. -/
theorem corner_parity_bias_eq_zero_of_odd_odd_seed_card
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (d : β → ℕ) (hd : ∀ i, d i < 2^(L i))
    (x : β → ZMod N) (hdzero : (∑ i, d i • x i)=0)
    (hodd : Odd (Finset.univ.filter (fun i ↦ Odd (x i).val)).card) :
    (∏ i, (if Even (x i).val then ((2^(L i)-d i : ℕ) : ℤ) else if Even (2^(L i)-d i) then 0 else 1))=0 := by
  classical
  by_contra hnz
  have hdi : ∀ i, Odd (x i).val → Odd (d i) := by
    intro i hi
    have hside : ¬ Even (2^(L i)-d i) := by
      intro he
      apply hnz
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_neg (Nat.not_even_iff_odd.mpr hi),if_pos he]
    have hK : Even (2^(L i)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL i; omega))
    have hbound := hd i
    rw [Nat.even_iff] at hside hK
    rw [Nat.odd_iff]
    omega
  have hpred : ∀ i, Odd (d i*(x i).val) ↔ Odd (x i).val := by
    intro i
    rw [Nat.odd_mul]
    exact ⟨And.right,fun hi ↦ ⟨hdi i hi,hi⟩⟩
  have he : Even (∑ i, d i*(x i).val) := by
    rw [Nat.even_iff,← parity_val_of_finite_seed_sum hN d x,hdzero]
    simp
  rw [Finset.even_sum_iff_even_card_odd] at he
  simp only [hpred] at he
  exact (Nat.not_even_iff_odd.mpr hodd) he

/-- An odd number of odd seeds removes the bias ENTIRELY: every
supported genuine boundary costs two full units of actual slack. In
particular this covers every all-odd genuine three-chain forest. -/
theorem twice_support_charged_box_card_bound_of_odd_seed_count
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) (hn : 2 ≤ n)
    {β : Type*} [Fintype β] [DecidableEq β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hodd : Odd (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) :
    2^n+2*(Finset.univ.filter (fun i ↦ 0 < d i)).card ≤ N+∏ i, (2^(L i)-d i) := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hodd.pos
  have ho : ∃ a, Odd (x a).val := ⟨a,(Finset.mem_filter.mp ha).2⟩
  have hh := parity_charged_box_card_bound_of_genuine_long_chain_forest hN hn hr L hL hlong
    g hg hinj E x b hchain hgenuine ho d hd hdpos hdzero
  rw [corner_parity_bias_eq_zero_of_odd_odd_seed_card hN L hL d hd x hdzero hodd,add_zero] at hh
  exact_mod_cast hh

end MinModulus
