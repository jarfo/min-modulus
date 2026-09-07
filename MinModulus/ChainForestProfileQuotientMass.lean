import MinModulus.ChainForestProfileQuotient

/-! Quantitative profile packing in every dominant quotient class.
The actual quotient index scales each separate profile mass. Exact
dyadic strata force a power-of-two lower mass in every class. These
constraints retain all arms; the sharp global conjecture remains open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- A forest box fibre over a subgroup containing one seed splits into
that entire axis and the corresponding companion fibre. -/
theorem forest_coset_fibre_card_eq_axis_mul_companion
    {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (x : β → G) (j : β)
    (H : AddSubgroup G) (hx : x j ∈ H) (r : G) :
    Nat.card {p : (∀ i, Fin (2^(L i))) // (∑ i, (p i).val • x i)-r ∈ H}=
      2^(L j)*Nat.card {p : (∀ i : {i : β // i ≠ j}, Fin (2^(L i.val))) //
        QuotientAddGroup.mk' H (∑ i, (p i).val • x i.val)=QuotientAddGroup.mk' H r} := by
  classical
  let C := {i : β // i ≠ j}
  let B := ∀ i : C, Fin (2^(L i.val))
  let π := QuotientAddGroup.mk' H
  let v : B → G := fun p ↦ ∑ i, (p i).val • x i.val
  let D := {p : B // π (v p)=π r}
  let T := {p : (∀ i, Fin (2^(L i))) // (∑ i, (p i).val • x i)-r ∈ H}
  let P : Fin (2^(L j)) × D → (∀ i, Fin (2^(L i))) := fun p i ↦
    if hi : i=j then hi.symm ▸ p.1 else p.2.val ⟨i,hi⟩
  have hsplit : ∀ q : (∀ i, Fin (2^(L i))),
      (∑ i, (q i).val • x i)=(q j).val • x j+v (fun i ↦ q i.val) := by
    intro q
    rw [← (Equiv.optionSubtypeNe j).sum_comp (fun i ↦ (q i).val • x i),Fintype.sum_option]
    rfl
  have hval : ∀ p, (∑ i, (P p i).val • x i)=p.1.val • x j+v p.2.val := by
    intro p
    rw [hsplit]
    simp only [P,dif_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [dif_neg i.property]
    rfl
  have hxzero : π (x j)=0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
  have hmem : ∀ p, (∑ i, (P p i).val • x i)-r ∈ H := by
    intro p
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change π ((∑ i, (P p i).val • x i)-r)=0
    rw [hval,map_sub,map_add,map_nsmul,hxzero,nsmul_zero,zero_add,p.2.property,sub_self]
  let F : Fin (2^(L j)) × D → T := fun p ↦ ⟨P p,hmem p⟩
  have hi : Function.Injective F := by
    intro p q he
    have hP : P p=P q := congrArg Subtype.val he
    apply Prod.ext
    · have hj := congrFun hP j
      simpa only [P,dif_pos rfl] using hj
    · apply Subtype.ext
      funext i
      have hh := congrFun hP i.val
      simpa only [P,dif_neg i.property] using hh
  have hs : Function.Surjective F := by
    intro q
    have hq : π (v (fun i ↦ q.val i.val))=π r := by
      have hh := (QuotientAddGroup.eq_zero_iff _).mpr q.property
      change π ((∑ i, (q.val i).val • x i)-r)=0 at hh
      rw [hsplit,map_sub,map_add,map_nsmul,hxzero,nsmul_zero,zero_add,sub_eq_zero] at hh
      exact hh
    refine ⟨(q.val j,⟨fun i ↦ q.val i.val,hq⟩),?_⟩
    apply Subtype.ext
    funext i
    dsimp only [F,P]
    split_ifs with hij
    · subst i; rfl
    · rfl
  have hh := Fintype.card_congr (Equiv.ofBijective F ⟨hi,hs⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin,T,D,B,C,π,v] using hh.symm

/-- Every coset of a finite subgroup has the subgroup's cardinality. -/
theorem forest_target_coset_card
    {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) (r : G) :
    (Finset.univ.filter (fun z : G ↦ z-r ∈ H)).card=Nat.card H := by
  classical
  let E : {z : G // z-r ∈ H} ≃ H :=
    { toFun := fun z ↦ ⟨z.val-r,z.property⟩
      invFun := fun h ↦ ⟨h.val+r,by simpa only [add_sub_cancel_right] using h.property⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro h; apply Subtype.ext; simp }
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using Fintype.card_congr E

/-- Below binary the full ordinary box is exactly balanced in EVERY
coset of any subgroup containing the sufficiently dominant seed. -/
theorem dominant_index_mul_box_coset_card_eq_two_pow
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) (r : G) :
    Nat.card (G ⧸ H)*(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      (∑ i, (p i).val • x i)-r ∈ H)).card=2^n := by
  classical
  obtain ⟨m,hm,hbalance⟩ := balanced_companion_quotient_of_subbinary_dominant_chain
    L hL g hg E x b hchain hsub j hlarge H hx
  have hf := forest_coset_fibre_card_eq_axis_mul_companion L x j H hx r
  rw [hbalance] at hf
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype] at hf
  rw [hf,← mul_assoc,mul_comm (Nat.card (G ⧸ H)) (2^(L j)),mul_assoc,hm,← pow_add]
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hLj : L j ≤ n := by
    rw [← hsize]
    exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  rw [Nat.add_sub_of_le hLj]

/-- The entire binary deficit must be paid separately in EVERY dominant
quotient class, scaled by the actual quotient index. All arm lengths and
all arities are retained. -/
theorem dominant_coset_profile_mass_card_bound
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) (r : G) :
    2^n ≤ Fintype.card G+Nat.card (G ⧸ H)*
      ∑ w ∈ forestCollisionProfiles n L x,
        ((forestProfileLowerBox L w).filter (fun p : (∀ i, Fin (2^(L i))) ↦ (∑ i, (p i).val • x i)-r ∈ H)).card := by
  classical
  by_cases hsub : Fintype.card G < 2^n
  · let V := Finset.univ.filter (fun z : G ↦ z-r ∈ H)
    have hh := profile_fibre_card_bound_with_avoided_set L hL g hg E x b hchain V ∅
      (Finset.empty_subset _) (by simp)
    simp only [V,mem_filter,mem_univ,true_and,card_empty,add_zero] at hh
    have hmul := Nat.mul_le_mul_left (Nat.card (G ⧸ H)) hh
    rw [Nat.mul_add,dominant_index_mul_box_coset_card_eq_two_pow L hL g hg E x b hchain hsub j hlarge H hx r,
      forest_target_coset_card,← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup,
      Nat.card_eq_fintype_card] at hmul
    exact hmul
  · omega

/-- The quantitative bound descends through any surjective homomorphism
that kills the sufficiently dominant seed. -/
theorem dominant_projection_profile_mass_card_bound
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G Q : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup Q] [Finite Q]
    (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (π : G →+ Q) (hπ : Function.Surjective π) (hx : π (x j)=0) (z : Q) :
    2^n ≤ Fintype.card G+Nat.card Q*
      ∑ w ∈ forestCollisionProfiles n L x,
        ((forestProfileLowerBox L w).filter (fun p ↦ π (∑ i, (p i).val • x i)=z)).card := by
  classical
  obtain ⟨r,hr⟩ := hπ z
  have hh := dominant_coset_profile_mass_card_bound L hL g hg E x b hchain j hlarge π.ker hx r
  have hc : Nat.card (G ⧸ π.ker)=Nat.card Q :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π hπ).toEquiv
  simpa only [hc,AddMonoidHom.mem_ker,map_sub,hr,sub_eq_zero] using hh

/-- Actual profile lower-point mass in one residue class modulo d. -/
noncomputable def forestProfileResidueMass
    {N : ℕ} {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ)
    (x : β → ZMod N) (d : ℕ) (z : ZMod d) : ℕ := by
  classical
  exact ∑ w ∈ forestCollisionProfiles n L x,
    ((forestProfileLowerBox L w).filter (fun p ↦
      ((∑ i, (p i).val • x i).val : ZMod d)=z)).card

/-- The actual dominant gcd scales the deficit in EACH cyclic residue
class. No supplied dyadic-index or parity premise is required. -/
theorem dominant_gcd_profile_residue_mass_card_bound
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (z : ZMod (N.gcd (x j).val)) :
    2^n ≤ N+N.gcd (x j).val*forestProfileResidueMass n L x (N.gcd (x j).val) z := by
  classical
  let d := N.gcd (x j).val
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (NeZero.pos N))⟩
  have hdiv : d ∣ N := Nat.gcd_dvd_left _ _
  let π : ZMod N →+ ZMod d := (ZMod.castHom hdiv (ZMod d)).toAddMonoidHom
  have hπval : ∀ a : ZMod N, π a=(a.val : ZMod d) := by
    intro a
    change (a.cast : ZMod d)=(a.val : ZMod d)
    exact ZMod.cast_eq_val a
  have hx : π (x j)=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff]
    exact Nat.gcd_dvd_right _ _
  have hh := dominant_projection_profile_mass_card_bound L hL g hg E x b hchain j hlarge
    π (ZMod.castHom_surjective hdiv) hx z
  simpa only [Nat.card_zmod,ZMod.card,hπval,forestProfileResidueMass,d] using hh

/-- For modulus 2^t*q and dominant gcd 2^e, EVERY actual quotient
class contains at least 2^(t-e) profile points below binary. -/
theorem two_power_le_each_dominant_profile_residue_mass
    {n t q e : ℕ} (hq : 0 < q) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^t*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^t*q)) (b : ZMod (2^t*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^t*q < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hgcd : (2^t*q).gcd (x j).val=2^e) (he : e ≤ t)
    (z : ZMod ((2^t*q).gcd (x j).val)) :
    2^(t-e) ≤ forestProfileResidueMass n L x ((2^t*q).gcd (x j).val) z := by
  letI : NeZero (2^t*q) := ⟨by positivity⟩
  have hh := dominant_gcd_profile_residue_mass_card_bound L hL g hg E x b hchain j hlarge z
  have hgap := two_pow_le_gap_of_subbinary_multiple hq hsub
  have hpow : 2^e*2^(t-e)=2^t := by rw [← pow_add,Nat.add_sub_of_le he]
  have hm : 2^e*2^(t-e) ≤ 2^e*forestProfileResidueMass n L x ((2^t*q).gcd (x j).val) z := by
    conv at hh => rhs; arg 2; lhs; rw [hgcd]
    omega
  exact Nat.le_of_mul_le_mul_left hm (Nat.two_pow_pos e)

/-- In an actual subbinary forest over an exact dyadic stratum, the index
exponent and all residue-class lower masses are extracted together. -/
theorem exists_dominant_index_with_residue_mass
    {n t q : ℕ} (hq : Odd q) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^t*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^t*q)) (b : ZMod (2^t*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^t*q < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j)) :
    ∃ e ≤ min t (n-L j), (2^t*q).gcd (x j).val=2^e ∧
      ∀ z : ZMod ((2^t*q).gcd (x j).val),
        2^(t-e) ≤ forestProfileResidueMass n L x ((2^t*q).gcd (x j).val) z := by
  letI : NeZero (2^t*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨e,he,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  have hdiv : 2^e ∣ 2^t := (hq.coprime_two_right.pow_right e).symm.dvd_of_dvd_mul_right
    (by rw [← hgcd]; exact Nat.gcd_dvd_left _ _)
  have het : e ≤ t := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hdiv
  refine ⟨e,by omega,hgcd,?_⟩
  exact two_power_le_each_dominant_profile_residue_mass hq.pos L hL g hg E x b hchain hsub j hlarge hgcd het

end MinModulus
