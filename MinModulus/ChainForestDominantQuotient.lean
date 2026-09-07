import MinModulus.ChainForestTwoLongArms

/-! A sufficiently dominant chain forces exact balance in the quotient
by its seed subgroup. Its index divides the companion binary-box size,
hence is a power of two. This constrains the actual dominant multiplier;
the sharp global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Near-full interval packing forces exact equality of all fibre
loads. The large interval absorbs every possible one-unit rounding loss. -/
theorem balanced_loads_of_long_interval_capacity
    {Q : Type*} [Fintype Q] [Nonempty Q] (w : Q → ℕ)
    {n K B H : ℕ} (hsum : (∑ z, w z)=B)
    (hcap : ∀ z, (K-n)*w z ≤ H)
    (hsub : Fintype.card Q*H < K*B) (hlarge : n*(B+1) ≤ K) :
    ∃ m, (∀ z, w z=m) ∧ Fintype.card Q*m=B := by
  classical
  obtain ⟨z,_,hmax⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have hle : ∀ t, w t ≤ w z := fun t ↦ hmax t (Finset.mem_univ _)
  have hB : B ≤ Fintype.card Q*w z := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ ↦ hle t)
    simpa only [hsum,Finset.sum_const,Finset.card_univ,smul_eq_mul] using hh
  have hnK : n ≤ K := by nlinarith
  have hsubeq : K-n+n=K := Nat.sub_add_cancel hnK
  have heq : Fintype.card Q*w z=B := by
    by_contra hnot
    have hb : B+1 ≤ Fintype.card Q*w z := by omega
    have hc := Nat.mul_le_mul_left (Fintype.card Q) (hcap z)
    have hround := Nat.mul_le_mul_left (K-n) hb
    have hbase : K*B ≤ (K-n)*(B+1) := by nlinarith
    nlinarith
  refine ⟨w z,?_,heq⟩
  intro t
  by_contra hnot
  have ht : w t < w z := lt_of_le_of_ne (hle t) hnot
  have hh := Finset.sum_lt_sum (s := Finset.univ) (fun i _ ↦ hle i) ⟨t,Finset.mem_univ _,ht⟩
  simp only [hsum,Finset.sum_const,Finset.card_univ,smul_eq_mul,heq,lt_self_iff_false] at hh

/-- The high part of the dominant coordinate gives an injective
family of long interval translates indexed by every companion-box point. -/
theorem high_interval_translates_injective_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (j : β) :
    Function.Injective (fun p : Fin (2^(L j)-n) × (∀ i : {i : β // i ≠ j}, Fin (2^(L i.val))) ↦
      (n+p.1.val) • x j+∑ i, (p.2 i).val • x i.val) := by
  classical
  let C := {i : β // i ≠ j}
  let P := fun (p : Fin (2^(L j)-n) × (∀ i : C, Fin (2^(L i.val)))) i ↦
    if h : i=j then n+p.1.val else (p.2 ⟨i,h⟩).val
  have hp : ∀ p i, P p i < 2^(L i) := by
    intro p i
    dsimp only [P]
    split_ifs with hi
    · subst i; have := p.1.isLt; omega
    · exact (p.2 ⟨i,hi⟩).isLt
  have hs : ∀ p, n ≤ ∑ i, P p i := by
    intro p
    have hh := Finset.single_le_sum (f := P p) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have hPj : P p j=n+p.1.val := by simp [P]
    rw [hPj] at hh
    omega
  have heval : ∀ p, (∑ i, P p i • x i)=(n+p.1.val) • x j+∑ i : C, (p.2 i).val • x i.val := by
    intro p
    rw [← (Equiv.optionSubtypeNe j).sum_comp (fun i ↦ P p i • x i),Fintype.sum_option]
    simp only [Equiv.optionSubtypeNe_none,Equiv.optionSubtypeNe_some,P,dif_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_neg i.property]
  intro p q he
  change (n+p.1.val) • x j+(∑ i : C, (p.2 i).val • x i.val)=
    (n+q.1.val) • x j+∑ i : C, (q.2 i).val • x i.val at he
  have hh := high_box_injective_of_valid_chain_forest L hL g hg E x b hchain (P p) (P q)
    (hp p) (hp q) (hs p) (hs q) (by rw [heval,heval]; exact he)
  apply Prod.ext
  · apply Fin.ext
    have hj := congrFun hh j
    simp only [P,dif_pos rfl] at hj
    omega
  · funext i
    apply Fin.ext
    have hi := congrFun hh i.val
    simpa only [P,dif_neg i.property] using hi

/-- Quotient fibres of the companion box are exactly balanced
once the dominant binary width is at least n times one more than the
companion-box size. The quotient index therefore divides that size. -/
theorem balanced_companion_quotient_of_subbinary_dominant_chain
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) :
    ∃ m, Nat.card (G ⧸ H)*m=2^(n-L j) ∧
      ∀ z : G ⧸ H, Nat.card {p : (∀ i : {i : β // i ≠ j}, Fin (2^(L i.val))) //
        QuotientAddGroup.mk' H (∑ i, (p i).val • x i.val)=z}=m := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let C := {i : β // i ≠ j}
  let B := ∀ i : C, Fin (2^(L i.val))
  let π := QuotientAddGroup.mk' H
  let v : B → G := fun p ↦ ∑ i, (p i).val • x i.val
  let f : B → G ⧸ H := fun p ↦ π (v p)
  let w : (G ⧸ H) → ℕ := fun z ↦ Fintype.card {p : B // f p=z}
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hsplit : L j+(∑ i : C, L i.val)=n := by
    rw [← hsize,← (Equiv.optionSubtypeNe j).sum_comp L,Fintype.sum_option]
    rfl
  have hsumC : (∑ i : C, L i.val)=n-L j := by omega
  have hB : Fintype.card B=2^(n-L j) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsumC]
  have htotal : (∑ z, w z)=2^(n-L j) := by
    have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simpa only [Fintype.card_sigma,w,hB] using hh
  have hcard : Fintype.card G=Fintype.card (G ⧸ H)*Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hxzero : π (x j)=0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
  have hcap : ∀ z, (2^(L j)-n)*w z ≤ Fintype.card H := by
    intro z
    obtain ⟨r,hr⟩ := QuotientAddGroup.mk'_surjective H z
    let F : Fin (2^(L j)-n) × {p : B // f p=z} → H := fun p ↦
      ⟨(n+p.1.val) • x j+v p.2.val-r,by
        apply (QuotientAddGroup.eq_zero_iff _).mp
        change π ((n+p.1.val) • x j+v p.2.val-r)=0
        rw [map_sub,map_add,map_nsmul,hxzero,nsmul_zero,zero_add]
        change f p.2.val-π r=0
        rw [p.2.property,hr,sub_self]⟩
    have hi : Function.Injective F := by
      intro p q he
      have hh := congrArg Subtype.val he
      have he' : (n+p.1.val) • x j+v p.2.val=(n+q.1.val) • x j+v q.2.val := sub_left_inj.mp hh
      have hpq := high_interval_translates_injective_of_valid_chain_forest L hL g hg E x b hchain j
        (a₁ := (p.1,p.2.val)) (a₂ := (q.1,q.2.val)) he'
      apply Prod.ext
      · exact congrArg (fun z : Fin (2^(L j)-n) × B ↦ z.1) hpq
      · exact Subtype.ext (congrArg (fun z : Fin (2^(L j)-n) × B ↦ z.2) hpq)
    have hh := Fintype.card_le_of_injective F hi
    simpa only [Fintype.card_prod,Fintype.card_fin,w] using hh
  have hpow : 2^n=2^(L j)*2^(n-L j) := by
    rw [← pow_add,Nat.add_sub_of_le (by omega : L j ≤ n)]
  obtain ⟨m,hm,hprod⟩ := balanced_loads_of_long_interval_capacity w htotal hcap
    (by rw [← hcard,← hpow]; exact hsub) hlarge
  refine ⟨m,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hprod
  · intro z
    simpa only [Nat.card_eq_fintype_card,w,f,v,C,B,π] using hm z

/-- Every subgroup containing a sufficiently dominant seed has
power-of-two index, with exponent bounded by the number of companions. -/
theorem quotient_index_two_power_of_subbinary_dominant_chain
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (H : AddSubgroup G) (hx : x j ∈ H) :
    ∃ e ≤ n-L j, Nat.card (G ⧸ H)=2^e := by
  obtain ⟨m,hm,_⟩ := balanced_companion_quotient_of_subbinary_dominant_chain
    L hL g hg E x b hchain hsub j hlarge H hx
  exact (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp ⟨m,hm.symm⟩

/-- In a cyclic ambient group the actual dominant multiplier has
power-of-two gcd with the modulus. Odd factors of the multiplier cannot
survive the exact companion-fibre balance. -/
theorem gcd_two_power_of_subbinary_dominant_chain
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j)) :
    ∃ e ≤ n-L j, N.gcd (x j).val=2^e := by
  obtain ⟨e,he,hindex⟩ := quotient_index_two_power_of_subbinary_dominant_chain
    L hL g hg E x b hchain (by simpa only [ZMod.card] using hsub) j hlarge
    (AddSubgroup.zmultiples (x j)) (AddSubgroup.mem_zmultiples (x j))
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples (x j))
  simp only [Nat.card_zmod,Nat.card_zmultiples,hindex] at hcard
  have ho : addOrderOf (x j)=N/(N.gcd (x j).val) := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
  have hmul : N.gcd (x j).val*addOrderOf (x j)=N := by
    rw [ho,Nat.mul_div_cancel' (Nat.gcd_dvd_left N (x j).val)]
  have hpos : 0 < addOrderOf (x j) := addOrderOf_pos _
  exact ⟨e,he,by nlinarith⟩

/-- An odd dominant seed is therefore a unit in the original
modulus. This conclusion is derived, not supplied as a normalization
hypothesis. -/
theorem isUnit_of_odd_subbinary_dominant_seed
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : Odd (x j).val) : IsUnit (x j) := by
  obtain ⟨e,_,he⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  have hgcd : N.gcd (x j).val=1 := Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_right.pow_right e) (Nat.gcd_dvd_right N (x j).val) (by rw [he])
  have hcop : (x j).val.Coprime N := (show N.Coprime (x j).val from hgcd).symm
  simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime (x j).val N).mpr hcop


/-- The dominant seed generates the entire odd-order component:
it is coprime to the odd part and its additive order is divisible by
that odd part, even when its two-primary multiplier is a nonunit. -/
theorem odd_part_of_subbinary_dominant_seed
    {n s q : ℕ} (hq : Odd q) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^s*q)) (b : ZMod (2^s*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^s*q < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j)) :
    q.Coprime (x j).val ∧ q ∣ addOrderOf (x j) := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨e,_,he⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  have hd : q.gcd (x j).val ∣ (2^s*q).gcd (x j).val := Nat.dvd_gcd
    ((Nat.gcd_dvd_left q (x j).val).trans (dvd_mul_left q (2^s))) (Nat.gcd_dvd_right q (x j).val)
  have hone : q.gcd (x j).val=1 := Nat.eq_one_of_dvd_coprimes
    (hq.coprime_two_right.pow_right e) (Nat.gcd_dvd_left q (x j).val) (by simpa only [he] using hd)
  refine ⟨hone,?_⟩
  have ho : addOrderOf (x j)=(2^s*q)/((2^s*q).gcd (x j).val) := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.addOrderOf_coe (x j).val (NeZero.ne (2^s*q))
  have hmul : 2^e*addOrderOf (x j)=2^s*q := by
    rw [← he,ho,Nat.mul_div_cancel' (Nat.gcd_dvd_left (2^s*q) (x j).val)]
  exact (hq.coprime_two_right.pow_right e).dvd_of_dvd_mul_left (by rw [hmul]; exact dvd_mul_left q (2^s))

/-- At length at least 67 the surviving dominant chain automatically
meets the exact-balance threshold. Its companions are logarithmic and
its seed subgroup has power-of-two index. -/
theorem exists_dominant_two_primary_seed_of_subbinary_genuine_three_chains
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hsub : Fintype.card G < 2^n) :
    ∃ j, (∀ i, i ≠ j → 2^(L i) ≤ 2*n) ∧ n-2*Nat.log 2 (2*n) ≤ L j ∧
      n*(2^(n-L j)+1) ≤ 2^(L j) ∧
      ∃ e ≤ n-L j, Nat.card (G ⧸ AddSubgroup.zmultiples (x j))=2^e := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hrest : ∀ i, i ≠ j → 2^(L i) ≤ 2*n := by
    intro i hij
    by_contra hnot
    have hjpow := Nat.pow_le_pow_right (by decide : 0 < 2) (hmax i (Finset.mem_univ _))
    have hh := binary_card_bound_of_genuine_three_chains_two_wide_arms hn hr L hL g hg E x b hchain
      hgenuine i j hij (by omega) (by omega)
    omega
  let C := {i : β // i ≠ j}
  have hCcard : Fintype.card C=2 := by
    have hh := Fintype.card_congr (Equiv.optionSubtypeNe j)
    simp only [Fintype.card_option,hr] at hh
    change Fintype.card C+1=3 at hh
    omega
  have hsplit : L j+(∑ i : C, L i.val)=n := by
    rw [← hsize,← (Equiv.optionSubtypeNe j).sum_comp L,Fintype.sum_option]
    rfl
  have hsumC : (∑ i : C, L i.val)=n-L j := by omega
  have hlogs : (∑ i : C, L i.val) ≤ 2*Nat.log 2 (2*n) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (i : C) _ ↦
      Nat.le_log_of_pow_le (by decide : 1 < 2) (hrest i.val i.property))
    simpa only [Finset.sum_const,Finset.card_univ,hCcard,smul_eq_mul] using hh
  have hB : 2^(n-L j) ≤ (2*n)^2 := by
    have hh := Finset.prod_le_pow_card Finset.univ (fun i : C ↦ 2^(L i.val)) (2*n)
      (fun i _ ↦ hrest i.val i.property)
    simpa only [Finset.prod_pow_eq_pow_sum,hsumC,Finset.card_univ,hCcard] using hh
  have hnL : n ≤ 3*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 23 ≤ L j := by omega
  have hcube : n^3 ≤ 2^(L j-4) :=
    (Nat.pow_le_pow_left hnL 3).trans (three_length_cube_le_exponential hLj)
  have hpow : 2^(L j)=16*2^(L j-4) := by
    rw [show L j=4+(L j-4) by omega,pow_add]
    norm_num
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    have hnb := Nat.mul_le_mul_left n hB
    have hn_cube : n ≤ n^3 := by
      have h1 : 1 ≤ n*n := by nlinarith
      have hh := Nat.mul_le_mul_left n h1
      nlinarith
    nlinarith
  refine ⟨j,hrest,by omega,hlarge,?_⟩
  exact quotient_index_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain
    hsub j hlarge (AddSubgroup.zmultiples (x j)) (AddSubgroup.mem_zmultiples (x j))

/-- Original large three-escape no-half data extract a dominant
multiplier whose gcd with the ORIGINAL modulus is a power of two.
An odd dominant seed is a full unit; the forest's parity and joint-span
information is retained alongside the logarithmic companion bound. -/
theorem exists_dominant_dyadic_multiplier_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
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
      ∃ j, (∀ a, a ≠ j → 2^(L a) ≤ 2*(n+1)) ∧
        n+1-2*Nat.log 2 (2*(n+1)) ≤ L j ∧
        (∃ e ≤ n+1-L j, (2^(s+1)*q).gcd (x j).val=2^e) ∧
        (Odd (x j).val → IsUnit (x j)) ∧
        q.Coprime (x j).val ∧ q ∣ addOrderOf (x j) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a t
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  obtain ⟨j,hrest,hlong,hlarge,_⟩ := exists_dominant_two_primary_seed_of_subbinary_genuine_three_chains
    (by omega) hr L hL g hg E x b hchain hgen (by simpa only [ZMod.card] using hsub)
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,j,hrest,hlong,?_,?_,?_⟩
  · exact gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  · exact isUnit_of_odd_subbinary_dominant_seed L hL g hg E x b hchain hsub j hlarge
  · exact odd_part_of_subbinary_dominant_seed hq L hL g hg E x b hchain hsub j hlarge

end MinModulus
