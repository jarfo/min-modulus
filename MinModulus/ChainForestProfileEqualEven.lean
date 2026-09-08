import MinModulus.ChainForestProfileFiveFive

/-! A uniform rival construction for even equal-companion primitive
phases below the maximal index. The companion lengths are unrestricted;
no finite certificate table or fixed binary prefix width is used. -/

namespace MinModulus

/-- The two off-center equal-companion weights have an exact combined
coin cost, uniformly in their common length. -/
theorem equal_even_phase_companion_coin_cost (k : ℕ) :
    gmin (k+1) (3*2^k-1)=k+1 ∧ gmin (k+1) (5*2^k-1)=k+2 := by
  induction k with
  | zero => norm_num [gmin]
  | succ k ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_two_pow
    have hp' : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
    have h3mod : (3*2^(k+1)-1)%2=1 := by omega
    have h3div : (3*2^(k+1)-1)/2=3*2^k-1 := by omega
    have h5mod : (5*2^(k+1)-1)%2=1 := by omega
    have h5div : (5*2^(k+1)-1)/2=5*2^k-1 := by omega
    constructor
    · rw [gmin,h3mod,h3div,ih.1]
      omega
    · rw [gmin,h5mod,h5div,ih.2]
      omega

/-- Even primitive phases strengthen the equal-width divisibility link
to twice the primitive denominator. -/
theorem twice_equal_denominator_dvd_of_even_phase
    {u T r q : ℕ} (_hu : 1 ≤ u) (hT : T+1=4*u)
    (hr : 2 ∣ r) (hlink : T ∣ 2*r+q) : 2*T ∣ 2*u*q+r := by
  obtain ⟨v,hv⟩ := hr
  obtain ⟨l,hl⟩ := hlink
  have hh : q+l+4*v=4*(u*l) := by nlinarith only [hv,hl,hT]
  have hd : 4 ∣ q+l := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨m,hm⟩ := hd
  refine ⟨m,?_⟩
  have hmul := congrArg (fun t : ℕ ↦ T*t) hm
  have hmul' := congrArg (fun t : ℕ ↦ t*q) hT
  nlinarith only [hmul,hmul',hl]

/-- The signed primitive basis has a uniform exact axis coefficient for
an even equal phase. Both the drop and the period deficit cancel. -/
theorem equal_even_primitive_rival_twice
    {u G T K H c V α z r q m M : ℕ} (_hu : 1 ≤ u) (hT : T+1=4*u)
    (hbase : H+c=V+1) (hlink : 2*T*m=2*u*q+r)
    (hap : (2*G*T : ℕ)*(α : ℤ)=(2*(u : ℤ)-1)*((K : ℤ)-H)+2*(u : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M) :
    2*((5*(u : ℤ)-1)*z+(G : ℤ)*α+(2-5*(u : ℤ))*V-((q : ℤ)+m)*M)=3*(K : ℤ)-H-2 := by
  have hTZ : (T : ℤ)+1=4*u := by exact_mod_cast hT
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hlZ : 2*(T : ℤ)*m=2*(u : ℤ)*q+r := by exact_mod_cast hlink
  have hh : (T : ℤ)*(2*((5*(u : ℤ)-1)*z+(G : ℤ)*α+(2-5*(u : ℤ))*V-((q : ℤ)+m)*M))=
      (T : ℤ)*(3*(K : ℤ)-H-2) := by
    push_cast at hap
    linear_combination hap+2*(5*(u : ℤ)-1)*hzp+2*(T : ℤ)*(5*(u : ℤ)-2)*hbZ-
      hlZ*(M : ℤ)+hTZ*(-3*(K : ℤ)+3*H+2*c-2*(q : ℤ)*M)
  have hTpos : (0 : ℤ) < T := by exact_mod_cast (show 0 < T by omega)
  exact (mul_left_cancel₀ (ne_of_gt hTpos)) hh

/-- Every even primitive phase below the maximal equal-companion index
has one explicit affordable rival, at arbitrary companion lengths. The
ordinary axis-width bound is sufficient; no table or fixed length cutoff
is used. -/
theorem exists_equal_even_primitive_rival
    {k D G T n N L M H c V α z r q : ℕ}
    (hDG : D*G=2*2^k) (hT : T+1=4*2^k)
    (hL : L+2*(k+2)=n) (hwidth : 2*n ≤ 2^L)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hr : 2 ∣ r) (hlink : T ∣ 2*r+q)
    (hap : (2*G*T : ℕ)*(α : ℤ)=(2*(2^k : ℕ)-1)*((2 : ℤ)^L-H)+2*(2^k : ℕ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x a b : ZMod N) (hα : α • x=D • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0) :
    ∃ s, n ≤ s ∧ 3*2^k-1 ≠ 2^(k+2)-1 ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin (k+1) (3*2^k-1)+gmin (k+1) (5*2^k-1) ≤ n ∧
      s • x+(3*2^k-1) • a+(5*2^k-1) • b=V • x := by
  have hu : 1 ≤ 2^k := Nat.one_le_two_pow
  have hn : 2 ≤ n := by omega
  have hLp : 1 ≤ L := by
    by_contra hh
    have hzero : L=0 := by omega
    simp only [hzero,pow_zero] at hwidth
    omega
  have hpow : 2^L=2*2^(L-1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨m,hm⟩ := twice_equal_denominator_dvd_of_even_phase hu hT hr hlink
  have hm' : 2*T*m=2*2^k*q+r := hm.symm
  let Z : ℤ := ((5*2^k-1 : ℕ) : ℤ)*z+(G : ℤ)*α+
    (1-((5*2^k-1 : ℕ) : ℤ))*V-((q+m : ℕ) : ℤ)*M
  have htb : 1 ≤ 5*2^k := by omega
  have hta : 1 ≤ 3*2^k := by omega
  have h2Z : 2*Z=3*(2 : ℤ)^L-H-2 := by
    have hh := equal_even_primitive_rival_twice (K:=2^L) (u:=2^k) hu hT hbase hm'
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp)
    dsimp [Z]
    simp only [Nat.cast_sub htb,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    push_cast at hh
    convert hh using 1
    ring
  have hKH : H+2 ≤ 2^L := by omega
  have hlow : (2 : ℤ)^L ≤ Z := by
    have hh : (H : ℤ)+2 ≤ (2 : ℤ)^L := by exact_mod_cast hKH
    linarith only [h2Z,hh]
  have hhigh : Z < 3*(2 : ℤ)^(L-1) := by
    have hp : (2 : ℤ)^L=2*(2 : ℤ)^(L-1) := by exact_mod_cast hpow
    have hHZ : (1 : ℤ) ≤ H := by exact_mod_cast hH
    linarith only [h2Z,hp,hHZ]
  have hZ : 0 ≤ Z := le_trans (by positivity) hlow
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hlo : 2^L ≤ Z.toNat := by
    exact_mod_cast (show (2 : ℤ)^L ≤ (Z.toNat : ℤ) by rw [hcast]; exact hlow)
  have hhi : Z.toNat < 3*2^(L-1) := by
    exact_mod_cast (show (Z.toNat : ℤ) < 3*(2 : ℤ)^(L-1) by rw [hcast]; exact hhigh)
  have hrem : Z.toNat-2^L < 2^(L-1) := by omega
  obtain ⟨u,huval,hucost⟩ := exists_rep_binary_block_tail 0 (L-1) 2 (Z.toNat-2^L) hrem
  have he : L-1+(0+1)=L := by omega
  rw [he,← hpow,Nat.add_sub_of_le hlo] at huval
  rw [he] at hucost
  norm_num [gmin] at hucost
  have hcoins := equal_even_phase_companion_coin_cost k
  have hne : 3*2^k-1 ≠ 2^(k+2)-1 := by
    have hp : 2^(k+2)=4*2^k := by rw [pow_add]; ring
    omega
  have hDGZ : (D : ℤ)*G=2*(2^k : ℕ) := by exact_mod_cast hDG
  have htaeq : ((3*2^k-1 : ℕ) : ℤ)=(5*2^k-1 : ℕ)+(D : ℤ)*(-(G : ℤ)) := by
    simp only [Nat.cast_sub hta,Nat.cast_sub htb,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    push_cast at hDGZ
    nlinarith only [hDGZ]
  refine ⟨Z.toNat,by omega,hne,u,huval,by omega,?_⟩
  have hpos : (0 : ℤ) ≤ ((5*2^k-1 : ℕ) : ℤ)*z-(-(G : ℤ))*α+
      (1-((5*2^k-1 : ℕ) : ℤ))*V-((q+m : ℕ) : ℤ)*M := by
    simpa only [sub_neg_eq_add,neg_mul] using hZ
  have hh := signed_axis_basis_rival_eq x a b (-(G : ℤ)) ((q+m : ℕ) : ℤ) htaeq hz hα hmx hpos
  simpa only [sub_neg_eq_add,neg_mul,Z] using hh

/-- A valid equal-companion forest cannot have an even primitive phase
below the maximal index. The complete full-length rival forces every
compatible phase to be odd, uniformly in the companion length. -/
theorem odd_primitive_phase_of_valid_equal_companion_forest
    {k D G T n N M H c V α z r q : ℕ}
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hLa : L a=k+2) (hLt : L t=k+2)
    (hDG : D*G=2*2^k) (hT : T+1=4*2^k) (hwidth : 2*n ≤ 2^(L j))
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hlink : T ∣ 2*r+q)
    (hap : (2*G*T : ℕ)*(α : ℤ)=(2*(2^k : ℕ)-1)*((2 : ℤ)^(L j)-H)+2*(2^k : ℕ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^(L j)+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (hα : α • x j=D • x a) (hz : z • x j+x a+x t=V • x j) (hmx : M • x j=0)
    (htarget : (∑ i, (2^(L i)-1) • x i)=V • x j) : Odd r := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,t} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hrank,Ne.symm haj,Ne.symm htj,Ne.symm hta]
  have hsize : L j+2*(k+2)=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simp [Ne.symm haj,Ne.symm htj,Ne.symm hta,hLa,hLt] at hs
    omega
  by_contra hodd
  have heven : 2 ∣ r := even_iff_two_dvd.mp ((Nat.even_or_odd r).resolve_right hodd)
  obtain ⟨s,hs,hne,u,hu,hcost,heval⟩ := exists_equal_even_primitive_rival hDG hT hsize hwidth
    hH hnc hbase heven hlink hap hzp (x j) (x a) (x t) hα hz hmx
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (k+1) (3*2^k-1)
  obtain ⟨ut,hut,hct⟩ := exists_rep_gmin (k+1) (5*2^k-1)
  apply not_validTuple_of_three_axis_representations hrank L g E x b hchain j a t haj htj hta
    s (3*2^k-1) (5*2^k-1) u ua ut hu (by simpa [hLa,add_assoc] using hua)
    (by simpa [hLt,add_assoc] using hut)
    (by simpa [hLa,hLt,hca,hct,add_assoc] using hcost) (by omega)
    (Or.inl (by simpa [hLa] using hne)) (heval.trans htarget.symm) hg

end MinModulus
