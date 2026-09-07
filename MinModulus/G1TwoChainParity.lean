import MinModulus.TwoEscapeGeometry

/-! The actual two-chain G1 residual has two ODD affine seeds. Any
even seed already supplies a same-parity half deletion. The dyadic
corner relation therefore carries matched parity/divisibility data,
not the unrestricted seed arithmetic of a general two-chain tuple. -/

namespace MinModulus
open Finset

/-- Every noninitial coordinate in a doubling chain has zero image in
the parity quotient, with no cyclic-unit normalization. -/
theorem parity_two_pow_smul_eq_zero_of_pos
    {G : Type*} [AddCommGroup G] (π : G →+ ZMod 2) (x : G)
    {t : ℕ} (ht : 0 < t) : π (2^t • x)=0 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  rw [map_nsmul,pow_succ']
  have htwo : ∀ z : ZMod 2, (2 : ℕ) • z=0 := by decide
  simp only [mul_nsmul,htwo,smul_zero]

/-- Away from the two actual seeds, every two-chain coordinate is even
after the given affine translation. -/
theorem two_chain_parity_eq_zero_away_seeds
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    {G : Type*} [AddCommGroup G] (π : G →+ ZMod 2)
    (g : Fin (A+L) → G) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (i : Fin (A+L)) (hia : i ≠ Fin.castAdd L ⟨0,hA⟩)
    (hil : i ≠ Fin.natAdd A ⟨0,hL⟩) : π (g i)=0 := by
  refine Fin.addCases (fun i hia _ ↦ ?_) (fun i _ hil ↦ ?_) i hia hil
  · have ht : 0 < i.val := by
      by_contra h
      apply hia
      exact congrArg (Fin.castAdd L) (Fin.ext (by change i.val=0; omega))
    rw [hleft]
    exact parity_two_pow_smul_eq_zero_of_pos π x ht
  · have ht : 0 < i.val := by
      by_contra h
      apply hil
      exact congrArg (Fin.natAdd A) (Fin.ext (by change i.val=0; omega))
    rw [hright]
    exact parity_two_pow_smul_eq_zero_of_pos π y ht

/-- If either actual affine seed is even, deleting the other seed
leaves a same-parity subtuple and constructs the requested half child.
This requires neither criticality nor a conjectural child bound. -/
theorem admitsValidTuple_half_of_two_chains_even_seed
    {n A L M : ℕ} [NeZero M] (hA : 0 < A) (hL : 0 < L)
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (E : Fin (A+L) ≃ Fin (n+1)) (b x y : ZMod (2*M))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hseed : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) x=0 ∨
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) y=0) : AdmitsValidTuple n M := by
  let π := (ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)).toAddMonoidHom
  let v : Fin (n+1) → ZMod (2*M) := fun i ↦ g i+b
  have hv : ValidTuple v := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let a : Fin (A+L) := Fin.castAdd L ⟨0,hA⟩
  let z : Fin (A+L) := Fin.natAdd A ⟨0,hL⟩
  have hav : v (E a)=x := by simpa [v,a] using hleft ⟨0,hA⟩
  have hzv : v (E z)=y := by simpa [v,z] using hright ⟨0,hL⟩
  have hp (i : Fin (A+L)) (hia : i ≠ a) (hiz : i ≠ z) : π (v (E i))=0 :=
    two_chain_parity_eq_zero_away_seeds hA hL π (fun i ↦ v (E i)) x y hleft hright i hia hiz
  rcases hseed with hx | hy
  · apply admitsValidTuple_half_of_all_but_one_same_parity v hv (E z) 0
    intro i hiz
    have he : E.symm i ≠ z := fun h ↦ hiz (by simpa using congrArg E h)
    by_cases hia : E.symm i=a
    · have hi : i=E a := by simpa using congrArg E hia
      change π (v i)=0
      rw [hi,hav]
      exact hx
    · have hh := hp (E.symm i) hia he
      change π (v i)=0
      simpa only [E.apply_symm_apply] using hh
  · apply admitsValidTuple_half_of_all_but_one_same_parity v hv (E a) 0
    intro i hia
    have he : E.symm i ≠ a := fun h ↦ hia (by simpa using congrArg E h)
    by_cases hiz : E.symm i=z
    · have hi : i=E z := by simpa using congrArg E hiz
      change π (v i)=0
      rw [hi,hzv]
      exact hy
    · have hh := hp (E.symm i) he hiz
      change π (v i)=0
      simpa only [E.apply_symm_apply] using hh

/-- Failure of actual half descent forces BOTH affine seeds to be odd.
Oddness is a necessary G1 condition, not an assumed unit condition. -/
theorem both_seeds_odd_of_two_chains_without_half
    {n A L N M : ℕ} [NeZero M] (hN : N=2*M) (hd : 2 ∣ N) (hA : 0 < A) (hL : 0 < L)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (E : Fin (A+L) ≃ Fin (n+1)) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hnohalf : ¬ AdmitsValidTuple n M) :
    ZMod.castHom hd (ZMod 2) x=1 ∧ ZMod.castHom hd (ZMod 2) y=1 := by
  subst N
  have hnot : ¬ (ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) x=0 ∨
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) y=0) := fun h ↦ hnohalf
    (admitsValidTuple_half_of_two_chains_even_seed hA hL g hg E b x y hleft hright h)
  have hcases : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
  exact ⟨(hcases _).resolve_left (fun h ↦ hnot (Or.inl h)),
    (hcases _).resolve_left (fun h ↦ hnot (Or.inr h))⟩

/-- The actual parity quotient identifies odd canonical representatives. -/
theorem odd_val_of_parity_eq_one
    {N : ℕ} [NeZero N] (hd : 2 ∣ N) (x : ZMod N)
    (hx : ZMod.castHom hd (ZMod 2) x=1) : Odd x.val := by
  change x.cast=1 at hx
  have hc : (x.val : ZMod 2)=1 := (ZMod.natCast_val x).trans hx
  have hh := congrArg ZMod.val hc
  rw [Nat.odd_iff]
  simpa only [ZMod.val_natCast,show (1 : ZMod 2).val=1 from rfl] using hh

/-- An actual corner zero relation survives in every common divisor of
the modulus and the two binary side lengths. No unit assumption is used. -/
theorem corner_relation_divisible_by_common_divisor
    {N D K H a b : ℕ} [NeZero N]
    (hDN : D ∣ N) (hDK : D ∣ K) (hDH : D ∣ H)
    (ha : a ≤ K) (hb : b ≤ H) (x y : ZMod N)
    (hzero : (K-a) • x+(H-b) • y=0) : D ∣ a*x.val+b*y.val := by
  have he : a • x+b • y=K • x+H • y := by
    calc
      a • x+b • y=0+(a • x+b • y) := by simp
      _=((K-a) • x+(H-b) • y)+(a • x+b • y) := by rw [hzero]
      _=((K-a)+a) • x+((H-b)+b) • y := by simp only [add_nsmul]; abel
      _=K • x+H • y := by rw [Nat.sub_add_cancel ha,Nat.sub_add_cancel hb]
  let π := ZMod.castHom hDN (ZMod D)
  have hh := congrArg π he
  simp only [nsmul_eq_mul,map_add,map_mul,map_natCast] at hh
  have hK : (K : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDK
  have hH : (H : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDH
  rw [hK,hH,zero_mul,zero_mul,add_zero] at hh
  have hx : π x=(x.val : ZMod D) := by rw [ZMod.castHom_apply,← ZMod.natCast_val]
  have hy : π y=(y.val : ZMod D) := by rw [ZMod.castHom_apply,← ZMod.natCast_val]
  rw [hx,hy] at hh
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_add,Nat.cast_mul] using hh

/-- If odd coefficients cancel a dyadic term modulo the next dyadic
power, the other term has exactly the SAME two-adic valuation. -/
theorem exists_odd_quotient_of_dyadic_odd_congruence
    {t b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (hdiv : 2^(t+1) ∣ 2^t*x+b*y) : ∃ v : ℕ, Odd v ∧ b=2^t*v := by
  have ht : 2^t ∣ 2^t*x+b*y :=
    (show 2^t ∣ 2^(t+1) by rw [pow_succ]; exact dvd_mul_right _ _).trans hdiv
  have hbmul : 2^t ∣ b*y := (Nat.dvd_add_iff_right (dvd_mul_right (2^t) x)).mpr ht
  have hb : 2^t ∣ b := (hy.coprime_two_left.pow_left t).dvd_of_dvd_mul_right hbmul
  obtain ⟨v,rfl⟩ := hb
  have htwo : 2 ∣ x+v*y := by
    apply (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2^t)).mp
    simpa only [pow_succ,mul_add,mul_assoc] using hdiv
  have hxmod := Nat.odd_iff.mp hx
  have hymod := Nat.odd_iff.mp hy
  have hmod := Nat.mod_eq_zero_of_dvd htwo
  rw [Nat.add_mod,Nat.mul_mod,hxmod,hymod,mul_one] at hmod
  refine ⟨v,Nat.odd_iff.mpr ?_,rfl⟩
  omega

/-- The dyadic side of an odd-seed corner forces a matching dyadic
factor in the other side, throughout the uncapped valuation range. -/
theorem exists_odd_quotient_of_dyadic_two_chain_corner
    {N A L t b : ℕ} [NeZero N] (htA : t < A) (htL : t < L)
    (hdiv : 2^(t+1) ∣ N) (hb : b ≤ 2^L) (x y : ZMod N)
    (hx : Odd x.val) (hy : Odd y.val)
    (hzero : (2^A-2^t) • x+(2^L-b) • y=0) :
    ∃ v : ℕ, Odd v ∧ b=2^t*v := by
  apply exists_odd_quotient_of_dyadic_odd_congruence hx hy
  exact corner_relation_divisible_by_common_divisor hdiv
    (pow_dvd_pow 2 (by omega : t+1 ≤ A)) (pow_dvd_pow 2 (by omega : t+1 ≤ L))
    (Nat.pow_le_pow_right (by omega) (by omega)) hb x y hzero

/-- Odd affine seeds force the two corner sides to have the same parity. -/
theorem even_corner_sum_of_odd_two_chain_seeds
    {N A L a b : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hN : 2 ∣ N)
    (ha : a ≤ 2^A) (hb : b ≤ 2^L) (x y : ZMod N)
    (hx : Odd x.val) (hy : Odd y.val)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) : Even (a+b) := by
  have hD : 2 ∣ a*x.val+b*y.val := corner_relation_divisible_by_common_divisor hN
    (dvd_pow_self 2 (by omega : A ≠ 0)) (dvd_pow_self 2 (by omega : L ≠ 0)) ha hb x y hzero
  have hh := Nat.mod_eq_zero_of_dvd hD
  have hmx : a*x.val % 2=a % 2 := by rw [Nat.mul_mod,Nat.odd_iff.mp hx,mul_one,Nat.mod_mod]
  have hmy : b*y.val % 2=b % 2 := by rw [Nat.mul_mod,Nat.odd_iff.mp hy,mul_one,Nat.mod_mod]
  rw [Nat.add_mod,hmx,hmy] at hh
  rw [Nat.even_iff,Nat.add_mod]
  exact hh

/-- The original critical two-escape G1 residual now supplies two ODD
affine seeds and a same-parity dyadic-sided deficit corner. This retains
the full original chains; oddness and corner parity are extracted. -/
theorem exists_odd_seed_corner_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n+1 ∧ ∃ E : Fin (A+L) ≃ Fin (n+1),
      ∃ x y : ZMod (2^(s+1)*q), Odd x.val ∧ Odd y.val ∧
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      ∃ d u : ℕ, 0 < d ∧ d ≤ 2^A ∧ 0 < u ∧ u ≤ 2^L ∧
        d+u ≤ n+2 ∧ Even (d+u) ∧ 2^(n+1) ≤ 2^(s+1)*q+d*u ∧
        ((∃ e, d=2^e) ∨ ∃ f, u=2^f) ∧
        (2^A-d) • x+(2^L-u) • y=0 := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hd : 2 ∣ 2^(s+1)*q := by rw [hN]; exact dvd_mul_right 2 _
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,hpay,hpow,hzero⟩ :=
    exists_deficit_corner_of_critical_two_escape_without_half hq hn g hg hcritical B hB b hclosed hnohalf
  obtain ⟨hx,hy⟩ := both_seeds_odd_of_two_chains_without_half hN hd hA hL
    g hg E b x y hleft hright hnohalf
  have hxo := odd_val_of_parity_eq_one hd x hx
  have hyo := odd_val_of_parity_eq_one hd y hy
  exact ⟨A,L,hA,hL,hsize,E,x,y,hxo,hyo,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,
    even_corner_sum_of_odd_two_chain_seeds hA hL hd hdA huL x y hxo hyo hzero,hpay,hpow,hzero⟩

end MinModulus
