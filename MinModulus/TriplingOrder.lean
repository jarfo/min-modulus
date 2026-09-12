import MinModulus.TriplingValidity

/-!
# Exact order of valid tripling orbits

In an abelian group with injective doubling, a valid tuple permuted by
tripling consists of consecutive powers of three times an element of order
`∑ i : Fin n, 3^i.val`. The parity obstruction and balanced ternary rule out
smaller orders. At odd cyclic moduli this proves the min-modulus lower bound
for this structural class, without an induction hypothesis or a cutoff.
-/

namespace MinModulus
open Finset

/-- A short zero-sum multiset of the tuple cannot have the tuple's parity:
tripling splits would create a repeated full-length rival. -/
theorem card_le_zero_multiset_of_valid_tripling
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i)
    (s : Multiset (Fin n)) (hs : 0<s.card) (hz : (s.map x).sum=0)
    (hp : s.card%2=n%2) : n ≤ s.card := by
  classical
  by_contra hle
  have htotal : ∑ i, x i=0 :=
    sum_eq_zero_of_tripling_invariant hinj R x ht univ (by simp)
  have hpred : ∀ i ∈ (Set.univ : Set (Fin n)), ∃ j ∈ (Set.univ : Set (Fin n)), x i=3 • x j := by
    intro i _
    exact ⟨R.symm i,Set.mem_univ _,by simpa using ht (R.symm i)⟩
  obtain ⟨r,hr⟩ : ∃ r, n=s.card+2*r+2 := ⟨(n-s.card-2)/2,by omega⟩
  obtain ⟨t,hcard,hzero,_⟩ := exists_zero_multiset_of_tripling_closed
    x Set.univ hpred s hs (by simp) hz r
  have hd : t=0 ∨ ∃ i u, t=i ::ₘ u :=
    Multiset.induction_on t (Or.inl rfl) (fun i u _ ↦ Or.inr ⟨i,u,rfl⟩)
  rcases hd with he | ⟨i,u,rfl⟩
  · simp [he] at hcard; omega
  let j := R.symm i
  have hji : x i=3 • x j := by simpa [j] using ht j
  have hall := multiset_count_eq_one_of_validTuple x hx (j ::ₘ j ::ₘ j ::ₘ u)
    (by simp_all) (by
      rw [htotal]
      simpa [Multiset.map_cons, Multiset.sum_cons, hji, three_nsmul, add_assoc] using hzero)
  have hbad := hall j
  simp only [Multiset.count_cons_self] at hbad
  omega

/-- The ternary geometric sum is half of three to the length minus one. -/
theorem two_mul_sum_ternary_powers_add_one (n : ℕ) :
    2*(∑ i : Fin n,3^i.val)+1=3^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,pow_succ]
    omega

/-- Balanced ternary covers its entire symmetric interval. -/
theorem exists_balanced_ternary_coefficients (n : ℕ) (z : ℤ)
    (hz : |z|≤∑ i : Fin n,(3:ℤ)^i.val) :
    ∃ c : Fin n → ℤ, (∀ i, -1≤c i ∧ c i≤1) ∧
      (∑ i, c i*(3:ℤ)^i.val)=z := by
  induction n generalizing z with
  | zero =>
    have : z=0 := by simpa using hz
    subst z
    exact ⟨Fin.elim0,by simp,by simp⟩
  | succ n ih =>
    let M : ℤ := ∑ i : Fin n,(3:ℤ)^i.val
    have hM : 0≤M := by positivity
    have hpow : (3:ℤ)^n=2*M+1 := by
      have h := two_mul_sum_ternary_powers_add_one n
      dsimp only [M]
      exact_mod_cast h.symm
    have hbound : -(M+(3:ℤ)^n)≤z ∧ z≤M+(3:ℤ)^n := by
      rw [abs_le] at hz
      simpa [Fin.sum_univ_castSucc,M] using hz
    obtain ⟨d,hd,hr⟩ : ∃ d : ℤ, (-1≤d ∧ d≤1) ∧ |z-d*(3:ℤ)^n|≤M := by
      by_cases hlo : z < -M
      · refine ⟨-1,by omega,?_⟩
        rw [abs_le]; constructor <;> nlinarith
      by_cases hhi : M < z
      · refine ⟨1,by omega,?_⟩
        rw [abs_le]; constructor <;> nlinarith
      · refine ⟨0,by omega,?_⟩
        rw [abs_le]; constructor <;> nlinarith
    obtain ⟨c,hc,he⟩ := ih (z-d*(3:ℤ)^n) hr
    refine ⟨Fin.snoc c d,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa using hd
      · simpa using hc j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last,he]
      ring

/-- The parity obstruction in multiplicity-vector form. -/
theorem card_le_sum_of_valid_tripling
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i)
    (p : Fin n → ℕ) (hp : 0<∑ i,p i) (hz : (∑ i,p i • x i)=0)
    (hpar : (∑ i,p i)%2=n%2) : n ≤ ∑ i,p i := by
  classical
  let s : Multiset (Fin n) := ∑ i, Multiset.replicate (p i) i
  have hcard : s.card=∑ i,p i := by simp [s,Multiset.card_sum]
  have hsum : (s.map x).sum=∑ i,p i • x i := by
    exact (map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom x))
      (fun i ↦ Multiset.replicate (p i) i) univ).trans (by simp)
  have h := card_le_zero_multiset_of_valid_tripling hinj x hx R ht s
    (by omega) (hsum.trans hz) (by omega)
  omega

/-- A balanced integral relation with even, nonpositive coefficient sum
is impossible for a valid tuple of odd length permuted by tripling. -/
theorem balanced_relation_eq_zero_of_valid_tripling
    {n : ℕ} (hn : Odd n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i)
    (c : Fin n → ℤ) (hc : ∀ i, -1≤c i ∧ c i≤1)
    (heven : (∑ i,c i)%2=0) (hle : ∑ i,c i≤0)
    (hz : (∑ i,c i • x i)=0) : ∀ i,c i=0 := by
  classical
  let p : Fin n → ℕ := fun i ↦ (1+c i).toNat
  have hp (i) : (p i : ℤ)=1+c i := Int.toNat_of_nonneg (by have := hc i; omega)
  have hcard : (↑(∑ i,p i) : ℤ)=n+∑ i,c i := by
    push_cast
    simp_rw [hp]
    simp [Finset.sum_add_distrib]
  have hnmod : n%2=1 := Nat.odd_iff.mp hn
  have hpar : (∑ i,p i)%2=n%2 := by omega
  have hpos : 0<∑ i,p i := by omega
  have htotal : ∑ i,x i=0 :=
    sum_eq_zero_of_tripling_invariant hinj R x ht univ (by simp)
  have hpsum : (∑ i,p i • x i)=0 := by
    calc
      _ = ∑ i, (1+c i) • x i := by simp_rw [← hp, natCast_zsmul]
      _ = (∑ i,x i)+(∑ i,c i • x i) := by simp [add_zsmul,Finset.sum_add_distrib]
      _ = 0 := by rw [htotal,hz,zero_add]
  have hge := card_le_sum_of_valid_tripling hinj x hx R ht p hpos hpsum hpar
  have heq : ∑ i,p i=n := by omega
  have hall := hx p heq (hpsum.trans htotal.symm)
  intro i
  have := hp i
  rw [hall i] at this
  omega

/-- Every balanced relation with even coefficient sum is trivial in a valid
odd tuple permuted by tripling. Negating handles positive coefficient sums. -/
theorem balanced_even_relation_eq_zero_of_valid_tripling
    {n : ℕ} (hn : Odd n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i)
    (c : Fin n → ℤ) (hc : ∀ i, -1≤c i ∧ c i≤1)
    (heven : (∑ i,c i)%2=0) (hz : (∑ i,c i • x i)=0) : ∀ i,c i=0 := by
  by_cases hle : ∑ i,c i≤0
  · exact balanced_relation_eq_zero_of_valid_tripling hn hinj x hx R ht c hc heven hle hz
  have h := balanced_relation_eq_zero_of_valid_tripling hn hinj x hx R ht
    (fun i ↦ -c i) (fun i ↦ by have := hc i; omega)
    (by rw [Finset.sum_neg_distrib]; omega)
    (by rw [Finset.sum_neg_distrib]; omega)
    (by simp only [neg_smul,Finset.sum_neg_distrib,hz,neg_zero])
  intro i
  have := h i
  omega

/-- Every positive common annihilator of a valid tripling orbit exceeds
half the ternary geometric sum. -/
theorem sum_ternary_powers_lt_two_mul_of_valid_tripling
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i)
    (d : ℕ) (hd : 0<d) (hkill : ∀ i,d • x i=0) :
    (∑ i : Fin n,3^i.val)<2*d := by
  classical
  by_contra hsmall
  have hbound : |2*(d:ℤ)|≤∑ i : Fin n,(3:ℤ)^i.val := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show 2*d≤∑ i : Fin n,3^i.val by omega)
  obtain ⟨c,hc,he⟩ := exists_balanced_ternary_coefficients n (2*d) hbound
  have heven : (∑ i,c i)%2=0 := by
    have hmod : (∑ i,c i*(3:ℤ)^i.val) ≡ (∑ i,c i) [ZMOD 2] := by
      apply Int.ModEq.sum
      intro i _
      simpa using (Int.ModEq.refl (c i)).mul ((show (3:ℤ) ≡ 1 [ZMOD 2] by decide).pow i.val)
    change _%2=_%2 at hmod
    rw [he] at hmod
    omega
  obtain ⟨a,e,horbit⟩ := exists_tripling_orbit_equiv_of_valid hn hinj x hx R ht
  let b : Fin n → ℤ := fun i ↦ c (e.symm i)
  have hb : ∑ i,b i=∑ i,c i := Equiv.sum_comp e.symm c
  have hzero : (∑ i,b i • x i)=0 := by
    rw [← Equiv.sum_comp e (fun i ↦ b i • x i)]
    simp only [b,Equiv.symm_apply_apply,horbit]
    have hterm (i : Fin n) : c i • (3^i.val • x a)=(c i*(3:ℤ)^i.val) • x a := by
      rw [← natCast_zsmul,smul_smul]
      norm_cast
    simp_rw [hterm]
    rw [← Finset.sum_smul,he,mul_smul]
    simp only [natCast_zsmul,hkill,smul_zero]
  have hall := balanced_even_relation_eq_zero_of_valid_tripling
    (odd_length_of_valid_tripling_perm hn hinj x hx R ht) hinj x hx R ht b
    (fun i ↦ hc _) (by rw [hb]; exact heven) hzero
  have hc0 (i) : c i=0 := by simpa only [b,Equiv.symm_apply_apply] using hall (e i)
  simp only [hc0,zero_mul,Finset.sum_const_zero] at he
  omega

/-- A valid tripling tuple consists of consecutive powers of three times
an element of exactly the ternary geometric-sum order. -/
theorem exists_tripling_generator_of_valid
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, x (R i)=3 • x i) :
    ∃ a, ∃ e : Equiv.Perm (Fin n),
      (∀ i,x (e i)=3^i.val • x a) ∧
      addOrderOf (x a)=∑ i : Fin n,3^i.val := by
  classical
  obtain ⟨a,e,he⟩ := exists_tripling_orbit_equiv_of_valid hn hinj x hx R ht
  let M := ∑ i : Fin n,3^i.val
  have hMpos : 0<M := Finset.sum_pos (fun i _ ↦ by positivity) ⟨a,mem_univ a⟩
  have hMkill : M • x a=0 := by
    dsimp only [M]
    rw [Finset.sum_smul]
    simp_rw [← he]
    exact (Equiv.sum_comp e x).trans
      (sum_eq_zero_of_tripling_invariant hinj R x ht univ (by simp))
  have hdpos : 0<addOrderOf (x a) := addOrderOf_pos_iff.mpr
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M,hMpos,hMkill⟩)
  have hkill (i) : addOrderOf (x a) • x i=0 := by
    obtain ⟨j,rfl⟩ := e.surjective i
    rw [he,smul_comm,addOrderOf_nsmul_eq_zero,smul_zero]
  have hbound := sum_ternary_powers_lt_two_mul_of_valid_tripling hn hinj x hx R ht
    (addOrderOf (x a)) hdpos hkill
  have horder := Nat.eq_of_dvd_of_lt_two_mul hMpos.ne'
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hMkill) hbound
  exact ⟨a,e,he,horder.symm⟩

/-- Odd cyclic moduli containing a valid tripling orbit are at least its
ternary geometric-sum order. -/
theorem sum_ternary_powers_le_modulus_of_valid_tripling
    {n N : ℕ} [NeZero N] (hn : 2≤n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i,g (R i)=3 • g i) :
    (∑ i : Fin n,3^i.val) ≤ N := by
  obtain ⟨a,_,_,horder⟩ := exists_tripling_generator_of_valid hn
    (add_self_injective_zmod hN) g hg R ht
  rw [← horder]
  have hdvd : addOrderOf (g a) ∣ N := by simpa only [ZMod.card] using
    (addOrderOf_dvd_card (x := g a))
  exact Nat.le_of_dvd (NeZero.pos N) hdvd

/-- The ternary geometric sum dominates the odd-stratum binary bound. -/
theorem two_pow_sub_one_le_sum_ternary_powers (n : ℕ) :
    2^n-1 ≤ ∑ i : Fin n,3^i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : 2^n≤3^n := Nat.pow_le_pow_left (by omega) n
    have hpos : 0<2^n := by positivity
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,pow_succ]
    omega

/-- G2 holds for every valid tuple permuted by tripling at an odd modulus. -/
theorem odd_stratum_lower_bound_of_valid_tripling
    {n N : ℕ} [NeZero N] (hn : 2≤n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i,g (R i)=3 • g i) :
    2^n-1 ≤ N :=
  (two_pow_sub_one_le_sum_ternary_powers n).trans
    (sum_ternary_powers_le_modulus_of_valid_tripling hn hN g hg R ht)

end MinModulus
