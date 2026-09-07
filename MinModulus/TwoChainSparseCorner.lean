import MinModulus.TwoChainAxis

/-! Joint binary weight savings force sparse corner sides. This is a
uniform restriction on actual interior relations, not a bounded census. -/

namespace MinModulus
open Finset

/-- A positive number below a binary range that is neither a power
nor a sum of two powers requires a range of at least three bits. -/
theorem three_le_width_of_not_two_binary_powers
    {w s : ℕ} (hs0 : 0 < s) (hs : s < 2^w)
    (hp : ¬ ∃ e, s=2^e) (hp2 : ¬ ∃ e f, s=2^e+2^f) : 3 ≤ w := by
  by_contra hnot
  have hh : 2^w ≤ 2^2 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hh
  have hc : s=1 ∨ s=2 ∨ s=3 := by omega
  rcases hc with rfl | rfl | rfl
  · exact hp ⟨0,rfl⟩
  · exact hp ⟨1,rfl⟩
  · exact hp2 ⟨1,0,rfl⟩

/-- A complement missing at least three binary digits saves three
coins, uniformly in width. No popcount implementation is assumed. -/
theorem exists_rep_compl_not_two_binary_powers : ∀ w s : ℕ,
    s < 2^w → 0 < s → (¬ ∃ e, s=2^e) → (¬ ∃ e f, s=2^e+2^f) →
    ∃ k, Supp w k ∧ val w k=2^w-1-s ∧ dsum w k ≤ w-3 := by
  intro w
  induction w with
  | zero => intro s hs; norm_num at hs; omega
  | succ w ih =>
    intro s hs hs0 hp hp2
    have h2 : 2^(w+1)=2*2^w := by rw [pow_succ']
    have hwp : 0 < 2^w := by positivity
    rcases Nat.even_or_odd s with ⟨q,hq⟩ | ⟨q,hq⟩
    · have hq0 : 0 < q := by omega
      have hqlt : q < 2^w := by omega
      have hqp : ¬ ∃ e, q=2^e := by
        rintro ⟨e,he⟩
        apply hp
        refine ⟨e+1,?_⟩
        rw [pow_succ]
        omega
      have hqp2 : ¬ ∃ e f, q=2^e+2^f := by
        rintro ⟨e,f,he⟩
        apply hp2
        refine ⟨e+1,f+1,?_⟩
        rw [pow_succ,pow_succ]
        omega
      have hw3 := three_le_width_of_not_two_binary_powers hq0 hqlt hqp hqp2
      obtain ⟨k,hks,hkv,hkd⟩ := ih q hqlt hq0 hqp hqp2
      refine ⟨shift 1 k,shift_supp hks,?_,?_⟩
      · rw [shift_val,hkv]
        omega
      · rw [shift_dsum]
        omega
    · have hq0 : 0 < q := by
        by_contra hnot
        have hs1 : s=1 := by omega
        exact hp ⟨0,by simpa only [pow_zero] using hs1⟩
      have hqlt : q < 2^w := by omega
      have hqp : ¬ ∃ e, q=2^e := by
        rintro ⟨e,he⟩
        apply hp2
        refine ⟨e+1,0,?_⟩
        rw [pow_succ,pow_zero]
        omega
      have hw2 : 2 ≤ w := by
        by_contra hnot
        have hh : 2^w ≤ 2^1 := Nat.pow_le_pow_right (by decide) (by omega)
        norm_num at hh
        exact hqp ⟨0,by rw [pow_zero]; omega⟩
      obtain ⟨k,hks,hkv,hkd⟩ := exists_rep_compl w q hqlt (by omega) hqp
      refine ⟨shift 0 k,shift_supp hks,?_,?_⟩
      · rw [shift_val,hkv]
        omega
      · rw [shift_dsum]
        omega

/-- Every interior corner side has at most two binary digits. If the
right side needed three, its complementary saving would pay for the
left side's one extra coin in a full-length far-side rival. -/
theorem right_corner_eq_power_or_two_powers_of_valid_two_chains
    {A L a b : ℕ} (hA : 0 < A) (hL : 0 < L)
    (ha : 0 < a) (haA : a < 2^A) (hb : 0 < b) (hbL : b < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) :
    (∃ e, b=2^e) ∨ ∃ e f, b=2^e+2^f := by
  by_contra hnot
  have hp : ¬ ∃ e, b=2^e := fun h ↦ hnot (Or.inl h)
  have hp2 : ¬ ∃ e f, b=2^e+2^f := fun h ↦ hnot (Or.inr h)
  have hL3 := three_le_width_of_not_two_binary_powers hb hbL hp hp2
  obtain ⟨p,hps,hpval,hpdsum⟩ := exists_rep_lt A (2^A-1-a) (by omega)
  obtain ⟨p',_,hp',hdp'⟩ := exists_binary_rep_add_two_top_coins hA p hps
  obtain ⟨q,hqs,hqval,hqdsum⟩ := exists_rep_compl_not_two_binary_powers L b hbL hb hp hp2
  obtain ⟨q',_,hq',hdq'⟩ := exists_binary_rep_add_two_top_coins hL q hqs
  have hAp : 0 < 2^A := by positivity
  have hLp : 0 < 2^L := by positivity
  have hpv : val A p'=(2^A-1)+(2^A-a) := by rw [hp',hpval]; omega
  have hqv : val L q'=(2^L-1)+(2^L-b) := by rw [hq',hqval]; omega
  have hsum : ((2^A-1)+(2^A-a)) • x+((2^L-1)+(2^L-b)) • y=
      (2^A-1) • x+(2^L-1) • y := by
    simp only [add_nsmul]
    calc
      _=((2^A-1) • x+(2^L-1) • y)+((2^A-a) • x+(2^L-b) • y) := by abel
      _=_ := by rw [hzero,add_zero]
  have hhigh : A+L ≤ ((2^A-1)+(2^A-a))+((2^L-1)+(2^L-b)) := by
    have h1 := Nat.lt_two_pow_self (n := A)
    have h2 := Nat.lt_two_pow_self (n := L)
    omega
  exact not_validTuple_of_two_chain_integer_weights g x y hleft hright p' q' hpv hqv
    (by omega) hhigh (by omega) hsum hg

/-- Both sides are sparse, and at least one is a single power. Thus
an actual interior corner has at most THREE binary digits in total. -/
theorem sparse_corner_sides_of_valid_two_chains
    {A L a b : ℕ} (hA : 0 < A) (hL : 0 < L)
    (ha : 0 < a) (haA : a < 2^A) (hb : 0 < b) (hbL : b < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) :
    ((∃ e, a=2^e) ∨ ∃ e f, a=2^e+2^f) ∧
      ((∃ e, b=2^e) ∨ ∃ e f, b=2^e+2^f) ∧
      ((∃ e, a=2^e) ∨ ∃ f, b=2^f) := by
  have hr := right_corner_eq_power_or_two_powers_of_valid_two_chains hA hL ha haA hb hbL
    g hg x y hleft hright hzero
  let v : Fin (L+A) → G := fun i ↦ g (finAddFlip i)
  have hv : ValidTuple v := validTuple_embedding finAddFlip.toEmbedding g hg
  have hl := right_corner_eq_power_or_two_powers_of_valid_two_chains hL hA hb hbL ha haA
    v hv y x (fun i ↦ by simpa only [v,finAddFlip_apply_castAdd] using hright i)
    (fun i ↦ by simpa only [v,finAddFlip_apply_natAdd] using hleft i) (by simpa only [add_comm] using hzero)
  have hp := power_deficit_of_zero_relation_of_valid_two_chains hA hL
    (by omega : 0 < 2^A-a) (by omega : 2^A-a < 2^A)
    (by omega : 0 < 2^L-b) (by omega : 2^L-b < 2^L) g hg x y hleft hright hzero
  refine ⟨hl,hr,?_⟩
  simpa only [Nat.sub_sub_self haA.le,Nat.sub_sub_self hbL.le] using hp

/-- Equality of two dyadic powers times odd factors identifies the
dyadic exponents, without factorization or a finite valuation census. -/
theorem dyadic_exponent_eq_of_odd_factor_eq
    {t e v w : ℕ} (hv : Odd v) (hw : Odd w)
    (he : 2^t*v=2^e*w) : t=e := by
  have aux : ∀ {t e v w : ℕ}, Odd v → 2^t*v=2^e*w → e ≤ t := by
    intro t e v w hv he
    by_contra hnot
    have hd : 2^(t+1) ∣ 2^e*w :=
      dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : t+1 ≤ e)) w
    rw [← he,pow_succ] at hd
    have hv2 : 2 ∣ v := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2^t)).mp hd
    have hz := Nat.mod_eq_zero_of_dvd hv2
    have ho := Nat.odd_iff.mp hv
    omega
  have h1 := aux hv he
  have h2 := aux hw he.symm
  omega

/-- A sparse number with a specified odd dyadic factor has only two
shapes: that dyadic power, or that power times one plus a higher power. -/
theorem odd_factor_eq_one_or_one_add_pow_of_sparse_dyadic
    {t v : ℕ} (hv : Odd v)
    (hs : (∃ e, 2^t*v=2^e) ∨ ∃ e f, 2^t*v=2^e+2^f) :
    v=1 ∨ ∃ r : ℕ, 0 < r ∧ v=1+2^r := by
  have hp (e : ℕ) (he : 2^t*v=2^e) : v=1 := by
    have ht := dyadic_exponent_eq_of_odd_factor_eq hv (by decide : Odd (1:ℕ))
      (by simpa only [mul_one] using he)
    rw [← ht] at he
    have hh : 0 < 2^t := by positivity
    nlinarith
  rcases hs with ⟨e,he⟩ | ⟨e,f,hef⟩
  · exact Or.inl (hp e he)
  · by_cases heq : e=f
    · left
      apply hp (e+1)
      rw [pow_succ]
      rw [← heq] at hef
      omega
    have ordered : ∀ {e f : ℕ}, e < f → 2^t*v=2^e+2^f →
        ∃ r : ℕ, 0 < r ∧ v=1+2^r := by
      intro e f hef he
      have hr : 0 < f-e := by omega
      have hodd : Odd (1+2^(f-e)) := by
        obtain ⟨r,hh⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f-e ≠ 0)
        rw [hh,pow_succ']
        exact ⟨2^r,by omega⟩
      have hpow : 2^f=2^e*2^(f-e) := by rw [← pow_add,Nat.add_sub_of_le hef.le]
      have he' : 2^t*v=2^e*(1+2^(f-e)) := by rw [hpow] at he; nlinarith
      have ht := dyadic_exponent_eq_of_odd_factor_eq hv hodd he'
      subst e
      refine ⟨f-t,hr,?_⟩
      have hh : 0 < 2^t := by positivity
      nlinarith
    right
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · exact ordered hlt hef
    · exact ordered hgt (by simpa only [Nat.add_comm] using hef)

/-- In the uncapped odd-seed range an actual sparse corner is either
square, or its other side is a*(1+2^r), r>0. No extra digit-shape input. -/
theorem square_or_dyadic_bump_of_valid_odd_seed_corner
    {N A L t b : ℕ} [NeZero N] (htA : t < A) (htL : t < L)
    (hdiv : 2^(t+1) ∣ N) (hb : 0 < b) (hbL : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hy : Odd y.val)
    (hzero : (2^A-2^t) • x+(2^L-b) • y=0) :
    b=2^t ∨ ∃ r : ℕ, 0 < r ∧ b=2^t*(1+2^r) := by
  obtain ⟨v,hv,hbval⟩ := exists_odd_quotient_of_dyadic_two_chain_corner
    htA htL hdiv hbL.le x y hx hy hzero
  have hp := right_corner_eq_power_or_two_powers_of_valid_two_chains (by omega) (by omega)
    (by positivity : 0 < 2^t) (Nat.pow_lt_pow_right (by decide) htA) hb hbL
    g hg x y hleft hright hzero
  rw [hbval] at hp
  rcases odd_factor_eq_one_or_one_add_pow_of_sparse_dyadic hv hp with he | ⟨r,hr,he⟩
  · exact Or.inl (by simpa only [he,mul_one] using hbval)
  · exact Or.inr ⟨r,hr,by simpa only [he] using hbval⟩

/-- The ORIGINAL critical two-escape G1 residual now has a strict
interior corner with at most three binary digits across both sides.
The tuple, chains, odd seeds, parity and full deficit payment are retained. -/
theorem exists_sparse_interior_corner_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 5 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n+1 ∧ ∃ E : Fin (A+L) ≃ Fin (n+1),
      ∃ x y : ZMod (2^(s+1)*q), Odd x.val ∧ Odd y.val ∧
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      ∃ d u : ℕ, 0 < d ∧ d < 2^A ∧ 0 < u ∧ u < 2^L ∧
        d+u ≤ n+2 ∧ Even (d+u) ∧ 2^(n+1) ≤ 2^(s+1)*q+d*u ∧
        ((∃ e, d=2^e) ∨ ∃ f, u=2^f) ∧
        ((∃ e, d=2^e) ∨ ∃ e f, d=2^e+2^f) ∧
        ((∃ e, u=2^e) ∨ ∃ e f, u=2^e+2^f) ∧
        (2^A-d) • x+(2^L-u) • y=0 := by
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,heven,hpay,hpow,hzero⟩ :=
    exists_interior_odd_seed_corner_of_critical_two_escape_without_half hq hn
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  obtain ⟨hdsp,husp,_⟩ := sparse_corner_sides_of_valid_two_chains hA hL hd0 hdA hu0 huL
    _ hv x y hleft hright hzero
  exact ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,heven,hpay,hpow,hdsp,husp,hzero⟩

end MinModulus
