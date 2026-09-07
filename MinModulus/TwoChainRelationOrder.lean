import MinModulus.TwoChainSparseCorner

/-! Every common factor of the unique actual rectangle relation gives
the exact additive order of its divided direction. This connects sparse
corner geometry to cyclic modulus divisibility without a unit premise. -/

namespace MinModulus
open Finset

/-- Dividing an actual nonzero rectangle relation by ANY common factor
produces an element of exactly that additive order. A smaller order would
give a second nonzero rectangle relation, contradicting uniqueness. -/
theorem addOrderOf_divided_two_chain_relation
    {A L D r s : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (hD : 0 < D) (hne : r ≠ 0 ∨ s ≠ 0) (hr : D*r < 2^A) (hs : D*s < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (D*r) • x+(D*s) • y=0) : addOrderOf (r • x+s • y)=D := by
  let z := r • x+s • y
  have hkill : D • z=0 := by simpa only [z,smul_add,← mul_nsmul,Nat.mul_comm] using hzero
  have hdvd : addOrderOf z ∣ D := addOrderOf_dvd_of_nsmul_eq_zero hkill
  have ho : 0 < addOrderOf z := by
    by_contra hnot
    have hz : addOrderOf z=0 := by omega
    rw [hz,zero_dvd_iff] at hdvd
    omega
  have hle : addOrderOf z ≤ D := Nat.le_of_dvd hD hdvd
  have hr' : addOrderOf z*r < 2^A := lt_of_le_of_lt (Nat.mul_le_mul_right r hle) hr
  have hs' : addOrderOf z*s < 2^L := lt_of_le_of_lt (Nat.mul_le_mul_right s hle) hs
  have hneD : D*r ≠ 0 ∨ D*s ≠ 0 := by
    rcases hne with hh | hh
    · exact Or.inl (mul_ne_zero hD.ne' hh)
    · exact Or.inr (mul_ne_zero hD.ne' hh)
  have hneO : addOrderOf z*r ≠ 0 ∨ addOrderOf z*s ≠ 0 := by
    rcases hne with hh | hh
    · exact Or.inl (mul_ne_zero ho.ne' hh)
    · exact Or.inr (mul_ne_zero ho.ne' hh)
  have hz' : (addOrderOf z*r) • x+(addOrderOf z*s) • y=0 := by
    simpa only [z,smul_add,← mul_nsmul,Nat.mul_comm] using addOrderOf_nsmul_eq_zero z
  have he := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL
    (two_chain_rectangle_wide_of_five_le hn) g hg x y hleft hright hr hs hneD hr' hs' hneO hzero hz'
  rcases hne with hh | hh
  · have hp : 0 < r := Nat.pos_of_ne_zero hh
    change addOrderOf z=D
    nlinarith [he.1]
  · have hp : 0 < s := Nat.pos_of_ne_zero hh
    change addOrderOf z=D
    nlinarith [he.2]

/-- The primitive integer direction of the unique interior relation
has additive order equal to the coefficient gcd, even for nonunit seeds. -/
theorem addOrderOf_primitive_two_chain_relation
    {A L d u : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (hd0 : 0 < d) (hd : d < 2^A) (hu : u < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : d • x+u • y=0) :
    addOrderOf ((d/d.gcd u) • x+(u/d.gcd u) • y)=d.gcd u := by
  have hD : 0 < d.gcd u := Nat.gcd_pos_of_pos_left u hd0
  have hdD : d.gcd u*(d/d.gcd u)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d u)
  have huD : d.gcd u*(u/d.gcd u)=u := Nat.mul_div_cancel' (Nat.gcd_dvd_right d u)
  apply addOrderOf_divided_two_chain_relation hA hL hn hD
    (Or.inl (by intro h; rw [h,mul_zero] at hdD; omega))
    (by simpa only [hdD] using hd) (by simpa only [huD] using hu)
    g hg x y hleft hright
  simpa only [hdD,huD] using hzero

/-- Every common coefficient divisor of the actual interior relation
divides the cyclic modulus. This is extracted from exact order. -/
theorem common_factor_dvd_modulus_of_valid_two_chain_relation
    {A L D r s N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (hD : 0 < D) (hne : r ≠ 0 ∨ s ≠ 0) (hr : D*r < 2^A) (hs : D*s < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (D*r) • x+(D*s) • y=0) : D ∣ N := by
  have ho := addOrderOf_divided_two_chain_relation hA hL hn hD hne hr hs g hg x y hleft hright hzero
  have hN : N • (r • x+s • y)=0 := by
    rw [nsmul_eq_mul,(ZMod.natCast_eq_zero_iff N N).mpr (dvd_refl N),zero_mul]
  have hd := addOrderOf_dvd_of_nsmul_eq_zero hN
  rwa [ho] at hd

/-- For two odd canonical seeds, the divided direction has exactly
the parity of the sum of its two integer coefficients. -/
theorem parity_val_of_two_odd_seed_direction
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) (r s : ℕ) (x y : ZMod N)
    (hx : Odd x.val) (hy : Odd y.val) :
    (r • x+s • y).val % 2=(r+s) % 2 := by
  have hc : r • x+s • y=((r*x.val+s*y.val : ℕ) : ZMod N) := by
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [hc,ZMod.val_natCast,Nat.mod_mod_of_dvd _ hN]
  have hmx : r*x.val % 2=r % 2 := by rw [Nat.mul_mod,Nat.odd_iff.mp hx,mul_one,Nat.mod_mod]
  have hmy : s*y.val % 2=s % 2 := by rw [Nat.mul_mod,Nat.odd_iff.mp hy,mul_one,Nat.mod_mod]
  rw [Nat.add_mod,hmx,hmy]
  exact (Nat.add_mod r s 2).symm

/-- An even element at an even cyclic modulus has additive order
dividing the actual half modulus, with its representative retained. -/
theorem addOrderOf_dvd_half_of_even_val
    {N M : ℕ} [NeZero N] (hN : N=2*M) (z : ZMod N) (hz : Even z.val) :
    addOrderOf z ∣ M := by
  obtain ⟨k,hk⟩ := hz
  have hd : N ∣ M*z.val := by
    refine ⟨k,?_⟩
    rw [hk]
    nlinarith [hN]
  have hh : M • z=0 := by
    have hc := (ZMod.natCast_eq_zero_iff (M*z.val) N).mpr hd
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul] using hc
  exact addOrderOf_dvd_of_nsmul_eq_zero hh

/-- Divided coefficient parity locks the common factor to the cyclic
modulus: even direction gives a half-modulus divisor; odd direction
gives an ODD index over the factor. No full-unit assumption is needed. -/
theorem parity_lock_of_divided_odd_seed_two_chain_relation
    {A L D r s N M : ℕ} [NeZero N] (hN : N=2*M)
    (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (hD : 0 < D) (hne : r ≠ 0 ∨ s ≠ 0) (hr : D*r < 2^A) (hs : D*s < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hy : Odd y.val) (hzero : (D*r) • x+(D*s) • y=0) :
    (Even (r+s) → D ∣ M) ∧ (Odd (r+s) → ∃ q : ℕ, Odd q ∧ N=D*q) := by
  have hd : 2 ∣ N := by rw [hN]; exact dvd_mul_right 2 M
  have ho := addOrderOf_divided_two_chain_relation hA hL hn hD hne hr hs g hg x y hleft hright hzero
  have hp := parity_val_of_two_odd_seed_direction hd r s x y hx hy
  constructor
  · intro heven
    have hz : Even (r • x+s • y).val := by rw [Nat.even_iff,hp]; exact Nat.even_iff.mp heven
    have hh := addOrderOf_dvd_half_of_even_val hN _ hz
    rwa [ho] at hh
  · intro hodd
    have hz : Odd (r • x+s • y).val := by rw [Nat.odd_iff,hp]; exact Nat.odd_iff.mp hodd
    obtain ⟨q,hq,hh⟩ := exists_odd_index_over_addOrderOf_of_odd_val _ hz
    exact ⟨q,hq,by simpa only [ho] using hh⟩

/-- The actual divided direction decides the dyadic depth. At modulus
2^(s+1)*q, an even direction has depth at most s; an odd direction has
depth EXACTLY s+1. This includes the capped branch instead of assuming
all corner factors are below the modulus valuation. -/
theorem dyadic_depth_lock_of_odd_seed_two_chain_relation
    {A L t r u s q : ℕ} (hq : Odd q)
    (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (hne : r ≠ 0 ∨ u ≠ 0) (hr : 2^t*r < 2^A) (hu : 2^t*u < 2^L)
    (g : Fin (A+L) → ZMod (2^(s+1)*q)) (hg : ValidTuple g) (x y : ZMod (2^(s+1)*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hy : Odd y.val) (hzero : (2^t*r) • x+(2^t*u) • y=0) :
    (Even (r+u) → t ≤ s) ∧ (Odd (r+u) → t=s+1) := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  obtain ⟨he,ho⟩ := parity_lock_of_divided_odd_seed_two_chain_relation hN hA hL hn
    (by positivity : 0 < 2^t) hne hr hu g hg x y hleft hright hx hy hzero
  constructor
  · intro heven
    have hd : 2^t ∣ 2^s := (hq.coprime_two_left.pow_left t).dvd_of_dvd_mul_right (he heven)
    have hle : 2^t ≤ 2^s := Nat.le_of_dvd (by positivity) hd
    by_contra hnot
    have hlt : 2^s < 2^t := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  · intro hodd
    obtain ⟨v,hv,hh⟩ := ho hodd
    exact (dyadic_exponent_eq_of_odd_factor_eq hq hv hh).symm

/-- The primitive direction of an actual odd-seed interior corner
supplies modulus divisibility and its full parity-dependent index lock.
All coefficients come from the original corner, not a proposed order. -/
theorem gcd_parity_lock_of_valid_odd_seed_two_chain_corner
    {A L a b N M : ℕ} [NeZero N] (hN : N=2*M)
    (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hy : Odd y.val) (hzero : (2^A-a) • x+(2^L-b) • y=0) :
    let D := (2^A-a).gcd (2^L-b)
    let r := (2^A-a)/D
    let u := (2^L-b)/D
    D ∣ N ∧ (Even (r+u) → D ∣ M) ∧ (Odd (r+u) → ∃ q : ℕ, Odd q ∧ N=D*q) := by
  dsimp only
  let d := 2^A-a
  let v := 2^L-b
  let D := d.gcd v
  have hD : 0 < D := Nat.gcd_pos_of_pos_left v (by dsimp [d]; omega)
  have hdD : D*(d/D)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d v)
  have hvD : D*(v/D)=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right d v)
  have hne : d/D ≠ 0 ∨ v/D ≠ 0 := Or.inl (by
    intro he
    rw [he,mul_zero] at hdD
    dsimp [d] at hdD
    omega)
  have hdr : D*(d/D) < 2^A := by rw [hdD]; dsimp [d]; omega
  have hvr : D*(v/D) < 2^L := by rw [hvD]; dsimp [v]; omega
  have hz : (D*(d/D)) • x+(D*(v/D)) • y=0 := by rw [hdD,hvD]; exact hzero
  have hdvd := common_factor_dvd_modulus_of_valid_two_chain_relation hA hL hn hD hne hdr hvr
    g hg x y hleft hright hz
  have hlock := parity_lock_of_divided_odd_seed_two_chain_relation hN hA hL hn hD hne hdr hvr
    g hg x y hleft hright hx hy hz
  exact ⟨hdvd,hlock⟩

end MinModulus
