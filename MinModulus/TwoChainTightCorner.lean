import MinModulus.TwoChainRelationOrder

/-! Tight corner packing gives actual cyclic boundary arrows. Combined
with boundary coefficient rigidity, this consumes the zero-slack corner
branch rather than leaving it as a geometric hypothesis. -/

namespace MinModulus
open Finset

/-- The retained rectangle after deleting the upper corner embeds in
the actual group. Expose the map used in the existing packing proof. -/
theorem deleted_corner_rectangle_injective_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    {d u : ℕ} (hd : d < 2^A) (hu : u < 2^L) (hne : d ≠ 0 ∨ u ≠ 0)
    (hz : d • x+u • y=0) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 • x+p.2 • y)
      (↑((range (2^A) ×ˢ range (2^L)) \ (Ico d (2^A) ×ˢ Ico u (2^L))) : Set (ℕ × ℕ)) := by
  classical
  let B : Finset (ℕ × ℕ) := range (2^A) ×ˢ range (2^L)
  let C : Finset (ℕ × ℕ) := Ico d (2^A) ×ˢ Ico u (2^L)
  let f : ℕ × ℕ → G := fun p ↦ p.1 • x+p.2 • y
  have hw := two_chain_rectangle_wide_of_five_le hn
  change Set.InjOn f (↑(B \ C) : Set (ℕ × ℕ))
  intro p hp q hq he
  have hpb := (mem_sdiff.mp hp).1
  have hqb := (mem_sdiff.mp hq).1
  simp only [B,mem_product,mem_range] at hpb hqb
  have aux : ∀ p q : ℕ × ℕ, p ∈ B \ C → q ∈ B \ C → f p=f q →
      p.1 ≤ q.1 → p.2 ≤ q.2 → p=q := by
    intro p q hp hq he hpq hpq'
    by_contra hnot
    have hqb := (mem_sdiff.mp hq).1
    simp only [B,mem_product,mem_range] at hqb
    have hdiff : q.1-p.1 ≠ 0 ∨ q.2-p.2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hnot (Prod.ext (by omega) (by omega))
    have hzero := zero_relation_of_ordered_rectangle_collision x y hpq hpq' he
    have heq := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL hw
      g hg x y hleft hright hd hu hne
      (show q.1-p.1 < 2^A by omega) (show q.2-p.2 < 2^L by omega) hdiff hz hzero
    apply (mem_sdiff.mp hq).2
    simp only [C,mem_product,mem_Ico]
    exact ⟨⟨by omega,hqb.1⟩,⟨by omega,hqb.2⟩⟩
  rcases rectangle_fibres_ordered_of_valid_two_chains hA hL g hg x y hleft hright
    hpb.1 hpb.2 hqb.1 hqb.2 he with h | h
  · exact aux p q hp hq he h.1 h.2
  · exact (aux q p hq hp he.symm h.1 h.2).symm

/-- Equality in the corner packing bound gives an ACTUAL full group
cover by retained rectangle points, with bounded original coefficients. -/
theorem rectangle_cover_of_valid_tight_two_chain_corner
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    {d u : ℕ} (hd : d < 2^A) (hu : u < 2^L) (hne : d ≠ 0 ∨ u ≠ 0)
    (hz : d • x+u • y=0)
    (htight : Fintype.card G+(2^A-d)*(2^L-u)=2^(A+L)) :
    ∀ z : G, ∃ r s : ℕ, r < 2^A ∧ s < 2^L ∧ (r < d ∨ s < u) ∧ r • x+s • y=z := by
  classical
  let B : Finset (ℕ × ℕ) := range (2^A) ×ˢ range (2^L)
  let C : Finset (ℕ × ℕ) := Ico d (2^A) ×ˢ Ico u (2^L)
  let f : ℕ × ℕ → G := fun p ↦ p.1 • x+p.2 • y
  have hCB : C ⊆ B := by
    intro p hp
    simp only [C,mem_product,mem_Ico] at hp
    exact mem_product.mpr ⟨mem_range.mpr hp.1.2,mem_range.mpr hp.2.2⟩
  have hi : Set.InjOn f (↑(B \ C) : Set (ℕ × ℕ)) :=
    deleted_corner_rectangle_injective_of_valid_two_chains hA hL hn g hg x y hleft hright hd hu hne hz
  have hcard : ((B \ C).image f).card=Fintype.card G := by
    rw [card_image_of_injOn hi,card_sdiff_of_subset hCB]
    simp only [B,C,card_product,card_range,Nat.card_Ico,← pow_add]
    omega
  have hall : (B \ C).image f=Finset.univ := Finset.eq_univ_of_card _ hcard
  intro z
  have hzmem : z ∈ (B \ C).image f := by rw [hall]; exact mem_univ z
  obtain ⟨p,hp,hpz⟩ := mem_image.mp hzmem
  have hb := (mem_sdiff.mp hp).1
  have hc := (mem_sdiff.mp hp).2
  simp only [B,mem_product,mem_range] at hb
  have hout : p.1 < d ∨ p.2 < u := by
    by_contra h
    push Not at h
    exact hc (by simp only [C,mem_product,mem_Ico]; omega)
  exact ⟨p.1,p.2,hb.1,hb.2,hout,hpz⟩

/-- Two actual seed relations give a common determinant annihilator. -/
theorem determinant_annihilates_two_chain_seeds
    {G : Type*} [AddCommGroup G] (x y : G) (K d u s : ℕ)
    (hzero : d • x+u • y=0) (hboundary : K • x=s • y) :
    (K*u+d*s) • x=0 ∧ (K*u+d*s) • y=0 := by
  have hx : (K*u) • x=(s*u) • y := by
    simpa only [mul_nsmul] using congrArg (fun z ↦ u • z) hboundary
  have hy : (d*s) • y=(d*K) • x := by
    simpa only [← mul_nsmul,Nat.mul_comm] using congrArg (fun z ↦ d • z) hboundary.symm
  constructor
  · calc
      (K*u+d*s) • x=(s*u) • y+(d*s) • x := by rw [add_nsmul,hx]
      _=s • (d • x+u • y) := by simp only [smul_add,← mul_nsmul,Nat.mul_comm]; abel
      _=0 := by rw [hzero,smul_zero]
  · calc
      (K*u+d*s) • y=(K*u) • y+(d*K) • x := by rw [add_nsmul,hy]
      _=K • (d • x+u • y) := by simp only [smul_add,← mul_nsmul,Nat.mul_comm]; abel
      _=0 := by rw [hzero,smul_zero]

/-- Actual coverage makes the relation determinant a multiple of the
cyclic modulus; generation is extracted from coverage, not assumed. -/
theorem modulus_dvd_relation_determinant_of_actual_cover
    {N : ℕ} (x y : ZMod N) (K d u s : ℕ)
    (hzero : d • x+u • y=0) (hboundary : K • x=s • y)
    (hcover : ∀ z : ZMod N, ∃ r v : ℕ, r • x+v • y=z) : N ∣ K*u+d*s := by
  obtain ⟨hx,hy⟩ := determinant_annihilates_two_chain_seeds x y K d u s hzero hboundary
  obtain ⟨r,v,hrv⟩ := hcover 1
  have hh : (K*u+d*s) • (1 : ZMod N)=0 := by
    rw [← hrv,smul_add,smul_comm (K*u+d*s) r x,smul_comm (K*u+d*s) v y,hx,hy]
    simp
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [nsmul_eq_mul,mul_one] using hh

/-- At a tight interior corner, the left boundary coefficient is
EXACTLY the opposite corner side. An odd left seed rules out an axial
representation, and actual coverage fixes the determinant to N. -/
theorem boundary_relation_of_valid_odd_seed_tight_corner
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (htight : N+a*b=2^(A+L)) : 2^A • x=b • y := by
  have hbinary : N < 2^(A+L) := by nlinarith [mul_pos ha0 hb0]
  have ht : Fintype.card (ZMod N)+(2^A-(2^A-a))*(2^L-(2^L-b))=2^(A+L) := by
    simpa only [ZMod.card,Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le] using htight
  have hcover := rectangle_cover_of_valid_tight_two_chain_corner hA hL (by omega)
    g hg x y hleft hright (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
    (Or.inl (by omega : 2^A-a ≠ 0)) hzero ht
  obtain ⟨r,s,hr,hs,_,hrep⟩ := hcover (2^A • x)
  have hrel : (2^A-r) • x=s • y := by
    apply add_left_cancel (a := r • x)
    rw [← add_nsmul,Nat.add_sub_of_le hr.le]
    exact hrep.symm
  have hr0 : r=0 := by
    by_contra hnot
    have hrp : 0 < r := by omega
    by_cases hs0 : s=0
    · let v : Fin (L+A) → ZMod N := fun i ↦ g (finAddFlip i)
      have hv : ValidTuple v := validTuple_embedding finAddFlip.toEmbedding g hg
      have hl : ∀ i : Fin L, v (Fin.castAdd A i)=2^i.val • y := by
        intro i
        simpa only [v,finAddFlip_apply_castAdd] using hright i
      have hh : ∀ i : Fin A, v (Fin.natAdd L i)=2^i.val • x := by
        intro i
        simpa only [v,finAddFlip_apply_natAdd] using hleft i
      have hbound := two_pow_le_modulus_of_valid_two_chains_odd_seed_axis hL hA (by omega)
        v hv y x hl hh hx (by omega : 0 < 2^A-r) (by omega : 2^A-r < 2^A)
        (by simpa only [hs0,zero_nsmul] using hrel)
      rw [Nat.add_comm L A] at hbound
      omega
    · exact positive_bounded_seed_relation_ne_of_valid_two_chains hA hL
        (by omega : 0 < 2^A-r) (by omega : 2^A-r < 2^A) (by omega : 0 < s) hs
        g hg x y hleft hright hrel
  have hboundary : 2^A • x=s • y := by simpa only [hr0,Nat.sub_zero] using hrel
  have hgen : ∀ z : ZMod N, ∃ r v : ℕ, r • x+v • y=z := by
    intro z
    obtain ⟨r,v,_,_,_,hh⟩ := hcover z
    exact ⟨r,v,hh⟩
  have hdiv := modulus_dvd_relation_determinant_of_actual_cover x y (2^A) (2^A-a) (2^L-b) s
    hzero hboundary hgen
  have hK : 0 < 2^A := by positivity
  have hH : 0 < 2^L := by positivity
  have hd : 0 < 2^A-a := by omega
  have hu : 0 < 2^L-b := by omega
  have hda : (2^A-a)+a=2^A := Nat.sub_add_cancel ha.le
  have hub : (2^L-b)+b=2^L := Nat.sub_add_cancel hb.le
  have hsH : 0 < 2^L-s := by omega
  have hsadd : (2^L-s)+s=2^L := Nat.sub_add_cancel hs.le
  rw [pow_add] at htight
  have hpos : 0 < 2^A*(2^L-b)+(2^A-a)*s := by positivity
  have hNeq : N=2^A*(2^L-b)+(2^A-a)*b := by
    have h1 := congrArg (fun v : ℕ ↦ 2^A*v) hub
    have h2 := congrArg (fun v : ℕ ↦ b*v) hda
    nlinarith only [htight,h1,h2]
  have hlt : 2^A*(2^L-b)+(2^A-a)*s < 2*N := by
    have hds : (2^A-a)*s < (2^A-a)*2^L := Nat.mul_lt_mul_of_pos_left hs hd
    have heD : (2^A-a)*2^L=(2^A-a)*(2^L-b)+(2^A-a)*b := by
      simpa only [mul_add] using (congrArg (fun v : ℕ ↦ (2^A-a)*v) hub).symm
    have hdu : (2^A-a)*(2^L-b) < 2^A*(2^L-b) :=
      Nat.mul_lt_mul_of_pos_right (by omega : 2^A-a < 2^A) hu
    omega
  obtain ⟨k,hk⟩ := hdiv
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hk1 : k=1 := by
    have hkpos : 0 < k := by
      by_contra hnot
      have hk0 : k=0 := by omega
      rw [hk0,mul_zero] at hk
      omega
    have hklt : k < 2 := by
      by_contra hnot
      have hh := Nat.mul_le_mul_left N (by omega : 2 ≤ k)
      omega
    omega
  rw [hk1,mul_one] at hk
  have hsb : s=b := by
    have hh : (2^A-a)*s=(2^A-a)*b := by omega
    nlinarith only [hh,hd]
  simpa only [hsb] using hboundary

/-- Tight interior packing with an odd seed extracts actual one-escape
closure. The complementary capacity is automatic from the small corner
and total-dimension width bounds. -/
theorem one_escape_of_valid_odd_seed_tight_corner
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (htight : N+a*b=2^(A+L)) :
    ∃ z : Fin (A+L), ∀ i, i ≠ z → ∃ j, g j=2 • g i := by
  have hboundary := boundary_relation_of_valid_odd_seed_tight_corner hA hL hn ha0 ha hb0 hb
    g hg x y hleft hright hx hzero htight
  have hsmall := small_corner_of_nonzero_relation_of_valid_two_chains
    (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L) (Or.inl (by omega : 2^A-a ≠ 0))
    g hg x y hleft hright hzero
  simp only [Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le] at hsmall
  have hwide := two_chain_rectangle_wide_of_five_le (by omega : 5 ≤ A+L)
  have hK : 0 < 2^A := by positivity
  have hH : 0 < 2^L := by positivity
  exact one_escape_of_valid_two_chain_boundary_capacity hA hL hb0 hb (by omega)
    g hg x y hleft hright hboundary

/-- FULL global bound for the tight odd-seed interior-corner class.
Actual one-escape closure is extracted, not a further assumption. -/
theorem global_lower_bound_of_valid_odd_seed_tight_corner
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (htight : N+a*b=2^(A+L)) : globalBound (A+L) ≤ N := by
  obtain ⟨z,hz⟩ := one_escape_of_valid_odd_seed_tight_corner hA hL hn ha0 ha hb0 hb
    g hg x y hleft hright hx hzero htight
  exact global_lower_bound_of_valid_one_escape_affine_doubling (by omega) g hg z 0
    (by simpa only [add_zero] using hz)

/-- EVERY exact-stratum bound also holds for tight odd-seed corners. -/
theorem stratum_lower_bound_of_valid_odd_seed_tight_corner
    {A L a b s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g) (x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (htight : 2^s*q+a*b=2^(A+L)) : stratumBound (A+L) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨z,hz⟩ := one_escape_of_valid_odd_seed_tight_corner hA hL hn ha0 ha hb0 hb
    g hg x y hleft hright hx hzero htight
  exact stratum_lower_bound_of_valid_one_escape_affine_doubling (by omega) hq g hg z 0
    (by simpa only [add_zero] using hz)

/-- DIRECT G1 half descent for ANY critical actual two-chain tuple
with tight interior corner packing. An even seed gives actual parity
deletion; otherwise the extracted one-escape bound contradicts criticality.
No G2/G3, child induction, primitivity or escape-count premise is needed. -/
theorem admitsValidTuple_half_of_critical_tight_two_chain_corner
    {n A L a c s q : ℕ} (hq : Odd q) (hn : 5 ≤ n) (hA : 0 < A) (hL : 0 < L)
    (ha0 : 0 < a) (ha : a < 2^A) (hc0 : 0 < c) (hc : c < 2^L)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (E : Fin (A+L) ≃ Fin (n+1)) (b x y : ZMod (2^(s+1)*q))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-c) • y=0)
    (htight : 2^(s+1)*q+a*c=2^(A+L)) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hd : 2 ∣ 2^(s+1)*q := by rw [hN]; exact dvd_mul_right 2 _
  obtain ⟨hx,_⟩ := both_seeds_odd_of_two_chains_without_half hN hd hA hL g hg E b x y hleft hright hnohalf
  have hxo := odd_val_of_parity_eq_one hd x hx
  have hsize : A+L=n+1 := by simpa using Fintype.card_congr E
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hb := stratum_lower_bound_of_valid_odd_seed_tight_corner hq hA hL (by omega)
    ha0 ha hc0 hc _ hv x y hleft hright hxo hzero htight
  rw [hsize] at hb
  omega

/-- The primitive coefficient gcd divides the ACTUAL corner packing
slack. This follows from exact relation order and a subtraction-free
formula for the retained rectangle size. -/
theorem gcd_dvd_two_chain_corner_packing_slack
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) :
    (2^A-a).gcd (2^L-b) ∣ N+a*b-2^(A+L) := by
  let d := 2^A-a
  let u := 2^L-b
  let D := d.gcd u
  let z := (d/D) • x+(u/D) • y
  have ho : addOrderOf z=D := addOrderOf_primitive_two_chain_relation hA hL hn
    (by dsimp [d]; omega) (by dsimp [d]; omega) (by dsimp [u]; omega) g hg x y hleft hright hzero
  have hNz : N • z=0 := by
    rw [nsmul_eq_mul,(ZMod.natCast_eq_zero_iff N N).mpr (dvd_refl N),zero_mul]
  have hDN : D ∣ N := by
    have hh := addOrderOf_dvd_of_nsmul_eq_zero hNz
    rwa [ho] at hh
  have hDT : D ∣ d*2^L+a*u := dvd_add
    (dvd_mul_of_dvd_left (Nat.gcd_dvd_left d u) (2^L))
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right d u) a)
  have hda : d+a=2^A := Nat.sub_add_cancel ha.le
  have hub : u+b=2^L := Nat.sub_add_cancel hb.le
  have hT : (d*2^L+a*u)+a*b=2^(A+L) := by
    rw [pow_add]
    have h1 := congrArg (fun v : ℕ ↦ 2^L*v) hda
    have h2 := congrArg (fun v : ℕ ↦ a*v) hub
    nlinarith only [h1,h2]
  have hp := rectangle_card_bound_of_valid_two_chains hA hL hn g hg x y hleft hright
    (by dsimp [d]; omega : d < 2^A) (by dsimp [u]; omega : u < 2^L)
    (Or.inl (by dsimp [d]; omega : d ≠ 0)) hzero
  simp only [d,u,ZMod.card,Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le] at hp
  have he : N+a*b-2^(A+L)=N-(d*2^L+a*u) := by omega
  change D ∣ N+a*b-2^(A+L)
  rw [he]
  exact Nat.dvd_sub hDN hDT

/-- After tight-packing G1 descent is consumed, the remaining actual
corner must pay at least ONE FULL primitive gcd in positive packing
slack. This is a strict arithmetic gain, not another closure premise. -/
theorem gcd_charge_of_critical_two_chain_corner_without_half
    {n A L a c s q : ℕ} (hq : Odd q) (hn : 5 ≤ n) (hA : 0 < A) (hL : 0 < L)
    (ha0 : 0 < a) (ha : a < 2^A) (hc0 : 0 < c) (hc : c < 2^L)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (E : Fin (A+L) ≃ Fin (n+1)) (b x y : ZMod (2^(s+1)*q))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-c) • y=0)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    2^(A+L)+(2^A-a).gcd (2^L-c) ≤ 2^(s+1)*q+a*c := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hsize : A+L=n+1 := by simpa using Fintype.card_congr E
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hp := rectangle_card_bound_of_valid_two_chains hA hL (by omega) _ hv x y hleft hright
    (by omega : 2^A-a < 2^A) (by omega : 2^L-c < 2^L) (Or.inl (by omega : 2^A-a ≠ 0)) hzero
  simp only [ZMod.card,Nat.sub_sub_self ha.le,Nat.sub_sub_self hc.le] at hp
  have hpos : 0 < 2^(s+1)*q+a*c-2^(A+L) := by
    by_contra hnot
    have ht : 2^(s+1)*q+a*c=2^(A+L) := by omega
    exact hnohalf (admitsValidTuple_half_of_critical_tight_two_chain_corner hq hn hA hL ha0 ha hc0 hc
      g hg hcritical E b x y hleft hright hzero ht)
  have hd := gcd_dvd_two_chain_corner_packing_slack hA hL (by omega) ha0 ha hc0 hc
    _ hv x y hleft hright hzero
  have hh := Nat.le_of_dvd hpos hd
  omega

/-- The ORIGINAL critical two-escape G1 residual now has a sparse
interior odd-seed corner paying for the binary deficit PLUS its full
primitive gcd. Zero packing slack has been actually eliminated. -/
theorem exists_gcd_charged_sparse_corner_of_critical_two_escape_without_half
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
        d+u ≤ n+2 ∧ Even (d+u) ∧
        2^(n+1)+(2^A-d).gcd (2^L-u) ≤ 2^(s+1)*q+d*u ∧
        ((∃ e, d=2^e) ∨ ∃ f, u=2^f) ∧
        ((∃ e, d=2^e) ∨ ∃ e f, d=2^e+2^f) ∧
        ((∃ e, u=2^e) ∨ ∃ e f, u=2^e+2^f) ∧
        (2^A-d) • x+(2^L-u) • y=0 := by
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,heven,_,hpow,hdsp,husp,hzero⟩ :=
    exists_sparse_interior_corner_of_critical_two_escape_without_half hq hn
      g hg hcritical B hB b hclosed hnohalf
  have hcharge := gcd_charge_of_critical_two_chain_corner_without_half hq hn hA hL hd0 hdA hu0 huL
    g hg hcritical E b x y hleft hright hzero hnohalf
  rw [hsize] at hcharge
  exact ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,heven,hcharge,hpow,hdsp,husp,hzero⟩

end MinModulus
