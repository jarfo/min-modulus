import MinModulus.TwoChainTightCorner

/-! Near-binary packing extracts full seed span. Exterior-column counting
then consumes positive corner slack, closing all interior two-chain bounds
and the original critical two-escape G1 branch from dimension nine onward.
The unrestricted global G1/G2/G3 gates remain open. -/

namespace MinModulus

/-- The quadratic packing error is smaller than half the binary scale
from dimension five onward. -/
theorem square_dimension_lt_half_binary {n : ℕ} (hn : 5 ≤ n) :
    (n+1)^2 < 2^(n+1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs : (n+1+1)^2 < 2*(n+1)^2 := by nlinarith only [hn]
    rw [show 2^(n+1+1)=2*2^(n+1) from pow_succ' 2 (n+1)]
    exact lt_trans hs (Nat.mul_lt_mul_of_pos_left ih (by decide))

/-- Actual subbinary two chains cannot be contained in a proper additive
subgroup: packing inside that subgroup would already exceed its size. -/
theorem subgroup_eq_top_of_valid_subbinary_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L))
    (S : AddSubgroup G) (hx : x ∈ S) (hy : y ∈ S) : S=⊤ := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have hmem : ∀ i, g i ∈ S := by
    apply Fin.addCases
    · intro i; rw [hleft]; exact S.nsmul_mem hx _
    · intro i; rw [hright]; exact S.nsmul_mem hy _
  let v : Fin (A+L) → S := fun i ↦ ⟨g i,hmem i⟩
  let xs : S := ⟨x,hx⟩
  let ys : S := ⟨y,hy⟩
  have hv : ValidTuple v := validTuple_of_comp S.subtype hg
  have hl : ∀ i : Fin A, v (Fin.castAdd L i)=2^i.val • xs := by
    intro i; apply Subtype.ext; exact hleft i
  have hr : ∀ i : Fin L, v (Fin.natAdd A i)=2^i.val • ys := by
    intro i; apply Subtype.ext; exact hright i
  have hp := near_binary_card_bound_of_valid_two_chains hA hL hn v hv xs ys hl hr
  have hi := S.card_mul_index
  simp only [Nat.card_eq_fintype_card] at hi
  have hG : 0 < Fintype.card G := Fintype.card_pos
  by_contra hproper
  have hi0 : S.index ≠ 0 := by intro hz; rw [hz,mul_zero] at hi; omega
  have hi1 : S.index ≠ 1 := by intro ho; exact hproper (AddSubgroup.index_eq_one.mp ho)
  have hi2 : 2 ≤ S.index := by omega
  have hhalf : 2*Fintype.card S ≤ Fintype.card G := by
    have hh := Nat.mul_le_mul_left (Fintype.card S) hi2
    nlinarith only [hh,hi]
  have hs := square_dimension_lt_half_binary hn
  rw [show 2^(A+L+1)=2*2^(A+L) from pow_succ' 2 (A+L)] at hs
  omega

/-- Full seed span is extracted from validity and subbinary cardinality;
there is no primitive-span, unit-seed or tight-packing assumption. -/
theorem seed_span_eq_top_of_valid_subbinary_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L)) :
    AddSubgroup.closure ({x,y} : Set G)=⊤ := by
  apply subgroup_eq_top_of_valid_subbinary_two_chains hA hL hn g hg x y hleft hright hcard
  · exact AddSubgroup.subset_closure (by simp)
  · exact AddSubgroup.subset_closure (by simp)

/-- Any common annihilator of the actual seeds annihilates the whole
ambient group in the subbinary regime. -/
theorem annihilates_group_of_valid_subbinary_two_chains
    {A L T : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L)) (hx : T • x=0) (hy : T • y=0) :
    ∀ z : G, T • z=0 := by
  let φ : G →+ G := nsmulAddMonoidHom T
  have ht := subgroup_eq_top_of_valid_subbinary_two_chains hA hL hn g hg x y hleft hright
    hcard φ.ker hx hy
  intro z
  have hz : z ∈ φ.ker := by rw [ht]; trivial
  exact hz

/-- Relation determinants are multiples of the cyclic modulus even
with positive packing slack. Full generation is a conclusion of validity. -/
theorem modulus_dvd_relation_determinant_of_valid_subbinary_two_chains
    {A L N K d u s : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : d • x+u • y=0) (hboundary : K • x=s • y) :
    N ∣ K*u+d*s := by
  obtain ⟨hx,hy⟩ := determinant_annihilates_two_chain_seeds x y K d u s hzero hboundary
  have hz := annihilates_group_of_valid_subbinary_two_chains hA hL hn g hg x y hleft hright
    (by simpa only [ZMod.card] using hN) hx hy (1 : ZMod N)
  simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff] using hz

/-- A represented left boundary has no nonzero first coordinate. The
existing interior zero relation excludes axes as well as mixed signs. -/
theorem first_coordinate_eq_zero_of_two_chain_boundary_representation
    {A L a b r s : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hr : r < 2^A) (hs : s < 2^L) (hrep : r • x+s • y=2^A • x) : r=0 := by
  have hrel : (2^A-r) • x=s • y := by
    apply add_left_cancel (a := r • x)
    rw [← add_nsmul,Nat.add_sub_of_le hr.le]
    exact hrep.symm
  by_contra hnot
  by_cases hs0 : s=0
  · have hz : (2^A-r) • x+0 • y=0 := by simpa only [hs0,zero_nsmul,add_zero] using hrel
    have hu := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL
      (two_chain_rectangle_wide_of_five_le hn) g hg x y hleft hright
      (by omega : 2^A-r < 2^A) (by positivity : 0 < 2^L) (Or.inl (by omega : 2^A-r ≠ 0))
      (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
      (Or.inl (by omega : 2^A-a ≠ 0)) hz hzero
    omega
  · exact positive_bounded_seed_relation_ne_of_valid_two_chains hA hL
      (by omega : 0 < 2^A-r) (by omega : 2^A-r < 2^A) (by omega : 0 < s) hs
      g hg x y hleft hright hrel

/-- Once a positive boundary relation is represented, its determinant
is exactly N, not a higher multiple, and it measures the entire slack. -/
theorem exact_boundary_determinant_of_valid_subbinary_two_chains
    {A L a b N s : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hs : s < 2^L) (hboundary : 2^A • x=s • y) :
    N=2^A*(2^L-b)+(2^A-a)*s ∧ b ≤ s ∧
      N+a*b-2^(A+L)=(2^A-a)*(s-b) := by
  have hp := rectangle_card_bound_of_valid_two_chains hA hL hn g hg x y hleft hright
    (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
    (Or.inl (by omega : 2^A-a ≠ 0)) hzero
  simp only [ZMod.card,Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le,pow_add] at hp
  have hd : 0 < 2^A-a := by omega
  have hu : 0 < 2^L-b := by omega
  have hda : (2^A-a)+a=2^A := Nat.sub_add_cancel ha.le
  have hub : (2^L-b)+b=2^L := Nat.sub_add_cancel hb.le
  have hR : 2^A*2^L=2^A*(2^L-b)+(2^A-a)*b+a*b := by
    have h1 := congrArg (fun v : ℕ ↦ 2^A*v) hub
    have h2 := congrArg (fun v : ℕ ↦ b*v) hda
    nlinarith only [h1,h2]
  have hpos : 0 < 2^A*(2^L-b)+(2^A-a)*s := by positivity
  have hlt : 2^A*(2^L-b)+(2^A-a)*s < 2*N := by
    have hds := Nat.mul_lt_mul_of_pos_left hs hd
    have heD : (2^A-a)*2^L=(2^A-a)*(2^L-b)+(2^A-a)*b := by
      simpa only [mul_add] using (congrArg (fun v : ℕ ↦ (2^A-a)*v) hub).symm
    have hdu := Nat.mul_lt_mul_of_pos_right (by omega : 2^A-a < 2^A) hu
    omega
  have hdiv := modulus_dvd_relation_determinant_of_valid_subbinary_two_chains hA hL hn
    g hg x y hleft hright hN hzero hboundary
  obtain ⟨k,hk⟩ := hdiv
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k=0 := by omega
    rw [hk0,mul_zero] at hk
    omega
  have hklt : k < 2 := by
    by_contra hh
    have hm := Nat.mul_le_mul_left N (by omega : 2 ≤ k)
    omega
  have hk1 : k=1 := by omega
  rw [hk1,mul_one] at hk
  have hbs : b ≤ s := by nlinarith only [hk,hp,hR,hd]
  refine ⟨hk.symm,hbs,?_⟩
  have hsb : (s-b)+b=s := Nat.sub_add_cancel hbs
  have hm := congrArg (fun v : ℕ ↦ (2^A-a)*v) hsb
  rw [pow_add]
  nlinarith only [hk,hR,hm,hp,Nat.sub_add_cancel hp]

/-- The previously proved axis inequality also controls the capacity of
every represented subbinary boundary, including positive packing slack. -/
theorem boundary_capacity_of_small_corner_determinant
    {n K H a b c N : ℕ} (hK : 0 < K) (hH : 0 < H)
    (ha : a < K) (hb : b < H) (hc : c < H)
    (hsmall : a+b ≤ n+1) (haxis : (K+1)*(n+1-K) ≤ H)
    (hN : N < K*H) (heq : N=K*(H-b)+(K-a)*c) :
    n ≤ 2*K-1+H-1-c := by
  have hd : 0 < K-a := by omega
  have hda : (K-a)+a=K := Nat.sub_add_cancel ha.le
  have hub : (H-b)+b=H := Nat.sub_add_cancel hb.le
  have hdc : (K-a)*c < K*b := by
    have hm := congrArg (fun v : ℕ ↦ K*v) hub
    nlinarith only [heq,hN,hm]
  by_cases hKn : K ≤ n+1
  · have ht : (n+1-K)+K=n+1 := Nat.sub_add_cancel hKn
    have hbt : b ≤ (n+1-K)+(K-a) := by omega
    have hmul := Nat.mul_le_mul_left K hbt
    have hcb : c < K+K*(n+1-K) := by
      by_cases hcK : c < K
      · omega
      · have hec : (c-K)+K=c := Nat.sub_add_cancel (by omega)
        have hh := Nat.mul_le_mul_right (c-K) (by omega : 1 ≤ K-a)
        have hm := congrArg (fun v : ℕ ↦ (K-a)*v) hec
        nlinarith only [hdc,hmul,hh,hm,hec]
    have hh : n+c < 2*K+H-1 := by
      have heH : 2*K+H-1+1=2*K+H := by omega
      nlinarith only [hcb,haxis,ht,heH]
    omega
  · omega

/-- Any represented positive boundary in the subbinary interior-corner
regime has enough complementary capacity to force actual one-escape
closure. Neither odd seeds nor tight packing are needed. -/
theorem one_escape_of_valid_subbinary_two_chain_boundary
    {A L a b N c : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hc : c < 2^L) (hboundary : 2^A • x=c • y) :
    ∃ z : Fin (A+L), ∀ i, i ≠ z → ∃ j, g j=2 • g i := by
  obtain ⟨he,hbc,_⟩ := exact_boundary_determinant_of_valid_subbinary_two_chains hA hL
    (by omega) ha0 ha hb0 hb g hg x y hleft hright hN hzero hc hboundary
  have hsmall := small_corner_of_nonzero_relation_of_valid_two_chains
    (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L) (Or.inl (by omega : 2^A-a ≠ 0))
    g hg x y hleft hright hzero
  simp only [Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le] at hsmall
  have haxis := two_chain_axis_corner_binary_inequality hA hL hn
  have hcap := boundary_capacity_of_small_corner_determinant (by positivity : 0 < 2^A)
    (by positivity : 0 < 2^L) ha hb hc hsmall haxis (by simpa only [pow_add] using hN) he
  have hK : 0 < 2^A := by positivity
  exact one_escape_of_valid_two_chain_boundary_capacity hA hL (by omega) hc (by omega)
    g hg x y hleft hright hboundary

/-- Two nonnegative zero relations annihilate both seeds by their
positive determinant difference. -/
theorem difference_determinant_annihilates_two_seeds
    {G : Type*} [AddCommGroup G] (x y : G) {K d u v : ℕ} (hle : d*v ≤ K*u)
    (hz : d • x+u • y=0) (hz' : K • x+v • y=0) :
    (K*u-d*v) • x=0 ∧ (K*u-d*v) • y=0 := by
  have h1 := congrArg (fun z ↦ u • z) hz'
  have h2 := congrArg (fun z ↦ v • z) hz
  have h3 := congrArg (fun z ↦ d • z) hz'
  have h4 := congrArg (fun z ↦ K • z) hz
  simp only [smul_add,smul_zero,← mul_nsmul] at h1 h2 h3 h4
  have hx : (K*u) • x=(d*v) • x := by
    apply add_right_cancel (b := (v*u) • y)
    exact h1.trans (by simpa only [Nat.mul_comm] using h2.symm)
  have hy : (K*u) • y=(d*v) • y := by
    apply add_left_cancel (a := (K*d) • x)
    calc
      _=(0 : G) := by simpa only [Nat.mul_comm] using h4
      _=_ := by simpa only [Nat.mul_comm] using h3.symm
  constructor
  · apply add_left_cancel (a := (d*v) • x)
    rw [← add_nsmul,Nat.add_sub_of_le hle,hx,add_zero]
  · apply add_left_cancel (a := (d*v) • y)
    rw [← add_nsmul,Nat.add_sub_of_le hle,hy,add_zero]

/-- A negative left-boundary coefficient of magnitude below the zero
relation's height would give a nonzero determinant strictly below N. -/
theorem no_short_negative_boundary_of_valid_subbinary_two_chains
    {A L a b N v : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hv : v < 2^L-b) : 2^A • x+v • y ≠ 0 := by
  intro hother
  have hd : 0 < 2^A-a := by omega
  have hu : 0 < 2^L-b := by omega
  have hlt : (2^A-a)*v < 2^A*(2^L-b) := by
    have h1 := Nat.mul_lt_mul_of_pos_left hv hd
    have h2 := Nat.mul_lt_mul_of_pos_right (by omega : 2^A-a < 2^A) hu
    omega
  obtain ⟨hx,hy⟩ := difference_determinant_annihilates_two_seeds x y hlt.le hzero hother
  have hz := annihilates_group_of_valid_subbinary_two_chains hA hL hn g hg x y hleft hright
    (by simpa only [ZMod.card] using hN) hx hy (1 : ZMod N)
  have hdiv : N ∣ 2^A*(2^L-b)-(2^A-a)*v := by
    simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff] using hz
  have hpos : 0 < 2^A*(2^L-b)-(2^A-a)*v := by omega
  have hle := Nat.le_of_dvd hpos hdiv
  have hp := rectangle_card_bound_of_valid_two_chains hA hL hn g hg x y hleft hright
    (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
    (Or.inl (by omega : 2^A-a ≠ 0)) hzero
  simp only [ZMod.card,Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le,pow_add] at hp
  have hda : (2^A-a)+a=2^A := Nat.sub_add_cancel ha.le
  have hub : (2^L-b)+b=2^L := Nat.sub_add_cancel hb.le
  have h1 := congrArg (fun z : ℕ ↦ 2^A*z) hub
  have h2 := congrArg (fun z : ℕ ↦ b*z) hda
  have hdb : 0 < (2^A-a)*b := mul_pos hd hb0
  have hKu : 2^A*(2^L-b) < N := by nlinarith only [hp,h1,h2,hdb]
  omega

/-- A collision between the retained rectangle and the short exterior
column necessarily gives a nonnegative represented boundary relation. -/
theorem boundary_of_short_exterior_column_collision
    {A L a b N r s t : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hr : r < 2^A) (hs : s < 2^L) (ht : t < 2^L-b)
    (hrep : r • x+s • y=2^A • x+t • y) :
    ∃ c : ℕ, c < 2^L ∧ 2^A • x=c • y := by
  by_cases hts : t ≤ s
  · have he : r • x+(s-t) • y=2^A • x := by
      apply add_right_cancel (b := t • y)
      calc
        _=r • x+s • y := by rw [add_assoc,← add_nsmul,Nat.sub_add_cancel hts]
        _=_ := hrep
    have hr0 := first_coordinate_eq_zero_of_two_chain_boundary_representation hA hL hn
      ha0 ha hb0 hb g hg x y hleft hright hzero hr (by omega : s-t < 2^L) he
    exact ⟨s-t,by omega,by simpa only [hr0,zero_nsmul,zero_add] using he.symm⟩
  · have hz := zero_relation_of_ordered_rectangle_collision x y hr.le (by omega : s ≤ t) hrep
    by_cases hr0 : r=0
    · exact (no_short_negative_boundary_of_valid_subbinary_two_chains hA hL hn
        ha0 ha hb0 hb g hg x y hleft hright hN hzero (by omega : t-s < 2^L-b)
        (by simpa only [hr0,Nat.sub_zero] using hz)).elim
    · have hu := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL
        (two_chain_rectangle_wide_of_five_le hn) g hg x y hleft hright
        (by omega : 2^A-r < 2^A) (by omega : t-s < 2^L) (Or.inl (by omega : 2^A-r ≠ 0))
        (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
        (Or.inl (by omega : 2^A-a ≠ 0)) hz hzero
      omega

/-- If the packing slack is smaller than the zero relation's height,
the exterior column cannot fit in the uncovered residues. A positive
boundary is therefore extracted from the actual tuple. -/
theorem exists_boundary_of_two_chain_slack_lt_height
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hslack : N+a*b-2^(A+L) < 2^L-b) :
    ∃ c : ℕ, c < 2^L ∧ 2^A • x=c • y := by
  classical
  open Finset in
  let B : Finset (ℕ × ℕ) := range (2^A) ×ˢ range (2^L)
  open Finset in
  let C : Finset (ℕ × ℕ) := Ico (2^A-a) (2^A) ×ˢ Ico (2^L-b) (2^L)
  let f : ℕ × ℕ → ZMod N := fun p ↦ p.1 • x+p.2 • y
  let w : ℕ → ZMod N := fun t ↦ 2^A • x+t • y
  have hCB : C ⊆ B := by
    intro p hp
    simp only [C,Finset.mem_product,Finset.mem_Ico] at hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp.1.2,Finset.mem_range.mpr hp.2.2⟩
  have hi : Set.InjOn f (↑(B \ C) : Set (ℕ × ℕ)) :=
    deleted_corner_rectangle_injective_of_valid_two_chains hA hL hn g hg x y hleft hright
      (by omega) (by omega) (Or.inl (by omega)) hzero
  have hR : ((B \ C).image f).card=2^(A+L)-a*b := by
    rw [Finset.card_image_of_injOn hi,Finset.card_sdiff_of_subset hCB]
    simp only [B,C,Finset.card_product,Finset.card_range,Nat.card_Ico,
      Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le,← pow_add]
  have hw : Set.InjOn w (↑(Finset.range (2^L-b)) : Set ℕ) := by
    have aux : ∀ t t', t < 2^L-b → t' < 2^L-b → t ≤ t' → t • y=t' • y → t=t' := by
      intro t t' ht ht' hle he
      by_contra hne
      have hz : (0 : ℕ) • x+(t'-t) • y=0 :=
        zero_relation_of_ordered_rectangle_collision x y (le_refl 0) hle
          (by simpa only [zero_nsmul,zero_add] using he)
      have hu := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL
        (two_chain_rectangle_wide_of_five_le hn) g hg x y hleft hright
        (by positivity : 0 < 2^A) (by omega : t'-t < 2^L) (Or.inr (by omega : t'-t ≠ 0))
        (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L)
        (Or.inl (by omega : 2^A-a ≠ 0)) hz hzero
      omega
    intro t ht t' ht' he
    have htt : t • y=t' • y := add_left_cancel he
    have ht0 := Finset.mem_range.mp ht
    have ht1 := Finset.mem_range.mp ht'
    rcases le_total t t' with hle | hle
    · exact aux t t' ht0 ht1 hle htt
    · exact (aux t' t ht1 ht0 hle htt.symm).symm
  have hW : ((Finset.range (2^L-b)).image w).card=2^L-b := by
    rw [Finset.card_image_of_injOn hw,Finset.card_range]
  by_contra hnot
  have hdis : Disjoint ((B \ C).image f) ((Finset.range (2^L-b)).image w) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
    obtain ⟨t,ht,htz⟩ := Finset.mem_image.mp hz'
    have hb' := (Finset.mem_sdiff.mp hp).1
    simp only [B,Finset.mem_product,Finset.mem_range] at hb'
    exact hnot (boundary_of_short_exterior_column_collision hA hL hn ha0 ha hb0 hb
      g hg x y hleft hright hN hzero hb'.1 hb'.2 (Finset.mem_range.mp ht) (hpz.trans htz.symm))
  have hcount := Finset.card_le_univ ((B \ C).image f ∪ (Finset.range (2^L-b)).image w)
  rw [Finset.card_union_of_disjoint hdis,hR,hW,ZMod.card] at hcount
  have hab : a*b ≤ 2^(A+L) := by rw [pow_add]; exact Nat.mul_le_mul ha.le hb.le
  omega

/-- The binary scale dominates the squared arm length from six onward. -/
theorem square_successor_le_two_pow_of_six_le {n : ℕ} (hn : 6 ≤ n) :
    (n+1)^2 ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs : (n+1+1)^2 ≤ 2*(n+1)^2 := by nlinarith only [hn]
    rw [show 2^(n+1)=2*2^n from pow_succ' 2 n]
    exact hs.trans (Nat.mul_le_mul_left 2 ih)

/-- From total dimension nine, a small corner with at least one dyadic
side has area no larger than one of the two relation coefficients. The
only quadratic-bound exceptions at dimension ten are non-dyadic (5,6). -/
theorem small_dyadic_corner_area_le_max_relation
    {A L a b : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 9 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (hs : a+b ≤ A+L+1) (hpow : (∃ e, a=2^e) ∨ ∃ e, b=2^e) :
    a*b ≤ max (2^A-a) (2^L-b) := by
  have aux : ∀ A L a b : ℕ, 0 < A → 0 < L → 9 ≤ A+L → A ≤ L →
      0 < a → a < 2^A → 0 < b → b < 2^L → a+b ≤ A+L+1 →
      ((∃ e, a=2^e) ∨ ∃ e, b=2^e) → a*b ≤ max (2^A-a) (2^L-b) := by
    intro A L a b hA hL hn hAL ha0 ha hb0 hb hs hpow
    by_cases hL6 : 6 ≤ L
    · have hq := square_successor_le_two_pow_of_six_le hL6
      have hsum : (a+b+1)^2 ≤ (2*L+2)^2 :=
        Nat.pow_le_pow_left (by omega : a+b+1 ≤ 2*L+2) 2
      have hp : a*b+b ≤ 2^L := by
        nlinarith only [hsum,hq,sq_nonneg ((a : ℤ)+1-b)]
      exact (by omega : a*b ≤ 2^L-b).trans (le_max_right _ _)
    · have hALcases : (A=4 ∧ L=5) ∨ (A=5 ∧ L=5) := by omega
      rcases hALcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hsum : (a+b+1)^2 ≤ 11^2 :=
          Nat.pow_le_pow_left (by omega : a+b+1 ≤ 11) 2
        have hp : a*b+b ≤ 32 := by nlinarith only [hsum,sq_nonneg ((a : ℤ)+1-b)]
        norm_num only [Nat.reducePow]
        exact (by omega : a*b ≤ 32-b).trans (le_max_right _ _)
      · norm_num only [Nat.reducePow] at ha hb ⊢
        by_contra hbad
        have hab : a ≤ 10 ∧ b ≤ 10 := by omega
        have hbad' : 32-a < a*b ∧ 32-b < a*b := by omega
        have hcases : (a=5 ∧ b=6) ∨ (a=6 ∧ b=5) := by
          interval_cases a <;> norm_num at hbad' ⊢ <;> omega
        have hp5 : ¬ ∃ e : ℕ, 5=2^e := by
          rintro ⟨e,he⟩
          have hh := Nat.lt_two_pow_self (n := e)
          have he5 : e < 5 := by omega
          interval_cases e <;> norm_num at he
        have hp6 : ¬ ∃ e : ℕ, 6=2^e := by
          rintro ⟨e,he⟩
          have hh := Nat.lt_two_pow_self (n := e)
          have he6 : e < 6 := by omega
          interval_cases e <;> norm_num at he
        rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hpow.elim hp5 hp6
        · exact hpow.elim hp6 hp5
  rcases le_total A L with hAL | hLA
  · exact aux A L a b hA hL hn hAL ha0 ha hb0 hb hs hpow
  · have hh := aux L A b a hL hA (by omega) hLA hb0 hb ha0 ha (by omega) hpow.symm
    simpa only [Nat.mul_comm,max_comm] using hh

/-- Small slack in EITHER orientation yields actual one-escape closure. -/
theorem one_escape_of_valid_two_chain_slack_lt_max_relation
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0)
    (hslack : N+a*b-2^(A+L) < max (2^A-a) (2^L-b)) :
    ∃ z : Fin (A+L), ∀ i, i ≠ z → ∃ j, g j=2 • g i := by
  rcases lt_max_iff.mp hslack with hsl | hsl
  · let v : Fin (L+A) → ZMod N := fun i ↦ g (finAddFlip i)
    have hv : ValidTuple v := validTuple_embedding finAddFlip.toEmbedding g hg
    have hl : ∀ i : Fin L, v (Fin.castAdd A i)=2^i.val • y := by
      intro i; simpa only [v,finAddFlip_apply_castAdd] using hright i
    have hr : ∀ i : Fin A, v (Fin.natAdd L i)=2^i.val • x := by
      intro i; simpa only [v,finAddFlip_apply_natAdd] using hleft i
    have hz : (2^L-b) • y+(2^A-a) • x=0 := by simpa only [add_comm] using hzero
    have hN' : N < 2^(L+A) := by simpa only [Nat.add_comm] using hN
    obtain ⟨c,hc,hc'⟩ := exists_boundary_of_two_chain_slack_lt_height hL hA (by omega)
      hb0 hb ha0 ha v hv y x hl hr hN' hz (by simpa only [Nat.add_comm,Nat.mul_comm] using hsl)
    obtain ⟨z,hz⟩ := one_escape_of_valid_subbinary_two_chain_boundary hL hA (by omega)
      hb0 hb ha0 ha v hv y x hl hr hN' hz hc hc'
    refine ⟨finAddFlip z,?_⟩
    intro i hi
    obtain ⟨j,hj⟩ := hz (finAddFlip.symm i) (by intro hh; apply hi; rw [← hh]; simp)
    exact ⟨finAddFlip j,by simpa only [v,Equiv.apply_symm_apply] using hj⟩
  · obtain ⟨c,hc,hc'⟩ := exists_boundary_of_two_chain_slack_lt_height hA hL (by omega)
      ha0 ha hb0 hb g hg x y hleft hright hN hzero hsl
    exact one_escape_of_valid_subbinary_two_chain_boundary hA hL hn ha0 ha hb0 hb
      g hg x y hleft hright hN hzero hc hc'

/-- ALL subbinary actual two chains with an interior corner have actual
one-escape closure from dimension nine onward. Positive slack is fully
consumed, not left as a further hypothesis. -/
theorem one_escape_of_valid_subbinary_interior_two_chains
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 9 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hN : N < 2^(A+L)) (hzero : (2^A-a) • x+(2^L-b) • y=0) :
    ∃ z : Fin (A+L), ∀ i, i ≠ z → ∃ j, g j=2 • g i := by
  have hs := small_corner_of_nonzero_relation_of_valid_two_chains
    (by omega : 2^A-a < 2^A) (by omega : 2^L-b < 2^L) (Or.inl (by omega : 2^A-a ≠ 0))
    g hg x y hleft hright hzero
  have hp := power_deficit_of_zero_relation_of_valid_two_chains hA hL
    (by omega : 0 < 2^A-a) (by omega : 2^A-a < 2^A)
    (by omega : 0 < 2^L-b) (by omega : 2^L-b < 2^L) g hg x y hleft hright hzero
  simp only [Nat.sub_sub_self ha.le,Nat.sub_sub_self hb.le] at hs hp
  have harea := small_dyadic_corner_area_le_max_relation hA hL hn ha0 ha hb0 hb hs hp
  have hab : 0 < a*b := mul_pos ha0 hb0
  exact one_escape_of_valid_two_chain_slack_lt_max_relation hA hL (by omega) ha0 ha hb0 hb
    g hg x y hleft hright hN hzero (by omega)

/-- FULL global bound for every actual interior two-chain corner in
dimension at least nine, with no odd-seed, capacity or slack premise. -/
theorem global_lower_bound_of_valid_interior_two_chains
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 9 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) : globalBound (A+L) ≤ N := by
  by_cases hN : N < 2^(A+L)
  · obtain ⟨z,hz⟩ := one_escape_of_valid_subbinary_interior_two_chains hA hL hn ha0 ha hb0 hb
      g hg x y hleft hright hN hzero
    exact global_lower_bound_of_valid_one_escape_affine_doubling (by omega) g hg z 0
      (by simpa only [add_zero] using hz)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- EVERY exact-stratum bound for the same unrestricted-slack interior
two-chain class, without any G1/G2/G3 input. -/
theorem stratum_lower_bound_of_valid_interior_two_chains
    {A L a b s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hn : 9 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g) (x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) : stratumBound (A+L) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  by_cases hN : 2^s*q < 2^(A+L)
  · obtain ⟨z,hz⟩ := one_escape_of_valid_subbinary_interior_two_chains hA hL hn ha0 ha hb0 hb
      g hg x y hleft hright hN hzero
    exact stratum_lower_bound_of_valid_one_escape_affine_doubling (by omega) hq g hg z 0
      (by simpa only [add_zero] using hz)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- DIRECT G1 half descent for ANY critical actual two-escape tuple in
parent dimension at least nine. Both cycle and acyclic branches are now
closed; no child induction, corner, span, unit or G2/G3 premise is needed. -/
theorem admitsValidTuple_half_of_critical_two_escape_nine_le
    {n s q : ℕ} (hq : Odd q) (hn : 8 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  obtain ⟨A,L,hA,hL,hsize,E,x,y,_,_,hleft,hright,a,c,ha0,ha,hc0,hc,_,_,_,_,hzero⟩ :=
    exists_interior_odd_seed_corner_of_critical_two_escape_without_half hq (by omega)
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hh := stratum_lower_bound_of_valid_interior_two_chains hq hA hL (by omega)
    ha0 ha hc0 hc _ hv x y hleft hright hzero
  rw [hsize] at hh
  omega

end MinModulus

