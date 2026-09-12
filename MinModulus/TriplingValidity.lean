import MinModulus.SIExtensionBound

/-!
# Tripling permutations in groups with injective doubling

A valid tuple permuted by tripling has one cycle of odd length. Tripling
splits increase multiset cardinality by two, so the component argument
must account for parity; duplicating the smaller odd component supplies
the even case. No conjectural lower bound is used.
-/
namespace MinModulus
open Finset

/-- Tripling-invariant index sets sum to zero when doubling is injective. -/
theorem sum_eq_zero_of_tripling_invariant
    {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (R : Equiv.Perm α) (x : α → G) (htriple : ∀ i, x (R i)=3 • x i)
    (C : Finset α) (hC : Set.BijOn R C C) : ∑ i ∈ C, x i=0 := by
  have hs : (∑ i ∈ C, x (R i))=∑ i ∈ C, x i :=
    Finset.sum_bij (fun i _ ↦ R i) (fun i hi ↦ hC.mapsTo hi)
      (fun _ _ _ _ he ↦ R.injective he)
      (fun j hj ↦ by obtain ⟨i,hi,he⟩ := hC.surjOn hj; exact ⟨i,hi,he⟩)
      (fun _ _ ↦ rfl)
  simp_rw [htriple] at hs
  rw [← Finset.smul_sum, show 3=2+1 by omega, add_nsmul, one_nsmul] at hs
  have hz : 2 • (∑ i ∈ C, x i)=0 :=
    add_right_cancel (by simpa using hs : 2 • (∑ i ∈ C, x i)+(∑ i ∈ C, x i)=0+(∑ i ∈ C, x i))
  apply hinj _ 0
  simpa [two_nsmul] using hz

/-- Ternary splitting realizes every cardinality with the seed's parity. -/
theorem exists_zero_multiset_of_tripling_closed
    {α G : Type*} [AddCommGroup G] (x : α → G) (C : Set α)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, x i=3 • x j)
    (s : Multiset α) (hspos : 0<s.card)
    (hsmem : ∀ i ∈ s, i ∈ C) (hsum : (s.map x).sum=0) (r : ℕ) :
    ∃ t : Multiset α, t.card=s.card+2*r ∧ (t.map x).sum=0 ∧
      ∀ i ∈ t, i ∈ C := by
  induction r with
  | zero => exact ⟨s,by omega,hsum,hsmem⟩
  | succ r ih =>
    obtain ⟨t,hcard,hzero,hmem⟩ := ih
    have htne : t≠0 := by intro hz; simp [hz] at hcard; omega
    have hd : t=0 ∨ ∃ i u, t=i ::ₘ u :=
      Multiset.induction_on t (Or.inl rfl) (fun i u _ ↦ Or.inr ⟨i,u,rfl⟩)
    rcases hd with hz | ⟨i,u,rfl⟩
    · exact False.elim (htne hz)
    obtain ⟨j,hj,hji⟩ := hpred i (hmem i (by simp))
    refine ⟨j ::ₘ j ::ₘ j ::ₘ u, by simp_all; omega, ?_, ?_⟩
    · simpa [Multiset.map_cons, Multiset.sum_cons, hji, three_nsmul, add_assoc] using hzero
    · intro a ha
      simp only [Multiset.mem_cons] at ha
      rcases ha with rfl | rfl | rfl | ha
      · exact hj
      · exact hj
      · exact hj
      · exact hmem a (by simp [ha])

/-- Parity-aware zero-sum expansion excludes every proper tripling component. -/
theorem tripling_invariant_eq_univ_of_valid
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (htriple : ∀ i, x (R i)=3 • x i)
    (C : Finset (Fin n)) (hCne : C.Nonempty) (hC : Set.BijOn R C C) :
    C=Finset.univ := by
  classical
  have htotal : ∑ i, x i=0 := sum_eq_zero_of_tripling_invariant hinj R x htriple univ (by simp)
  have expand (D : Finset (Fin n)) (hD : Set.BijOn R D D)
      (s : Multiset (Fin n)) (hspos : 0<s.card) (hsmem : ∀ i ∈ s, i ∈ D)
      (hsum : (s.map x).sum=0) (hle : s.card≤n) (hpar : s.card%2=n%2) :
      D=univ := by
    have hpred : ∀ i ∈ (D : Set (Fin n)), ∃ j ∈ (D : Set (Fin n)), x i=3 • x j := by
      intro i hi
      obtain ⟨j,hj,he⟩ := hD.surjOn hi
      exact ⟨j,hj,by rw [← he]; exact htriple j⟩
    obtain ⟨r,hr⟩ : ∃ r, n=s.card+2*r := ⟨(n-s.card)/2,by omega⟩
    obtain ⟨t,htcard,htsum,htmem⟩ := exists_zero_multiset_of_tripling_closed
      x D hpred s hspos hsmem hsum r
    have hall := multiset_count_eq_one_of_validTuple x hx t (by omega) (htsum.trans htotal.symm)
    exact Finset.eq_univ_of_forall (fun i ↦ htmem i (Multiset.count_pos.mp (by rw [hall i]; omega)))
  have hCzero : (C.val.map x).sum=0 := sum_eq_zero_of_tripling_invariant hinj R x htriple C hC
  by_cases hpar : C.card%2=n%2
  · exact expand C hC C.val hCne.card_pos (by simp) hCzero (by simpa using Finset.card_le_univ C) hpar
  by_contra hproper
  have hD : Set.BijOn R (Cᶜ : Finset (Fin n)) (Cᶜ : Finset (Fin n)) := by
    constructor
    · intro i hi
      change R i ∈ Cᶜ
      apply Finset.mem_compl.mpr
      intro hRi
      obtain ⟨j,hj,hji⟩ := hC.surjOn hRi
      have : j=i := R.injective hji
      exact (Finset.mem_compl.mp hi) (this ▸ hj)
    · constructor
      · exact fun _ _ _ _ he ↦ R.injective he
      · intro i hi
        refine ⟨R.symm i,?_,by simp⟩
        apply Finset.mem_compl.mpr
        intro hmem
        have := hC.mapsTo hmem
        exact (Finset.mem_compl.mp hi) (by simpa using this)
  have hDne : Cᶜ.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    have : C=univ := by simpa using congrArg (fun S : Finset (Fin n) ↦ Sᶜ) he
    exact hproper this)
  have hDzero : ((Cᶜ).val.map x).sum=0 := sum_eq_zero_of_tripling_invariant hinj R x htriple Cᶜ hD
  have hcards : C.card+Cᶜ.card=n := by simpa using Finset.card_add_card_compl C
  have hDproper : Cᶜ≠univ := by
    intro he
    obtain ⟨i,hi⟩ := hCne
    exact (Finset.mem_compl.mp (he ▸ Finset.mem_univ i)) hi
  by_cases hDpar : Cᶜ.card%2=n%2
  · exact hDproper (expand Cᶜ hD Cᶜ.val hDne.card_pos (by simp) hDzero
      (by simpa using Finset.card_le_univ Cᶜ) hDpar)
  have heven : n%2=0 := by omega
  rcases le_total C.card Cᶜ.card with hle | hle
  · apply hproper
    apply expand C hC (C.val+C.val) (by simp; omega) (by simp) (by simp [hCzero])
    · simp; omega
    · simp; omega
  · apply hDproper
    apply expand Cᶜ hD (Cᶜ.val+Cᶜ.val) (by simp; omega) (by simp) (by simp [hDzero])
    · simp; omega
    · simp; omega

/-- A tripling permutation of a nontrivial valid tuple has no fixed point. -/
theorem tripling_apply_ne_of_valid
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (htriple : ∀ i, x (R i)=3 • x i) (i : Fin n) : R i≠i := by
  classical
  intro he
  have hfull := tripling_invariant_eq_univ_of_valid hinj x hx R htriple {i}
    (Finset.singleton_nonempty i) (by simp [he])
  have hc := congrArg Finset.card hfull
  simp only [Finset.card_singleton,Finset.card_univ,Fintype.card_fin] at hc
  omega

/-- Every tripling permutation of a valid tuple is a single cycle. -/
theorem isCycle_of_valid_tripling
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (htriple : ∀ i, x (R i)=3 • x i) : R.IsCycle := by
  classical
  have hne := tripling_apply_ne_of_valid hn hinj x hx R htriple
  let a : Fin n := ⟨0,by omega⟩
  let C := (R.cycleOf a).support
  have hcycleOn : R.IsCycleOn C := R.isCycleOn_support_cycleOf a
  have ha : a ∈ C := (Equiv.Perm.mem_support_cycleOf_iff' (hne a)).2
    (Equiv.Perm.SameCycle.refl R a)
  have hfull : C=univ := tripling_invariant_eq_univ_of_valid hinj x hx R htriple C ⟨a,ha⟩ hcycleOn.1
  exact ⟨a,hne a,fun b _ ↦ hcycleOn.2 ha (by simp [hfull])⟩


/-- A valid tripling permutation enumerates the tuple by consecutive powers. -/
theorem exists_tripling_orbit_equiv_of_valid
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (htriple : ∀ i, x (R i)=3 • x i) :
    ∃ a, ∃ e : Equiv.Perm (Fin n), ∀ i, x (e i)=3^i.val • x a := by
  classical
  have hcycle := isCycle_of_valid_tripling hn hinj x hx R htriple
  have hne := tripling_apply_ne_of_valid hn hinj x hx R htriple
  let a : Fin n := ⟨0,by omega⟩
  let f : Fin n → Fin n := fun i ↦ R^[i.val] a
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨k,hk⟩ := hcycle.exists_pow_eq (hne a) (hne b)
    have hr : ∃ k, R^[k] a=b := ⟨k,by simpa only [Equiv.Perm.coe_pow] using hk⟩
    obtain ⟨k,hk,hkb⟩ := exists_iterate_lt_card_of_reachable R a b hr
    exact ⟨⟨k,by simpa using hk⟩,hkb⟩
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨Finite.injective_iff_surjective.mpr hf,hf⟩
  have hiter : ∀ k, x (R^[k] a)=3^k • x a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',htriple,ih,← mul_nsmul,pow_succ',Nat.mul_comm]
  exact ⟨a,e,fun i ↦ hiter i.val⟩

/-- Pairing adjacent ternary powers factors an even-length geometric sum. -/
theorem sum_ternary_powers_even_length (k : ℕ) :
    (∑ i : Fin (2*k), 3^i.val)=4*(∑ i : Fin k, 9^i.val) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = (∑ i : Fin (2*k), 3^i.val)+3^(2*k)+3^(2*k+1) := by
        rw [show 2*(k+1)=2*k+1+1 by omega,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
        rfl
      _ = 4*(∑ i : Fin k, 9^i.val)+4*9^k := by
        rw [ih,pow_succ,pow_mul]
        norm_num
        ring
      _ = _ := by rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]; ring

/-- A tripling-invariant valid tuple has odd length. For an even orbit,
doubling the even-position multiset would be a full-length zero-sum rival. -/
theorem odd_length_of_valid_tripling_perm
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G, x+x=y+y → x=y)
    (x : Fin n → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin n)) (htriple : ∀ i, x (R i)=3 • x i) : Odd n := by
  classical
  by_contra hodd
  obtain ⟨k,hk⟩ := Nat.not_odd_iff_even.mp hodd
  have hnk : n=2*k := by omega
  clear hk
  subst n
  obtain ⟨a,e,he⟩ := exists_tripling_orbit_equiv_of_valid hn hinj x hx R htriple
  have hzero : ∑ i, x i=0 := sum_eq_zero_of_tripling_invariant hinj R x htriple univ (by simp)
  have hfour : (4*(∑ i : Fin k, 9^i.val)) • x a=0 := by
    rw [← sum_ternary_powers_even_length,Finset.sum_smul]
    simp_rw [← he]
    exact (Equiv.sum_comp e x).trans hzero
  let t : Multiset (Fin (2*k)) := (Finset.univ : Finset (Fin k)).val.map
    (fun i ↦ e ⟨2*i.val,by omega⟩)
  have ht : (t.map x).sum=(∑ i : Fin k, 9^i.val) • x a := by
    simp only [t,Multiset.map_map,Function.comp_def]
    change (∑ i : Fin k, x (e ⟨2*i.val,by omega⟩))=_
    simp_rw [he,pow_mul]
    norm_num
    rw [Finset.sum_smul]
  have hfour' : 4 • (t.map x).sum=0 := by rw [ht,← mul_nsmul]; simpa [Nat.mul_comm] using hfour
  have htwo : (t.map x).sum+(t.map x).sum=0 := by
    apply hinj _ 0
    simpa only [show (4 : ℕ)=2+2 by omega,add_nsmul,two_nsmul,zero_add] using hfour'
  have hall := multiset_count_eq_one_of_validTuple x hx (t+t)
    (by simp [t]; omega) (by simpa [hzero,Multiset.map_add,Multiset.sum_add] using htwo)
  have hbad := hall a
  rw [Multiset.count_add] at hbad
  omega

/-- Odd cyclic moduli satisfy the tripling-cycle and odd-length restrictions. -/
theorem isCycle_and_odd_length_of_valid_tripling_zmod
    {n N : ℕ} [NeZero N] (hn : 2≤n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin n)) (ht : ∀ i, g (R i)=3 • g i) :
    R.IsCycle ∧ Odd n :=
  ⟨isCycle_of_valid_tripling hn (add_self_injective_zmod hN) g hg R ht,
   odd_length_of_valid_tripling_perm hn (add_self_injective_zmod hN) g hg R ht⟩


/-- Injective tripling turns range closure into the required permutation. -/
theorem odd_length_of_valid_tripling_closed
    {n : ℕ} (hn : 2≤n) {G : Type*} [AddCommGroup G]
    (hinj2 : ∀ x y : G, x+x=y+y → x=y)
    (hinj3 : ∀ x y : G, 3 • x=3 • y → x=y)
    (g : Fin n → G) (hg : ValidTuple g)
    (hclosed : ∀ i, ∃ j, g j=3 • g i) : Odd n := by
  classical
  let R : Fin n → Fin n := fun i ↦ Classical.choose (hclosed i)
  have hR (i : Fin n) : g (R i)=3 • g i := Classical.choose_spec (hclosed i)
  have hi : Function.Injective R := by
    intro i j he
    apply validTuple_injective g hg
    apply hinj3
    rw [← hR i,← hR j,he]
  let P : Equiv.Perm (Fin n) := Equiv.ofBijective R ⟨hi,Finite.surjective_of_injective hi⟩
  exact odd_length_of_valid_tripling_perm hn hinj2 g hg P hR

/-- At odd moduli coprime to three, every even-length valid tuple has a
coordinate whose triple leaves the tuple. -/
theorem exists_tripling_escape_of_even_valid_odd_zmod
    {n N : ℕ} [NeZero N] (hn : 2≤n) (heven : Even n)
    (hN : Odd N) (h3 : Nat.Coprime 3 N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    ∃ i, ∀ j, g j≠3 • g i := by
  classical
  by_contra hno
  push Not at hno
  have hunit : IsUnit ((3 : ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime 3 N).mpr h3
  have hodd := odd_length_of_valid_tripling_closed hn (add_self_injective_zmod hN)
    (fun x y he ↦ hunit.mul_left_cancel (by simpa only [nsmul_eq_mul] using he)) g hg hno
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end MinModulus
