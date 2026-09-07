import MinModulus.ChainForestBalancedAxis

/-! Actual collision-profile packing inside arbitrary target sets.
Both parity classes of an even cyclic box pay their own deficit. Their
imbalance gives an extra absolute-value charge, with all short arms
retained. Original three-escape no-half data supply the stronger bounds;
the sharp global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Removing all actual profile rectangles makes the ordinary forest
box injective, without any lower bound on the arm widths. -/
theorem box_injective_outside_profile_rectangles
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    Function.Injective (fun p : {p : (∀ i, Fin (2^(L i))) //
      p ∉ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)} ↦
        ∑ i, (p.val i).val • x i) := by
  classical
  intro p q he
  by_contra hne
  have hne' : p.val ≠ q.val := fun h ↦ hne (Subtype.ext h)
  obtain ⟨w,hw,hp | hq⟩ := box_collision_meets_profile_lower_box L hL g hg E x b hchain
    p.val q.val hne' he
  · exact p.property (Finset.mem_biUnion.mpr ⟨w,hw,hp⟩)
  · exact q.property (Finset.mem_biUnion.mpr ⟨w,hw,hq⟩)

/-- Actual profile rectangles pay the packing deficit inside ANY
chosen target set. Avoided residues are charged in the same target set. -/
theorem profile_fibre_card_bound_with_avoided_set
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [DecidableEq G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (V F : Finset G) (hFV : F ⊆ V)
    (havoid : ∀ z ∈ F, ∀ p : (∀ i, Fin (2^(L i))), (∑ i, (p i).val • x i) ≠ z) :
    (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦ (∑ i, (p i).val • x i) ∈ V)).card+F.card ≤
      V.card+∑ w ∈ forestCollisionProfiles n L x,
        ((forestProfileLowerBox L w).filter (fun p ↦ (∑ i, (p i).val • x i) ∈ V)).card := by
  classical
  let U := (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)
  have hh := fibre_card_bound_with_avoided_set
    (fun p : (∀ i, Fin (2^(L i))) ↦ ∑ i, (p i).val • x i) (fun p ↦ p ∈ U)
    (box_injective_outside_profile_rectangles L hL g hg E x b hchain) V F hFV havoid
  have hset : (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      (∑ i, (p i).val • x i) ∈ V ∧ p ∈ U))=
      (forestCollisionProfiles n L x).biUnion (fun w ↦
        (forestProfileLowerBox L w).filter (fun p ↦ (∑ i, (p i).val • x i) ∈ V)) := by
    ext p
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,U]
    aesop
  rw [hset] at hh
  exact hh.trans (Nat.add_le_add_left (Finset.card_biUnion_le) _)

/-- Each parity class of an even cyclic forest box has exactly half
its points as soon as one seed is odd. -/
theorem twice_parity_box_card_eq_two_pow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hsize : (∑ i, L i)=n)
    (x : β → ZMod N) (hodd : ∃ a, Odd (x a).val) (v : Bool) :
    2*((Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card : ℤ)=((2^n : ℕ) : ℤ) := by
  classical
  have he := twice_even_binary_box_card_eq_two_pow hN L hL hsize x hodd
  cases v
  · have hs := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (∀ i, Fin (2^(L i)))))
      (fun p ↦ Even (∑ i, (p i).val • x i).val)
    have hbox : Fintype.card (∀ i, Fin (2^(L i)))=2^n := by
      simp only [Fintype.card_pi,Fintype.card_fin,Finset.prod_pow_eq_pow_sum,hsize]
    simp only [decide_eq_false_iff_not,card_univ,hbox] at *
    omega
  · simpa only [decide_eq_true_eq] using he

/-- Every actual short-arm profile packing holds separately in
BOTH parity classes. No all-long or supplied-relation hypothesis remains. -/
theorem parity_profile_card_bound_of_valid_chain_forest
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (v : Bool) :
    ((2^n : ℕ) : ℤ) ≤ (N : ℤ)+2*(∑ w ∈ forestCollisionProfiles n L x,
      (((forestProfileLowerBox L w).filter (fun p ↦
        decide (Even (∑ i, (p i).val • x i).val)=v)).card : ℤ)) := by
  classical
  let V := Finset.univ.filter (fun z : ZMod N ↦ decide (Even z.val)=v)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hh := profile_fibre_card_bound_with_avoided_set L hL g hg E x b hchain V ∅
    (Finset.empty_subset _) (by simp)
  simp only [V,mem_filter,mem_univ,true_and,card_empty,add_zero] at hh
  have hb := twice_parity_box_card_eq_two_pow hN L hL hsize x hodd v
  have hv : 2*(V.card : ℤ)=(N : ℤ) := by
    have he := twice_even_cyclic_card_eq_modulus hN
    cases v
    · have hs := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod N)))
        (fun z ↦ Even z.val)
      simp only [V,decide_eq_false_iff_not,card_univ,ZMod.card] at *
      omega
    · simpa only [V,decide_eq_true_eq] using he
  have hh' : ((Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card : ℤ) ≤ (V.card : ℤ)+
      ∑ w ∈ forestCollisionProfiles n L x,
        (((forestProfileLowerBox L w).filter (fun p ↦
          decide (Even (∑ i, (p i).val • x i).val)=v)).card : ℤ) := by
    exact_mod_cast hh
  omega

/-- The number of lower-profile box points in one actual parity class. -/
noncomputable def forestProfileParityMass
    {N : ℕ} {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ)
    (x : β → ZMod N) (v : Bool) : ℕ := by
  classical
  exact ∑ w ∈ forestCollisionProfiles n L x,
    ((forestProfileLowerBox L w).filter (fun p ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card

/-- The total of the two profile parity masses is exactly the sum
of their rectangle volumes, including every overflow pattern. -/
theorem forestProfileParityMass_add
    {N : ℕ} {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) (x : β → ZMod N) :
    forestProfileParityMass n L x true+forestProfileParityMass n L x false=
      ∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  rw [forestProfileParityMass,forestProfileParityMass,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp only [decide_eq_true_eq,decide_eq_false_iff_not]
  rw [Finset.card_filter_add_card_filter_not,forestProfileLowerBox_card]

/-- The imbalance between actual even and odd profile points is an
additional exact charge on the binary deficit, with arbitrary short arms. -/
theorem profile_parity_imbalance_card_bound
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) :
    ((2^n : ℕ) : ℤ)+|(forestProfileParityMass n L x true : ℤ)-
        (forestProfileParityMass n L x false : ℤ)| ≤
      (N : ℤ)+((∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) : ℕ) : ℤ) := by
  have he := parity_profile_card_bound_of_valid_chain_forest hN L hL g hg E x b hchain hodd true
  have ho := parity_profile_card_bound_of_valid_chain_forest hN L hL g hg E x b hchain hodd false
  have hE : (forestProfileParityMass n L x true : ℤ)=
      ∑ w ∈ forestCollisionProfiles n L x,
        (((forestProfileLowerBox L w).filter (fun p ↦
          decide (Even (∑ i, (p i).val • x i).val)=true)).card : ℤ) := by
    simp only [forestProfileParityMass,Nat.cast_sum]
  have hO : (forestProfileParityMass n L x false : ℤ)=
      ∑ w ∈ forestCollisionProfiles n L x,
        (((forestProfileLowerBox L w).filter (fun p ↦
          decide (Even (∑ i, (p i).val • x i).val)=false)).card : ℤ) := by
    simp only [forestProfileParityMass,Nat.cast_sum]
  rw [← hE] at he
  rw [← hO] at ho
  rw [← forestProfileParityMass_add,Nat.cast_add]
  rcases le_total (forestProfileParityMass n L x true : ℤ) (forestProfileParityMass n L x false : ℤ) with h | h
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

/-- At a subbinary multiple of 2^(s+1), EACH profile parity mass
is at least 2^s. The two parity deficits cannot subsidize one another. -/
theorem two_power_le_each_profile_parity_mass
    {n s q : ℕ} (hq : 0 < q) {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^(s+1)*q)) (b : ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^(s+1)*q < 2^n) (hodd : ∃ a, Odd (x a).val) (v : Bool) :
    2^s ≤ forestProfileParityMass n L x v := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨by positivity⟩
  have hN : 2 ∣ 2^(s+1)*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
  have hp := parity_profile_card_bound_of_valid_chain_forest hN L hL g hg E x b hchain hodd v
  have hp' : 2^n ≤ 2^(s+1)*q+2*forestProfileParityMass n L x v := by
    unfold forestProfileParityMass
    exact_mod_cast hp
  have hgap := two_pow_le_gap_of_subbinary_multiple hq hsub
  conv at hgap => lhs; rw [pow_succ]
  omega

/-- Original three-escape no-half data extract one to four actual
profiles whose even AND odd lower-point counts each pay the dyadic gap. -/
theorem exists_parity_profile_forest_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 9 ≤ n)
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
      (forestCollisionProfiles (n+1) L x).Nonempty ∧
      (forestCollisionProfiles (n+1) L x).card ≤ 4 ∧
      2^(s+1) ≤ 2^(n+1)-2^(s+1)*q ∧
      (2^(n+1)-2^(s+1)*q ≤ ∑ w ∈ forestCollisionProfiles (n+1) L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) ∧
      ∀ v : Bool, 2^s ≤ forestProfileParityMass (n+1) L x v := by
  classical
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,hfour,hgap,hvol⟩ :=
    exists_four_profile_forest_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  have ho : ∃ a, Odd (x a).val := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a ↦ Odd (x a).val)).card)
    exact ⟨a,(Finset.mem_filter.mp ha).2⟩
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,hfour,hgap,hvol,?_⟩
  exact fun v ↦ two_power_le_each_profile_parity_mass hq.pos L hL g hg E x b hchain
    (hc.trans_le (Nat.sub_le _ _)) ho v

end MinModulus
