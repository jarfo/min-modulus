import MinModulus.ChainForestProfileUnequalIntegral

/-! The complete maximal even-axis closure is consumed by the original
three-escape problem. A remaining subglobal forest has a unique longest
chain and either an odd unit seed, or an even seed for which every actual
collision profile uses a companion. The complete actual profile family,
parity charges, genuine endpoints, joint span and small index are retained.
The other profiles and unrestricted conjecture remain open. -/

namespace MinModulus
open Finset

/-- The exact dominant-width threshold forces every other chain to
be strictly shorter. This statement uses only the lengths. -/
theorem strictly_longest_of_dominant_width
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hsize : (∑ i, L i)=n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j)) :
    ∀ i, i ≠ j → L i < L j := by
  classical
  intro i hij
  have hpair : L j+L i ≤ n := by
    have hh := Finset.sum_le_sum_of_subset (Finset.subset_univ ({j,i} : Finset β)) (f := L)
    simpa only [Finset.sum_pair (Ne.symm hij),hsize] using hh
  by_contra hh
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : L j ≤ n-L j)
  have hm := Nat.mul_le_mul_right (2^(n-L j)+1) (show 1 ≤ n by omega)
  omega

/-- The maximal even-axis bound needs only the original two-odd-seed
count; both companion names and their parity are supplied internally. -/
theorem maximal_even_axis_global_bound_of_two_odd_seeds
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] [DecidableEq β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hmax : ∀ i, L i ≤ L j) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  have hc : (Finset.univ.erase j).card=2 := by simp [hr]
  obtain ⟨a,k,hak,hpair⟩ := Finset.card_eq_two.mp hc
  have haj : a ≠ j := (Finset.mem_erase.mp (by rw [hpair]; simp : a ∈ Finset.univ.erase j)).1
  have hkj : k ≠ j := (Finset.mem_erase.mp (by rw [hpair]; simp : k ∈ Finset.univ.erase j)).1
  exact even_axis_maximal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
    j a k haj hkj hak.symm hmax hj
    (odd_companions_of_three_seeds hr (fun i ↦ (x i).val) hodd j (Nat.not_odd_iff_even.mpr hj)) v hv hvz

/-- Below the global bound, every profile has a positive companion
coefficient when the longest seed is even. -/
theorem positive_companion_of_subglobal_maximal_even_seed
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] [DecidableEq β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hmax : ∀ i, L i ≤ L j) (hj : Even (x j).val)
    (hsub : N < globalBound n)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x) :
    ∃ i, i ≠ j ∧ 0 < (v i).val := by
  by_contra hh
  have hz : ∀ i, i ≠ j → (v i).val=0 := by
    intro i hij
    by_contra hi
    exact hh ⟨i,hij,by omega⟩
  have hb := maximal_even_axis_global_bound_of_two_odd_seeds hn hN hr L hL g hg E x b hchain hgen
    hodd j hmax hj v hv hz
  omega

/-- Original subglobal three-escape data with a maximal even-axis
profile have an actual half-modulus child. Failed descent supplies the
missing companion parity and genuine endpoints internally. -/
theorem admitsValidTuple_half_of_subglobal_three_escape_maximal_even_axis
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcglobal : 2^(s+1)*q < globalBound (n+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a)
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val)
    (j : A) (hmax : ∀ i, L i ≤ L j) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles (n+1) L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hNeven : 2 ∣ 2^(s+1)*q := ⟨2^s*q,hN⟩
  have hle : globalBound (n+1) ≤ stratumBound (n+1) (s+1) := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (min_le_right _ _)) _
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half
    hq g hg (hcglobal.trans_le hle) A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    rw [hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)]
    exact hgenuine a.val a.property t
  have ho := two_le_odd_seed_card_of_chain_forest_without_half hN hNeven L hL g hg E x b hchain hnohalf
  have hodd : 2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card := by
    apply ho.trans
    apply Finset.card_le_card
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      odd_val_of_parity_eq_one hNeven (x a) (Finset.mem_filter.mp ha).2⟩
  have hb := maximal_even_axis_global_bound_of_two_odd_seeds (by omega) hN hr L hL
    g hg E x b hchain hgen hodd j hmax hj v hv hvz
  omega

/-- The same original half descent holds in every critical high
stratum. The high-stratum premise is essential to this global consumer. -/
theorem admitsValidTuple_half_of_critical_high_stratum_maximal_even_axis
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1)) (hs : Nat.log 2 (n+1) ≤ s+1)
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a)
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val)
    (j : A) (hmax : ∀ i, L i ≤ L j) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles (n+1) L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : AdmitsValidTuple n (2^s*q) := by
  have hcglobal : 2^(s+1)*q < globalBound (n+1) := by
    simpa only [stratumBound,globalBound,min_eq_right hs] using hc
  exact admitsValidTuple_half_of_subglobal_three_escape_maximal_even_axis hq hn g hg hcglobal
    A hA b hclosed L hL E x hchain hend j hmax hj v hv hvz

/-- The original subglobal no-half residual retains the entire actual
profile family and all parity, volume, span and index data. Its unique
longest chain is now an odd unit or an even seed whose every profile
uses a companion. The closed maximal even-axis family is absent. -/
theorem exists_dominant_profile_residual_of_subglobal_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcglobal : 2^(s+1)*q < globalBound (n+1))
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
      (forestCollisionProfiles (n+1) L x).card ≤ 3 ∧
      2^(s+1) ≤ 2^(n+1)-2^(s+1)*q ∧
      (2^(n+1)-2^(s+1)*q ≤ ∑ w ∈ forestCollisionProfiles (n+1) L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) ∧
      (∀ v : Bool, 2^s ≤ forestProfileParityMass (n+1) L x v) ∧
      (∀ w ∈ forestCollisionProfiles (n+1) L x,
        (Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card ≤ 1 ∧
        ∀ a, 2^(L a)-1 < (w a).val →
          (∃ e, (w a).val+1=2^(L a)+2^e) ∧
          ∀ i, i ≠ a → (w i).val < 2^(L i)-1 ∧ ∃ e, (w i).val+1=2^e) ∧
      ∃ j, (∀ i, i ≠ j → L i < L j) ∧
        (∀ i, i ≠ j → 2^(L i) ≤ 2*(n+1)) ∧
        n+1-2*Nat.log 2 (2*(n+1)) ≤ L j ∧
        (n+1)*(2^(n+1-L j)+1) ≤ 2^(L j) ∧
        (∃ e ≤ Nat.log 2 (2*(n+1)), (2^(s+1)*q).gcd (x j).val=2^e ∧
          (e=0 ∨ ∃ i, i ≠ j ∧ e ≤ L i)) ∧
        (2^(s+1)*q).gcd (x j).val ≤ 2*(n+1) ∧
        (q.Coprime (x j).val ∧ q ∣ addOrderOf (x j)) ∧
        ((Odd (x j).val ∧ IsUnit (x j)) ∨
          (Even (x j).val ∧ ∀ v ∈ forestCollisionProfiles (n+1) L x,
            ∃ i, i ≠ j ∧ 0 < (v i).val)) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hle : globalBound (n+1) ≤ stratumBound (n+1) (s+1) := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (min_le_right _ _)) _
  have hc := hcglobal.trans_le hle
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,hthree,hgap,hvol,hparity,hshape⟩ :=
    exists_three_dyadic_profile_forest_of_critical_three_escape_without_half
      hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    rw [hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)]
    exact hgenuine a t
  have hsub : 2^(s+1)*q < 2^(n+1) := hcglobal.trans_le (Nat.sub_le _ _)
  obtain ⟨j,hrest,hlong,hlarge,_⟩ := exists_dominant_two_primary_seed_of_subbinary_genuine_three_chains
    (by omega) hr L hL g hg E x b hchain hgen (by simpa only [ZMod.card] using hsub)
  have hstrict := strictly_longest_of_dominant_width (by omega : 0 < n+1) L hsize j hlarge
  have hmax : ∀ i, L i ≤ L j := by
    intro i
    by_cases hij : i=j
    · rw [hij]
    · exact (hstrict i hij).le
  obtain ⟨e,_,he,hfit⟩ := dominant_index_exponent_le_one_companion_of_three_chains
    hr L hL g hg E x b hchain hsub j hlarge hodd
  have hwidth : 2^e ≤ 2*(n+1) := by
    rcases hfit with he0 | ⟨a,haj,ha⟩
    · rw [he0,pow_zero]; omega
    · exact (Nat.pow_le_pow_right (by decide : 0 < 2) ha).trans (hrest a haj)
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,hthree,hgap,hvol,hparity,hshape,
    j,hstrict,hrest,hlong,hlarge,⟨e,Nat.le_log_of_pow_le (by decide : 1 < 2) hwidth,he,hfit⟩,
    by rwa [he],odd_part_of_subbinary_dominant_seed hq L hL g hg E x b hchain hsub j hlarge,?_⟩
  by_cases hj : Odd (x j).val
  · exact Or.inl ⟨hj,isUnit_of_odd_subbinary_dominant_seed L hL g hg E x b hchain hsub j hlarge hj⟩
  · have hje : Even (x j).val := Nat.not_odd_iff_even.mp hj
    exact Or.inr ⟨hje,fun v hv ↦ positive_companion_of_subglobal_maximal_even_seed
      (by omega) hN hr L hL g hg E x b hchain hgen hodd j hmax hje hcglobal v hv⟩

end MinModulus
