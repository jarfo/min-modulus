import MinModulus.ChainForestProfileDoubleOverflow

/-! A subglobal genuine even-axis forest has exactly its axis base and
one incompatible half-width overflow. Odd packing charges only the
quarter-companion rectangle, giving a direct conditional global bound.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- In three chains, actual profiles overflowing the same arm coincide
under the joint wide-box condition. -/
theorem forestCollisionProfiles_eq_of_overflow_on_same_arm
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w u : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (a : β) (hwa : 2^(L a)-1 < (w a).val) (hua : 2^(L a)-1 < (u a).val) : w=u := by
  classical
  have hlow (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
      (ha : 2^(L a)-1 < (v a).val) : ∀ i, i ≠ a → (v i).val < 2^(L i)-1 := by
    have hvm : (∑ i, (v i).val)<n ∧
        (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    intro i hia
    exact (dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
      (fun i ↦ (v i).val) (fun i ↦ by have := (v i).isLt; omega) hvm.1 hvm.2 a ha i hia).1
  apply forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain w u hw hu
  intro i
  by_cases hi : i=a
  · subst i; exact iff_of_true hwa hua
  · have := hlow w hw hwa i hi
    have := hlow u hu hua i hi
    omega

/-- Every other profile beside an axis base overflows a companion arm. -/
theorem profile_eq_axis_base_or_companion_overflow
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hwidth : n ≤ 2^(L j))
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    w=v ∨ ∃ a, a ≠ j ∧ 2^(L a)-1 < (w a).val := by
  classical
  have hsmall (u : ∀ i, Fin (2*(2^(L i)-1)+1)) (hu : u ∈ forestCollisionProfiles n L x) :
      (u j).val < 2^(L j) := by
    have hum : (∑ i, (u i).val)<n ∧
        (∑ i, (u i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hu
    have := Finset.single_le_sum (f := fun i ↦ (u i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  by_cases ho : ∃ a, 2^(L a)-1 < (w a).val
  · obtain ⟨a,ha⟩ := ho
    right
    refine ⟨a,?_,ha⟩
    intro hh
    subst a
    have := hsmall w hw
    omega
  · left
    apply forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain w v hw hv
    intro i
    have hwlow : ¬ 2^(L i)-1 < (w i).val := fun hi ↦ ho ⟨i,hi⟩
    have hvlow : ¬ 2^(L i)-1 < (v i).val := by
      by_cases hij : i=j
      · subst i; have := hsmall v hv; omega
      · rw [hvz i hij]; omega
    exact iff_of_false hwlow hvlow

/-- Below the sharp bound, a genuine even-axis case is exactly its
axis base and one incompatible overflow, with second entries on every arm.
The complete family and incompatibility are derived, not supplied. -/
theorem even_axis_subglobal_profile_pair
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    (∀ i, 2 ≤ L i) ∧ ∃ w a, a ≠ j ∧ forestCollisionProfiles n L x={v,w} ∧
      2^(L a)-1 < (w a).val ∧ ¬ ∀ i, i ≠ j → Even (w i).val := by
  classical
  have hL2 : ∀ i, 2 ≤ L i := by
    intro i
    by_contra hi
    have hi1 : L i=1 := by have := hL i; omega
    by_cases hij : i=j
    · subst i
      rw [hi1] at hwidth
      norm_num at hwidth
      omega
    · have hh := (even_axis_base_length_one_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
        j i hij hi1 hwidth hj hother v hv hvz).2
      omega
  have hinc : ∀ w ∈ forestCollisionProfiles n L x, ∀ a, 2^(L a)-1 < (w a).val →
      ¬ ∀ i, i ≠ j → Even (w i).val := by
    intro w hw a ha hc
    have hh := (even_axis_base_compatible_overflow_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
      j hwidth hj hother w v hw hv hc a ha hvz).2
    omega
  have hsome : ∃ w ∈ forestCollisionProfiles n L x, w ≠ v := by
    by_contra hh
    push Not at hh
    have ha : ∃ a, a ≠ j := by
      have hc : (Finset.univ.erase j).card=2 := by simp [hr]
      obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase j).card)
      exact ⟨a,(Finset.mem_erase.mp ha).1⟩
    obtain ⟨a,haj⟩ := ha
    have hb := binary_bound_of_even_axis_profile_family (show 2 ∣ N from ⟨M,hN⟩) L hL g hg E x b hchain
      ⟨a,hother a haj⟩ j hj (by intro w hw i hij; rw [hh w hw]; exact hvz i hij)
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    omega
  obtain ⟨w,hw,hwne⟩ := hsome
  obtain hh | ⟨a,haj,ha⟩ := profile_eq_axis_base_or_companion_overflow L hL hwide g hg E x b hchain
    j (by omega) v w hv hw hvz
  · exact False.elim (hwne hh)
  have hfamily : forestCollisionProfiles n L x={v,w} := by
    ext u
    constructor
    · intro hu
      obtain huv | ⟨k,hkj,hk⟩ := profile_eq_axis_base_or_companion_overflow L hL hwide g hg E x b hchain
        j (by omega) v u hv hu hvz
      · simp [huv]
      by_cases hka : k=a
      · subst k
        have heq := forestCollisionProfiles_eq_of_overflow_on_same_arm hr L hL hwide g hg E x b hchain
          u w hu hw a hk ha
        simp [heq]
      · exact False.elim (no_two_incompatible_overflows_with_even_axis_base (show 2 ∣ N from ⟨M,hN⟩)
          hr L hL2 hwide g hg E x b hchain j a k haj hkj hka (by omega) hj hother v w u hv hw hu hvz
          ha hk (hinc w hw a ha) (hinc u hu k hk))
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hv
      · exact (Finset.mem_singleton.mp hu) ▸ hw
  exact ⟨hL2,w,a,haj,hfamily,ha,hinc w hw a ha⟩

/-- Half-shaped companion sides give exactly one quarter of the
companion box for each point of the dominant height. -/
theorem half_profile_lowerBox_card
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i) (hsize : (∑ i, L i)=n)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hwj : (w j).val < 2^(L j))
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1)) :
    (forestProfileLowerBox L w).card=((w j).val+1)*2^(n-L j-2) := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsplit : L j+L a+L k=n := by
    rw [hset] at hsize
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hsize
  have hpow : ∀ i, 2*2^(L i-1)=2^(L i) := by
    intro i
    rw [← pow_succ',Nat.sub_add_cancel (by have := hL i; omega : 1 ≤ L i)]
  have hsj : min ((w j).val+1) (2*(2^(L j)-1)+1-(w j).val)=(w j).val+1 := by
    omega
  have hsa : min ((w a).val+1) (2*(2^(L a)-1)+1-(w a).val)=2^(L a-1) := by
    have := hpow a
    have := Nat.two_pow_pos (L a-1)
    omega
  have hsk : min ((w k).val+1) (2*(2^(L k)-1)+1-(w k).val)=2^(L k-1) := by
    have := hpow k
    have := Nat.two_pow_pos (L k-1)
    omega
  rw [forestProfileLowerBox_card,hset]
  simp only [Finset.prod_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
    Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.prod_singleton,hsj,hsa,hsk]
  rw [← pow_add]
  congr 2
  have := hL a
  have := hL k
  omega

/-- The complete axis-base/incompatible-overflow pair pays only the
half rectangle's volume: the even axis base cancels out of odd packing. -/
theorem even_axis_half_profile_pair_gap
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hwidth : n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (ha : 2^(L a)-1 < (w a).val) (hinc : ¬ ∀ i, i ≠ j → Even (w i).val)
    (hfamily : forestCollisionProfiles n L x={v,w}) :
    2^n ≤ N+((w j).val+1)*2^(n-L j-2) := by
  classical
  have hpos : ∀ i, 0 < L i := fun i ↦ by have := hL i; omega
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hsmall (u : ∀ i, Fin (2*(2^(L i)-1)+1)) (hu : u ∈ forestCollisionProfiles n L x) :
      (∑ i, (u i).val)<n ∧ (u j).val < 2^(L j) := by
    have hum : (∑ i, (u i).val)<n ∧
        (∑ i, (u i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hu
    have := Finset.single_le_sum (f := fun i ↦ (u i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hvw : v ≠ w := by
    intro hh
    have hvaz := hvz a haj
    rw [hh] at hvaz
    omega
  have hk : ∃ k, k ≠ j ∧ k ≠ a := by
    have hc : ((Finset.univ.erase j).erase a).card=1 := by simp [hr,haj]
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase j).erase a).card)
    exact ⟨k,(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,(Finset.mem_erase.mp hk).1⟩
  obtain ⟨k,hkj,hka⟩ := hk
  obtain ⟨hwa,hwk,_⟩ := even_axis_incompatible_overflow_half_shape hN hr L hL hwide g hg E x b hchain
    j a k haj hkj hka hwidth hj hother v w hv hw hvz ha hinc
  have hwcard := half_profile_lowerBox_card hr L hL hsize j a k haj hkj hka w (hsmall w hw).2 hwa hwk
  have hvcard := forestProfileLowerBox_card_of_axis L j v (hsmall v hv).2 hvz
  have hvo : ∀ i, ¬ 2^(L i)-1 < (v i).val := by
    intro i
    by_cases hij : i=j
    · subst i; have := (hsmall v hv).2; omega
    · rw [hvz i hij]; omega
  have hvbias : forestProfileParityBias L x v=((v j).val+1 : ℕ) := by
    have hh := profile_bias_eq_signed_height_of_unique_even_seed L hpos x j hj hother hwidth v
      (hsmall v hv).1 (by intro i hij; rw [hvz i hij]; exact Even.zero)
    simpa only [hvo,Finset.filter_false,Finset.card_empty,pow_zero,one_mul,Nat.cast_add,Nat.cast_one] using hh
  have hwzero : forestProfileParityBias L x w=0 := by
    have hex := hinc
    push Not at hex
    obtain ⟨i,hij,hi⟩ := hex
    exact profile_parity_bias_eq_zero_of_odd_coordinate L x w i (hother i hij) (Nat.not_even_iff_odd.mp hi)
  have hh := explicit_profile_bias_card_bound hN L hpos g hg E x b hchain ⟨a,hother a haj⟩
  simp only [hfamily,Finset.sum_pair hvw,hvbias,hwzero,add_zero,← forestProfileLowerBox_card,hvcard,hwcard,
    Nat.cast_add] at hh
  simp only [Nat.cast_one] at hh
  have hnonneg : (0 : ℤ) ≤ ((v j).val : ℤ)+1 := by positivity
  rw [abs_of_nonneg hnonneg] at hh
  exact_mod_cast (show ((2^n : ℕ) : ℤ) ≤ (N : ℤ)+(((w j).val+1)*2^(n-L j-2) : ℕ) by omega)

/-- A subglobal even-axis case extracts its unique incompatible
half rectangle together with a charge exceeding the allowed deficit. -/
theorem even_axis_subglobal_profile_pair_large_charge
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    (∀ i, 2 ≤ L i) ∧ ∃ w a, a ≠ j ∧ forestCollisionProfiles n L x={v,w} ∧
      2^(L a)-1 < (w a).val ∧ (¬ ∀ i, i ≠ j → Even (w i).val) ∧
      2^(Nat.log 2 n) < ((w j).val+1)*2^(n-L j-2) := by
  classical
  obtain ⟨hL2,w,a,haj,hfamily,ha,hinc⟩ := even_axis_subglobal_profile_pair hn hN hr L hL hwide
    g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j a haj (by omega) hj hother v w hv hw hvz ha hinc hfamily
  refine ⟨hL2,w,a,haj,hfamily,ha,hinc,?_⟩
  unfold globalBound at hsub
  omega

/-- Bounding the actual overflow half-rectangle charges closes every
genuine even-axis family in the established range, with family exhaustion
and all short-arm and compatibility cases handled internally. -/
theorem even_axis_global_bound_of_small_half_profile_charges
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hcharge : ∀ w ∈ forestCollisionProfiles n L x, ∀ a, 2^(L a)-1 < (w a).val →
      ((w j).val+1)*2^(n-L j-2) ≤ 2^(Nat.log 2 n)) : globalBound n ≤ N := by
  by_contra hnN
  obtain ⟨_,w,a,_,hfamily,ha,_,hlarge⟩ := even_axis_subglobal_profile_pair_large_charge hn hN hr L hL hwide
    g hg E x b hchain hgen j hwidth hj hother v hv hvz (by omega)
  have hw : w ∈ forestCollisionProfiles n L x := by
    classical
    rw [hfamily]
    simp
  have hh := hcharge w hw a ha
  omega

end MinModulus
