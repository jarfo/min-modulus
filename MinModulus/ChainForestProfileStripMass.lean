import MinModulus.ChainForestProfileQuotientMass

/-! Exact zero-quotient counts for compatible overflow strips. Under the
existing dominance threshold, the full actual gcd removes one quotient
width from each strip's deficit charge. Singleton and several-strip
families are covered. The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Positive multiples of d below K are counted by floor((K-1)/d). -/
theorem card_positive_divisible_fin
    (K d : ℕ) (hK : 0 < K) :
    Nat.card {q : Fin K // 0 < q.val ∧ d ∣ q.val}=(K-1)/d := by
  classical
  let S := (Finset.Ioc 0 (K-1)).filter (fun q ↦ d ∣ q)
  let E : {q : Fin K // 0 < q.val ∧ d ∣ q.val} ≃ S :=
    { toFun := fun q ↦ ⟨q.val.val,by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Ioc.mpr ⟨q.property.1,by have := q.val.isLt; omega⟩,q.property.2⟩⟩
      invFun := fun q ↦ ⟨⟨q.val,by
        have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.property).1).2
        omega⟩,⟨(Finset.mem_Ioc.mp (Finset.mem_filter.mp q.property).1).1,(Finset.mem_filter.mp q.property).2⟩⟩
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }
  have hh := Nat.card_congr E
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,S,Nat.Ioc_filter_dvd_card_eq_div] using hh

/-- A strip contains exactly h*floor((K_a-1)/d) points whose overflowing
coordinate is divisible by d. This counts the complete lower rectangle. -/
theorem forest_strip_divisible_axis_card
    {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ)
    (j a : β) (haj : a ≠ j)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hj : (w j).val < 2^(L j)) (ha : (w a).val=2^(L a))
    (hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0) (d : ℕ) :
    ((forestProfileLowerBox L w).filter (fun p ↦ d ∣ (p a).val)).card=
      ((w j).val+1)*((2^(L a)-1)/d) := by
  classical
  let D := {q : Fin (2^(L a)) // 0 < q.val ∧ d ∣ q.val}
  let T := {q : (∀ i, Fin (2^(L i))) // q ∈ forestProfileLowerBox L w ∧ d ∣ (q a).val}
  let P : Fin ((w j).val+1) × D → (∀ i, Fin (2^(L i))) := fun p i ↦
    ⟨if i=j then p.1.val else if i=a then p.2.val.val else 0,by
      split_ifs with hij hia
      · subst i; have := p.1.isLt; omega
      · subst i; exact p.2.val.isLt
      · exact Nat.two_pow_pos _⟩
  have hPj : ∀ p, (P p j).val=p.1.val := by intro p; simp [P]
  have hPa : ∀ p, (P p a).val=p.2.val.val := by intro p; simp [P,haj]
  have hPz : ∀ p i, i ≠ j → i ≠ a → (P p i).val=0 := by intro p i hij hia; simp [P,hij,hia]
  have hmem : ∀ p, P p ∈ forestProfileLowerBox L w ∧ d ∣ (P p a).val := by
    intro p
    rw [forestProfileLowerBox_eq_strip L j a haj w hj ha hz,hPj,hPa]
    exact ⟨⟨by have := p.1.isLt; omega,by have := p.2.property.1; omega,hPz p⟩,p.2.property.2⟩
  let F : Fin ((w j).val+1) × D → T := fun p ↦ ⟨P p,hmem p⟩
  have hi : Function.Injective F := by
    intro p q he
    have hh : P p=P q := congrArg Subtype.val he
    apply Prod.ext
    · apply Fin.ext
      have hj' := congrArg (fun v ↦ (v j).val) hh
      simpa only [hPj] using hj'
    · apply Subtype.ext
      apply Fin.ext
      have ha' := congrArg (fun v ↦ (v a).val) hh
      simpa only [hPa] using ha'
  have hs : Function.Surjective F := by
    intro q
    obtain ⟨hqj,hqa,hqz⟩ := (forestProfileLowerBox_eq_strip L j a haj w hj ha hz q.val).mp q.property.1
    refine ⟨(⟨(q.val j).val,by omega⟩,⟨q.val a,⟨by omega,q.property.2⟩⟩),?_⟩
    apply Subtype.ext
    funext i
    apply Fin.ext
    dsimp only [F,P]
    split_ifs with hij hia
    · subst i; rfl
    · subst i; rfl
    · exact (hqz i hij hia).symm
  have hT : Fintype.card T=((forestProfileLowerBox L w).filter (fun p ↦ d ∣ (p a).val)).card := by
    simp only [T,Fintype.card_subtype]
    congr 1
    ext p
    simp
  have hD : Fintype.card D=(2^(L a)-1)/d := by
    simpa only [Nat.card_eq_fintype_card,D] using card_positive_divisible_fin (2^(L a)) d (Nat.two_pow_pos _)
  have hh := Fintype.card_congr (Equiv.ofBijective F ⟨hi,hs⟩)
  simpa only [hT,hD,Fintype.card_prod,Fintype.card_fin] using hh.symm

/-- If the dominant seed projects to zero and the overflow seed to a
unit, a strip's zero-class points are exactly the positive multiples
of the quotient modulus along its overflowing axis. -/
theorem forest_strip_zero_projection_card
    {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (x : β → G) {d : ℕ}
    (π : G →+ ZMod d) (j a : β) (haj : a ≠ j)
    (hx : π (x j)=0) (hu : IsUnit (π (x a)))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hj : (w j).val < 2^(L j)) (ha : (w a).val=2^(L a))
    (hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0) :
    ((forestProfileLowerBox L w).filter (fun p ↦ π (∑ i, (p i).val • x i)=0)).card=
      ((w j).val+1)*((2^(L a)-1)/d) := by
  classical
  have heq : (forestProfileLowerBox L w).filter (fun p ↦ π (∑ i, (p i).val • x i)=0)=
      (forestProfileLowerBox L w).filter (fun p ↦ d ∣ (p a).val) := by
    ext p
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hp
    obtain ⟨_,_,hpz⟩ := (forestProfileLowerBox_eq_strip L j a haj w hj ha hz p).mp hp
    have heval : π (∑ i, (p i).val • x i)=(p a).val • π (x a) := by
      rw [map_sum]
      simp only [map_nsmul]
      apply Finset.sum_eq_single a
      · intro i _ hia
        by_cases hij : i=j
        · subst i; rw [hx,nsmul_zero]
        · rw [hpz i hij hia,zero_nsmul]
      · simp
    rw [heval,nsmul_eq_mul,hu.mul_left_eq_zero,ZMod.natCast_eq_zero_iff]
  rw [heq]
  exact forest_strip_divisible_axis_card L j a haj w hj ha hz d

/-- Exact zero-class mass of ANY compatible actual overflow profile.
The dominant index and unit companion projection are derived from validity. -/
theorem compatible_overflow_zero_residue_card
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    ((forestProfileLowerBox L w).filter (fun p ↦
      ((∑ i, (p i).val • x i).val : ZMod (N.gcd (x j).val))=0)).card=
      ((w j).val+1)*((2^(L a)-1)/(N.gcd (x j).val)) := by
  classical
  obtain ⟨e,_,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
  let d := N.gcd (x j).val
  letI : NeZero d := ⟨by dsimp only [d]; rw [hgcd]; positivity⟩
  have hdiv : d ∣ N := Nat.gcd_dvd_left _ _
  let π : ZMod N →+ ZMod d := (ZMod.castHom hdiv (ZMod d)).toAddMonoidHom
  have hπval : ∀ z : ZMod N, π z=(z.val : ZMod d) := by
    intro z
    change (z.cast : ZMod d)=(z.val : ZMod d)
    exact ZMod.cast_eq_val z
  have hx : π (x j)=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff]
    exact Nat.gcd_dvd_right _ _
  have hwidth : n ≤ 2^(L j) := by
    have hh : n ≤ n*(2^(n-L j)+1) := by nlinarith [Nat.two_pow_pos (n-L j)]
    omega
  obtain ⟨haj,hwa,hz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hcompat a ha
  have hu : IsUnit (π (x a)) := by
    rw [hπval,ZMod.isUnit_iff_coprime]
    dsimp only [d]
    rw [hgcd]
    exact (hodd a haj).coprime_two_right.pow_right e
  have hwj : (w j).val < 2^(L j) := by
    have hmem : (∑ i, (w i).val)<n ∧
        (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
    have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcount := forest_strip_zero_projection_card L x π j a haj hx hu w hwj hwa hz
  simpa only [hπval,d] using hcount

/-- The zero dominant-quotient class gives the exact rounded strip
bound. This improves the parity charge to the actual dominant index. -/
theorem singleton_compatible_overflow_quotient_gap_bound
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hsingle : forestCollisionProfiles n L x={w})
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    2^n ≤ N+N.gcd (x j).val*(((w j).val+1)*((2^(L a)-1)/(N.gcd (x j).val))) := by
  classical
  by_cases hsub : N < 2^n
  · have hw : w ∈ forestCollisionProfiles n L x := by rw [hsingle]; exact Finset.mem_singleton_self _
    have hcount := compatible_overflow_zero_residue_card hr L hL g hg E x b hchain hsub j hlarge hodd w hw hcompat a ha
    have hh := dominant_gcd_profile_residue_mass_card_bound L hL g hg E x b hchain j hlarge 0
    simpa only [forestProfileResidueMass,hsingle,Finset.sum_singleton,hcount] using hh
  · omega

/-- Rounding a dyadic strip width to multiples of a dyadic quotient
removes exactly one quotient width, with natural subtraction below it. -/
theorem dyadic_strip_rounding (L e : ℕ) :
    2^e*((2^L-1)/2^e)=2^L-2^e := by
  by_cases he : e ≤ L
  · have hk : 2^L=2^e*2^(L-e) := by rw [← pow_add,Nat.add_sub_of_le he]
    rw [hk]
    have hd := Nat.mul_sub_div 0 (2^e) (2^(L-e)) (by positivity)
    simp only [zero_add,Nat.zero_div,zero_add] at hd
    rw [hd,Nat.mul_sub_left_distrib,mul_one]
  · have hk : (2 : ℕ)^L < 2^e := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
    have hp := Nat.two_pow_pos L
    rw [Nat.div_eq_of_lt (by omega : 2^L-1 < 2^e),mul_zero,Nat.sub_eq_zero_of_le (by omega)]

/-- A singleton compatible strip pays at most (K_a-d)*h, where d is
the ACTUAL dominant gcd. This is the full quotient correction, including
the zero-deficit case K_a<=d. -/
theorem singleton_compatible_overflow_index_charge_bound
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hsingle : forestCollisionProfiles n L x={w})
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    2^n ≤ N+(2^(L a)-N.gcd (x j).val)*((w j).val+1) := by
  by_cases hsub : N < 2^n
  · obtain ⟨e,_,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
    have hh := singleton_compatible_overflow_quotient_gap_bound hr L hL g hg E x b hchain j hlarge hodd w hsingle hcompat a ha
    have hround : N.gcd (x j).val*((2^(L a)-1)/N.gcd (x j).val)=2^(L a)-N.gcd (x j).val := by
      rw [hgcd]
      exact dyadic_strip_rounding (L a) e
    rwa [mul_left_comm,hround,mul_comm ((w j).val+1)] at hh
  · omega

/-- For an entire family of compatible overflow strips, the deficit is
charged by (K_a-d)*h on each actual overflowing arm. Several strips are
included, and arms no wider than the index contribute zero. -/
theorem compatible_overflow_family_index_charge_bound
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val)
    (hprofiles : ∀ w ∈ forestCollisionProfiles n L x,
      (∀ i, i ≠ j → Even (w i).val) ∧ ∃ a, 2^(L a)-1 < (w a).val) :
    2^n ≤ N+∑ w ∈ forestCollisionProfiles n L x, ∑ a,
      if 2^(L a)-1 < (w a).val then (2^(L a)-N.gcd (x j).val)*((w j).val+1) else 0 := by
  classical
  by_cases hsub : N < 2^n
  · obtain ⟨e,_,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain L hL g hg E x b hchain hsub j hlarge
    have hh := dominant_gcd_profile_residue_mass_card_bound L hL g hg E x b hchain j hlarge 0
    have heq : N.gcd (x j).val*forestProfileResidueMass n L x (N.gcd (x j).val) 0=
        ∑ w ∈ forestCollisionProfiles n L x, ∑ a,
          if 2^(L a)-1 < (w a).val then (2^(L a)-N.gcd (x j).val)*((w j).val+1) else 0 := by
      rw [forestProfileResidueMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hcompat,a,ha⟩ := hprofiles w hw
      have hmem : (∑ i, (w i).val)<n ∧
          (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
        simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
      have hle := three_chain_profile_overflow_card_le_one hr L hL g hg E x b hchain
        (fun i ↦ (w i).val) (fun i ↦ by have := (w i).isLt; omega) hmem.1 hmem.2
      have hno : ∀ i, i ≠ a → ¬ 2^(L i)-1 < (w i).val := by
        intro i hia hi
        apply hia
        exact Finset.card_le_one.mp hle i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
          a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
      have hinner : (∑ i, if 2^(L i)-1 < (w i).val then
          (2^(L i)-N.gcd (x j).val)*((w j).val+1) else 0)=
            (2^(L a)-N.gcd (x j).val)*((w j).val+1) := by
        rw [Finset.sum_eq_single a]
        · rw [if_pos ha]
        · intro i _ hia; rw [if_neg (hno i hia)]
        · simp
      rw [hinner,compatible_overflow_zero_residue_card hr L hL g hg E x b hchain hsub j hlarge hodd w hw hcompat a ha]
      have hround : N.gcd (x j).val*((2^(L a)-1)/N.gcd (x j).val)=2^(L a)-N.gcd (x j).val := by
        rw [hgcd]
        exact dyadic_strip_rounding (L a) e
      rw [mul_left_comm,hround,mul_comm]
    rwa [heq] at hh
  · omega

end MinModulus
