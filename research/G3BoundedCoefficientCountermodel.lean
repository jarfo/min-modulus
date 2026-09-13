import research.G3BalancedCountermodel

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- At a binary power-gap modulus, every rival to the all-ones multiset
has the single low ordinary value `2^s-1`. Positive wraps need too many coins. -/
theorem binary_power_gap_multiset_classification
    {n s : ℕ} (hs : s < n) (k : ℕ → ℕ) (hd : dsum n k=n)
    (hmod : val n k ≡ 2^n-1 [MOD 2^n-2^s]) :
    (∀ i < n, k i=1) ∨ val n k=2^s-1 := by
  let N := (2:ℕ)^n-2^s
  have hp : 2^s < (2:ℕ)^n := Nat.pow_lt_pow_right (by decide) hs
  have hhalf : 2*2^s ≤ (2:ℕ)^n := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show s+1 ≤ n by omega)
    simpa only [pow_succ'] using hh
  have hN : 0 < N := by dsimp [N]; omega
  have h1 : 1 ≤ (2:ℕ)^s := Nat.one_le_two_pow
  change val n k ≡ 2^n-1 [MOD N] at hmod
  rcases lt_trichotomy (val n k) (2^n-1) with hlt | heq | hgt
  · right
    have hdvd : N ∣ 2^n-1-val n k :=
      (Nat.modEq_iff_dvd' (by omega)).mp hmod
    obtain ⟨j,hj⟩ := hdvd
    have hjpos : 0 < j := by
      by_contra hh
      have : j=0 := by omega
      simp only [this,mul_zero] at hj
      omega
    have hjone : j=1 := by
      by_contra hh
      have hjtwo : 2 ≤ j := by omega
      have hm := Nat.mul_le_mul_left N hjtwo
      dsimp [N] at hm hj
      omega
    simp only [hjone,mul_one] at hj
    dsimp [N] at hj
    omega
  · exact Or.inl (ones_unique n k heq hd)
  · exfalso
    have hdvd : N ∣ val n k-(2^n-1) :=
      (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    obtain ⟨j,hj⟩ := hdvd
    have hjeq : val n k=2^n-1+j*N := by
      rw [Nat.mul_comm] at hj
      omega
    have hjpos : 0 < j := by
      by_contra hh
      have : j=0 := by omega
      simp only [this,zero_mul,add_zero] at hjeq
      omega
    have hw : n-1+1=n := by omega
    have hgd := gmin_le_dsum (n-1) k
    rw [hw,hd] at hgd
    have hNt : N+2^s=2^(n-1+1) := by rw [hw]; dsimp [N]; omega
    have hslack := slack (by omega : s ≤ n-1) hNt j
    rw [hw,← hjeq] at hslack
    omega

/-- A low binary value is supported below the gap exponent. -/
theorem binary_low_value_forces_low_support
    {n s : ℕ} (k : ℕ → ℕ) (hv : val n k=2^s-1) :
    ∀ i < n, s ≤ i → k i=0 := by
  intro i hi hsi
  have hterm : k i*2^i ≤ val n k := by
    unfold val
    exact Finset.single_le_sum (f := fun j ↦ k j*2^j)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hi)
  have hp : (2:ℕ)^s ≤ 2^i := Nat.pow_le_pow_right (by decide) hsi
  have h1 : 1 ≤ (2:ℕ)^s := Nat.one_le_two_pow
  by_contra hh
  have hk : 1 ≤ k i := by omega
  have hm := Nat.mul_le_mul_right ((2:ℕ)^i) hk
  simp only [one_mul] at hm
  omega

/-- A rival bounded by C in each coordinate needs at most C*s coins,
since it must be supported on the s low binary positions. -/
theorem binary_power_gap_bounded_multiset_unique
    {n s C : ℕ} (hs : s < n) (hlarge : C*s < n)
    (k : ℕ → ℕ) (hcap : ∀ i < n, k i ≤ C) (hd : dsum n k=n)
    (hmod : val n k ≡ 2^n-1 [MOD 2^n-2^s]) : ∀ i < n, k i=1 := by
  rcases binary_power_gap_multiset_classification hs k hd hmod with hone | hv
  · exact hone
  · exfalso
    have hlow := binary_low_value_forces_low_support k hv
    have hds : dsum n k=dsum s k := by
      unfold dsum
      exact (Finset.sum_subset (Finset.range_subset_range.mpr hs.le)
        (fun i hi hni ↦ hlow i (Finset.mem_range.mp hi)
          (by simpa only [Finset.mem_range,not_lt] using hni))).symm
    have hbound : dsum s k ≤ s*C := by
      unfold dsum
      calc
        (∑ i ∈ range s, k i) ≤ ∑ i ∈ range s, C :=
          Finset.sum_le_sum (fun i hi ↦ hcap i (lt_trans (Finset.mem_range.mp hi) hs))
        _ = s*C := by simp
    rw [Nat.mul_comm] at hbound
    omega

/-- The binary tuple passes every admissible zero-relation test whose
positive coefficients are below C, whenever n > C*s. -/
theorem binary_power_gap_bounded_zero_isolation
    {n s C : ℕ} (hs : s < n) (hlarge : C*s < n)
    (c : Fin n → ℤ) (hcap : ∀ i, -1 ≤ c i ∧ c i < C)
    (hsum : ∑ i, c i=0)
    (hweight : ∑ i, c i • (2 : ZMod (2^n-2^s))^i.val=0) : c=0 := by
  let k : ℕ → ℕ := fun i ↦ if hi : i<n then (c ⟨i,hi⟩+1).toNat else 0
  have hk (i : Fin n) : (k i.val : ℤ)=c i+1 := by
    simp only [k,dif_pos i.isLt]
    change ((c i+1).toNat : ℤ)=c i+1
    exact Int.toNat_of_nonneg (by have := (hcap i).1; omega)
  have hkcap : ∀ i < n, k i ≤ C := by
    intro i hi
    have hh := hk ⟨i,hi⟩
    change (k i : ℤ)=c ⟨i,hi⟩+1 at hh
    have hu := (hcap ⟨i,hi⟩).2
    omega
  have hd : dsum n k=n := by
    unfold dsum
    rw [← Fin.sum_univ_eq_sum_range]
    have hh : (∑ i : Fin n, (k i.val : ℤ))=n := by
      simp_rw [hk]
      simp [Finset.sum_add_distrib,hsum]
    exact_mod_cast hh
  have hmod : val n k ≡ 2^n-1 [MOD 2^n-2^s] := by
    have hw : (∑ i : Fin n, (k i.val : ℤ) • (2 : ZMod (2^n-2^s))^i.val)=
        ∑ i : Fin n, (2 : ZMod (2^n-2^s))^i.val := by
      simp_rw [hk,add_smul,one_zsmul]
      rw [Finset.sum_add_distrib,hweight,zero_add]
    have hval : ((val n k : ℕ) : ZMod (2^n-2^s))=
        ((2^n-1 : ℕ) : ZMod (2^n-2^s)) := by
      unfold val
      rw [← sum_two_pow n,← Fin.sum_univ_eq_sum_range,← Fin.sum_univ_eq_sum_range]
      push_cast
      simpa only [zsmul_eq_mul,Int.cast_natCast] using hw
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hval
  have hone := binary_power_gap_bounded_multiset_unique hs hlarge k hkcap hd hmod
  funext i
  have hh := hk i
  have ho := hone i.val i.isLt
  simp only [Pi.zero_apply]
  omega

/-- Every fixed coefficient cap is eventually smaller than dimension
divided by the number of low binary positions. The threshold is explicit. -/
theorem coefficient_cap_log_bound
    (C n : ℕ) (hn : 2^(C+4) ≤ n) : C*(Nat.log 2 n+1) < n := by
  have hlog : C+4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hsquare : ∀ L : ℕ, 4 ≤ L → L^2 ≤ 2^L := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ L hL ih =>
      have hm := Nat.mul_le_mul_right L (show 3 ≤ L by omega)
      calc
        (L+1)^2 ≤ 2*(L^2) := by nlinarith
        _ ≤ 2*2^L := Nat.mul_le_mul_left 2 ih
        _ = 2^(L+1) := (pow_succ' 2 L).symm
  have hm := Nat.mul_le_mul_right (Nat.log 2 n+1)
    (show C+1 ≤ Nat.log 2 n by omega)
  have hstrict : C*(Nat.log 2 n+1) < (Nat.log 2 n)^2 := by nlinarith
  exact lt_of_lt_of_le hstrict ((hsquare _ (by omega)).trans
    (Nat.pow_log_le_self 2 (by have := Nat.one_le_two_pow (n := C+4); omega)))

/-- The cap needed for differences of unit witnesses is already ineffective
from dimension sixteen onward. -/
theorem three_mul_log_add_one_lt_from_sixteen
    (n : ℕ) (hn : 16 ≤ n) : 3*(Nat.log 2 n+1) < n := by
  have hlog : 4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
  have hpow : ∀ L : ℕ, 4 ≤ L → 3*(L+1) < 2^L := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ L hL ih => rw [pow_succ]; omega
  exact lt_of_lt_of_le (hpow _ hlog) (Nat.pow_log_le_self 2 (by omega))

/-- At the actual G3 modulus, bounded admissible isolation is still strictly
weaker than full validity, uniformly whenever the stated cap fits. -/
theorem exceptional_bounded_isolation_countermodel
    (C n : ℕ) (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (hlarge : C*(Nat.log 2 n+1) < n) :
    ∃ g : Fin n → ZMod (2*globalBound (n-1)), ¬ ValidTuple g ∧
      ∀ c : Fin n → ℤ, (∀ i, -1 ≤ c i ∧ c i < C) →
        (∑ i, c i)=0 → (∑ i, c i • g i)=0 → c=0 := by
  have hln := log_add_two_le n hn
  have hlog := log_pred_eq_log_of_not_pow n hn hnpow
  have hgap : 2*globalBound (n-1)=(2:ℕ)^n-2^(Nat.log 2 n+1) := by
    have hp : (2:ℕ)*2^(n-1)=2^n := by
      rw [← pow_succ']
      congr 1
      omega
    unfold globalBound
    rw [hlog,Nat.mul_sub,hp,← pow_succ']
  rw [hgap]
  refine ⟨fun i ↦ 2^i.val,binary_tuple_not_valid_of_large_power_gap (by omega)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n),?_⟩
  exact fun c hc hs hw ↦ binary_power_gap_bounded_zero_isolation (by omega) hlarge c hc hs hw

/-- Any fixed positive-coefficient cutoff misses invalid binary tuples
at all sufficiently large G3 exceptional moduli. -/
theorem exceptional_bounded_isolation_countermodel_eventually
    (C n : ℕ) (hn : 2^(C+4) ≤ n) (hnpow : 2^Nat.log 2 n ≠ n) :
    ∃ g : Fin n → ZMod (2*globalBound (n-1)), ¬ ValidTuple g ∧
      ∀ c : Fin n → ℤ, (∀ i, -1 ≤ c i ∧ c i < C) →
        (∑ i, c i)=0 → (∑ i, c i • g i)=0 → c=0 := by
  apply exceptional_bounded_isolation_countermodel C n _ hnpow (coefficient_cap_log_bound C n hn)
  have hp : (2:ℕ)^4 ≤ 2^(C+4) := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  omega

/-- The same-target unit-witness antichain argument uses only isolation
for coefficients in [-1,2], rather than full multiset validity. -/
theorem unit_witness_antichain_of_bounded_isolation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (hsep : ∀ c : Fin n → ℤ, (∀ i, -1 ≤ c i ∧ c i < 3) →
      (∑ i, c i)=0 → (∑ i, c i • g i)=0 → c=0)
    (h : G) (F : Finset (Fin n → ℤ))
    (hF : ∀ c ∈ F, Witness g h c) (hupper : ∀ c ∈ F, ∀ i, c i ≤ 1) :
    let negSupport := fun c : Fin n → ℤ ↦ Finset.univ.filter (fun i ↦ c i = -1)
    Set.InjOn negSupport F ∧
      IsAntichain (· ⊆ ·) (↑(F.image negSupport) : Set (Finset (Fin n))) := by
  classical
  dsimp only
  let negSupport := fun c : Fin n → ℤ ↦ Finset.univ.filter (fun i ↦ c i = -1)
  have heq c (hc : c ∈ F) d (hd : d ∈ F) (hs : negSupport c ⊆ negSupport d) : c=d := by
    apply sub_eq_zero.mp
    apply hsep (c-d)
    · intro i
      have hcl := (hF c hc).2.1 i
      have hdl := (hF d hd).2.1 i
      have hcu := hupper c hc i
      have hdu := hupper d hd i
      have hsub : c i= -1 → d i= -1 := by
        intro hi
        have hm : i ∈ negSupport c := by simp [negSupport,hi]
        simpa [negSupport] using hs hm
      simp only [Pi.sub_apply]
      omega
    · simp only [Pi.sub_apply,Finset.sum_sub_distrib,(hF c hc).2.2.1,
        (hF d hd).2.2.1,sub_self]
    · simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,(hF c hc).2.2.2,
        (hF d hd).2.2.2,sub_self]
  constructor
  · intro c hc d hd he
    exact heq c hc d hd (show negSupport c ⊆ negSupport d from
      (show negSupport c=negSupport d from he).subset)
  · intro S hS T hT hne hsub
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hT
    exact hne (congrArg negSupport (heq c hc d hd hsub))

/-- From dimension sixteen, an invalid tuple at every G3 modulus satisfies
all the same-target unit-witness antichain and Sperner restrictions. -/
theorem exceptional_antichain_countermodel
    (n : ℕ) (hn : 16 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n) :
    ∃ g : Fin n → ZMod (2*globalBound (n-1)), ¬ ValidTuple g ∧
      ∀ (h : ZMod (2*globalBound (n-1))) (F : Finset (Fin n → ℤ)),
        (∀ c ∈ F, Witness g h c) → (∀ c ∈ F, ∀ i, c i ≤ 1) →
        let negSupport := fun c : Fin n → ℤ ↦ Finset.univ.filter (fun i ↦ c i = -1)
        Set.InjOn negSupport F ∧
          IsAntichain (· ⊆ ·) (↑(F.image negSupport) : Set (Finset (Fin n))) ∧
            F.card ≤ n.choose (n/2) := by
  classical
  obtain ⟨g,hinvalid,hsep⟩ := exceptional_bounded_isolation_countermodel 3 n
    (by omega) hnpow (three_mul_log_add_one_lt_from_sixteen n hn)
  refine ⟨g,hinvalid,?_⟩
  intro h F hF hupper
  obtain ⟨hi,ha⟩ := unit_witness_antichain_of_bounded_isolation g hsep h F hF hupper
  refine ⟨hi,ha,?_⟩
  have hh := ha.sperner
  rw [Finset.card_image_iff.mpr hi] at hh
  simpa only [Fintype.card_fin] using hh

end MinModulus.Research
