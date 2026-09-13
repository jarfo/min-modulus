import MinModulus.G3ExceptionalStructure
import MinModulus.Descent
import Mathlib.Combinatorics.SetFamily.LYM

set_option autoImplicit false

/-! Equal-rank subset collisions yield reversible witnesses in small quotients. -/
namespace MinModulus.Research
open Finset

/-- Counting subsets by their cardinality and value forces a collision at one rank. -/
theorem exists_equal_card_subset_sum_collision
    {n : ℕ} {H : Type*} [AddCommMonoid H] [Fintype H]
    (g : Fin n → H) (hsmall : (n+1)*Fintype.card H < 2^n) :
    ∃ S T : Finset (Fin n), S ≠ T ∧ S.card = T.card ∧
      (∑ i ∈ S, g i) = ∑ i ∈ T, g i := by
  classical
  let f : Finset (Fin n) → Fin (n+1) × H := fun S ↦
    (⟨S.card,by have := Finset.card_le_univ S; simp only [Fintype.card_fin] at this; omega⟩,
      ∑ i ∈ S, g i)
  have hni : ¬ Function.Injective f := by
    intro hi
    have hh := Fintype.card_le_of_injective f hi
    simp only [Fintype.card_finset,Fintype.card_fin,Fintype.card_prod] at hh
    omega
  obtain ⟨S,T,he,hne⟩ := Function.not_injective_iff.mp hni
  exact ⟨S,T,hne,congrArg Fin.val (congrArg Prod.fst he),congrArg Prod.snd he⟩

/-- An equal-rank collision downstairs lifts to a witness with every coefficient
in {-1,0,1}; its value upstairs is nonzero and killed by the quotient map. -/
theorem exists_unit_kernel_witness_of_small_quotient
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (g : Fin n → G) (hg : ValidTuple g)
    (hsmall : (n+1)*Fintype.card H < 2^n) :
    ∃ h : G, ∃ c : Fin n → ℤ,
      h ≠ 0 ∧ f h = 0 ∧ Witness g h c ∧ (∀ i, c i ≤ 1) := by
  classical
  obtain ⟨S,T,hne,hcard,hvalue⟩ :=
    exists_equal_card_subset_sum_collision (fun i ↦ f (g i)) hsmall
  let c : Fin n → ℤ := fun i ↦ (if i ∈ S then 1 else 0)-(if i ∈ T then 1 else 0)
  have hcne : c ≠ 0 := by
    intro hc
    apply hne
    ext i
    have hi := congrFun hc i
    simp only [c,Pi.zero_apply] at hi
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    dsimp [c]
    split_ifs <;> omega
  have hupper : ∀ i, c i ≤ 1 := by
    intro i
    dsimp [c]
    split_ifs <;> omega
  have hsum : ∑ i, c i = 0 := by
    simp [c,Finset.sum_sub_distrib,hcard]
  let h := ∑ i, c i • g i
  have hw : Witness g h c := ⟨hcne,hfloor,hsum,rfl⟩
  have hnz : h ≠ 0 := by
    intro hz
    exact (validTuple_iff_no_zero_witness g).mp hg c (hz ▸ hw)
  refine ⟨h,c,hnz,?_,hw,hupper⟩
  have hweight : h = (∑ i ∈ S, g i) - ∑ i ∈ T, g i := by
    simp only [h,c,sub_smul,ite_smul,one_zsmul,zero_smul,
      Finset.sum_sub_distrib,Finset.sum_ite_mem,Finset.univ_inter]
  simp only [hweight,map_sub,map_sum,hvalue,sub_self]

/-- Unlike an anchor-heavy witness, a witness bounded above by one can be reversed. -/
theorem witness_neg_of_unit_coefficients
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    {h : G} {c : Fin n → ℤ} (hc : Witness g h c) (hupper : ∀ i, c i ≤ 1) :
    Witness g (-h) (-c) := by
  refine ⟨neg_ne_zero.mpr hc.1,?_,?_,?_⟩
  · intro i
    have := hupper i
    simp only [Pi.neg_apply]
    omega
  · simpa only [Pi.neg_apply,Finset.sum_neg_distrib,neg_zero] using congrArg Neg.neg hc.2.2.1
  · simpa only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib] using congrArg Neg.neg hc.2.2.2

/-- The Mersenne odd factor is too small even to separate subsets of each fixed rank. -/
theorem exceptional_odd_part_rank_count_lt (n : ℕ) (hn : 3 ≤ n) :
    (n+1)*(2^(n-Nat.log 2 n-1)-1) < 2^n := by
  have hLn := log_add_two_le n hn
  have hnK := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hprod : 2^(Nat.log 2 n+1)*2^(n-Nat.log 2 n-1) = (2:ℕ)^n := by
    rw [← pow_add]
    congr 1
    omega
  have hq : 2^(n-Nat.log 2 n-1)-1 < (2:ℕ)^(n-Nat.log 2 n-1) := by
    have : 0 < (2:ℕ)^(n-Nat.log 2 n-1) := by positivity
    omega
  calc
    (n+1)*(2^(n-Nat.log 2 n-1)-1) ≤
        2^(Nat.log 2 n+1)*(2^(n-Nat.log 2 n-1)-1) :=
      Nat.mul_le_mul_right _ (by omega)
    _ < 2^(Nat.log 2 n+1)*2^(n-Nat.log 2 n-1) :=
      Nat.mul_lt_mul_of_pos_left hq (by positivity)
    _ = 2^n := hprod

/-- Every hypothetical exceptional tuple has a reversible witness at a nonzero
kernel target. This is an existence restriction, not the G3 contradiction. -/
theorem exists_exceptional_reversible_kernel_witness
    (n : ℕ) (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g) :
    ∃ h : ZMod (2*globalBound (n-1)), ∃ c : Fin n → ℤ,
      h ≠ 0 ∧
      ZMod.castHom (odd_part_dvd_exceptional n hn hnpow)
        (ZMod (2^(n-Nat.log 2 n-1)-1)) h = 0 ∧
      Witness g h c ∧ Witness g (-h) (-c) ∧ (∀ i, -1 ≤ c i ∧ c i ≤ 1) := by
  have hexp := one_le_mersenne_exponent n hn
  have hqpos : 0 < 2^(n-Nat.log 2 n-1)-1 := by
    have hh : (2:ℕ)^1 ≤ 2^(n-Nat.log 2 n-1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    norm_num only [pow_one] at hh
    omega
  let : NeZero (2^(n-Nat.log 2 n-1)-1) := ⟨hqpos.ne'⟩
  let f := (ZMod.castHom (odd_part_dvd_exceptional n hn hnpow)
    (ZMod (2^(n-Nat.log 2 n-1)-1))).toAddMonoidHom
  obtain ⟨h,c,hnz,hker,hc,hupper⟩ := exists_unit_kernel_witness_of_small_quotient f g hg
    (by simpa only [ZMod.card] using exceptional_odd_part_rank_count_lt n hn)
  exact ⟨h,c,hnz,hker,hc,witness_neg_of_unit_coefficients g hc hupper,
    fun i ↦ ⟨hc.2.1 i,hupper i⟩⟩

/-- At a fixed target, nested negative supports determine the same fully light witness. -/
theorem same_target_unit_witness_eq_of_negative_support_subset
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    {h : G} {c d : Fin n → ℤ} (hc : Witness g h c) (hd : Witness g h d)
    (hcupper : ∀ i, c i ≤ 1) (hdupper : ∀ i, d i ≤ 1)
    (hsub : ∀ i, c i = -1 → d i = -1) : c=d := by
  by_contra hne
  apply (validTuple_iff_no_zero_witness g).mp hg (c-d)
  refine ⟨sub_ne_zero.mpr hne,?_,?_,?_⟩
  · intro i
    have hcl := hc.2.1 i
    have hdl := hd.2.1 i
    have hcu := hcupper i
    have hdu := hdupper i
    have hs := hsub i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hc.2.2.1,hd.2.2.1,sub_self]
  · simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,hc.2.2.2,hd.2.2.2,sub_self]

/-- Fully light witnesses at a fixed target form an antichain through their negative supports. -/
theorem same_target_unit_witness_family_antichain
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (h : G) (F : Finset (Fin n → ℤ))
    (hF : ∀ c ∈ F, Witness g h c) (hupper : ∀ c ∈ F, ∀ i, c i ≤ 1) :
    let negSupport := fun c : Fin n → ℤ ↦ Finset.univ.filter (fun i ↦ c i = -1)
    Set.InjOn negSupport F ∧
      IsAntichain (· ⊆ ·) (↑(F.image negSupport) : Set (Finset (Fin n))) := by
  classical
  dsimp only
  let negSupport := fun c : Fin n → ℤ ↦ Finset.univ.filter (fun i ↦ c i = -1)
  have heq c (hc : c ∈ F) d (hd : d ∈ F) (hs : negSupport c ⊆ negSupport d) : c=d := by
    apply same_target_unit_witness_eq_of_negative_support_subset g hg
      (hF c hc) (hF d hd) (hupper c hc) (hupper d hd)
    intro i hi
    have hm : i ∈ negSupport c := by simp [negSupport,hi]
    simpa [negSupport] using hs hm
  constructor
  · intro c hc d hd he
    exact heq c hc d hd (show negSupport c ⊆ negSupport d from (show negSupport c = negSupport d from he).subset)
  · intro S hS T hT hne hsub
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hT
    exact hne (congrArg negSupport (heq c hc d hd hsub))

/-- Sperner bounds fully light witnesses at one target by the middle binomial coefficient. -/
theorem same_target_unit_witness_family_card_le_middle_binomial
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (h : G) (F : Finset (Fin n → ℤ))
    (hF : ∀ c ∈ F, Witness g h c) (hupper : ∀ c ∈ F, ∀ i, c i ≤ 1) :
    F.card ≤ n.choose (n/2) := by
  classical
  obtain ⟨hi,ha⟩ := same_target_unit_witness_family_antichain g hg h F hF hupper
  have hh := ha.sperner
  rw [Finset.card_image_iff.mpr hi] at hh
  simpa only [Fintype.card_fin] using hh

end MinModulus.Research
