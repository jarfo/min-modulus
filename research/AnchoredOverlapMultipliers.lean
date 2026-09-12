import research.AnchoredPairLowerBound

/-! Multiplier relations controlling intersections of anchored cubes.
The relation-free hypothesis below is explicit and is not asserted for
all valid tuples. No odd-order assumption is needed for these implications. -/
namespace MinModulus.Research
open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

private theorem no_anchor_relation_of_sum_le_one (g : Fin n → G) (hg : ValidTuple g)
    (k : Fin n) (e : Fin n → ℤ) (hek : e k = 0) (hne : e ≠ 0)
    (hge : ∀ j, -1 ≤ e j) (hs : (∑ j, e j) ≤ 1)
    (hv : (∑ j, e j • (g j - g k)) = 0) : False := by
  let c : Fin n → ℤ := fun j ↦ e j - if j = k then ∑ i, e i else 0
  have hcne : c ≠ 0 := by
    intro hc
    apply hne
    funext j
    by_cases hj : j = k
    · simpa [hj] using hek
    · have h := congrFun hc j
      simpa [c,hj] using h
  have hcge (j : Fin n) : -1 ≤ c j := by
    by_cases hj : j = k
    · simp only [c,hj,hek,if_true,zero_sub]
      omega
    · simpa [c,hj] using hge j
  apply (validTuple_iff_no_zero_witness g).mp hg c
  refine ⟨hcne,hcge,?_,?_⟩
  · simp [c,Finset.sum_sub_distrib]
  · simpa [c,sub_smul,ite_smul,Finset.sum_sub_distrib,smul_sub,
      ← Finset.sum_smul] using hv

/-- Dissociation at an arbitrary anchor forbids every nonzero ternary relation. -/
theorem ternary_anchor_relation_eq_zero (g : Fin n → G) (hg : ValidTuple g)
    (k : Fin n) (e : Fin n → ℤ) (hek : e k = 0)
    (hb : ∀ j, -1 ≤ e j ∧ e j ≤ 1)
    (hv : (∑ j, e j • (g j - g k)) = 0) : e = 0 := by
  by_contra hne
  by_cases hs : (∑ j, e j) ≤ 1
  · exact no_anchor_relation_of_sum_le_one g hg k e hek hne (fun j ↦ (hb j).1) hs hv
  · apply no_anchor_relation_of_sum_le_one g hg k (-e)
    · simp [hek]
    · simpa only [neg_ne_zero] using hne
    · intro j
      have := (hb j).2
      change -1 ≤ -e j
      omega
    · simp only [Pi.neg_apply,Finset.sum_neg_distrib]
      omega
    · simpa only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,hv,neg_zero]

/-- In particular, the multiplier-one search has no solutions for a valid tuple. -/
theorem anchored_multiplier_one_relation_impossible (g : Fin n → G) (hg : ValidTuple g)
    (k l : Fin n) (e : Fin n → ℤ) (hek : e k = 0) (hel : e l = 1)
    (hb : ∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) :
    (∑ j, e j • (g j - g k)) ≠ 0 := by
  intro hv
  have he := ternary_anchor_relation_eq_zero g hg k e hek (by
    intro j
    by_cases hjk : j = k
    · simp [hjk,hek]
    by_cases hjl : j = l
    · simp [hjl,hel]
    exact hb j hjk hjl) hv
  have hz : e l = 0 := congrFun he l
  omega

def anchoredOverlapCoefficients (S T : Finset (Fin n)) (k l : Fin n) (j : Fin n) : ℤ :=
  (if j ∈ S then 1 else 0) - (if j ∈ T then 1 else 0) -
    (if j = k then (S.card : ℤ) else 0) + (if j = l then (T.card : ℤ) else 0)

theorem anchoredOverlapCoefficients_sum (S T : Finset (Fin n)) (k l : Fin n) :
    (∑ j, anchoredOverlapCoefficients S T k l j) = 0 := by
  simp [anchoredOverlapCoefficients, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem anchoredOverlapCoefficients_value (g : Fin n → G)
    (S T : Finset (Fin n)) (k l : Fin n) :
    (∑ j, anchoredOverlapCoefficients S T k l j • g j) =
      (∑ j ∈ S, (g j - g k)) - ∑ j ∈ T, (g j - g l) := by
  simp only [anchoredOverlapCoefficients, add_smul, sub_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, natCast_zsmul,
    Finset.sum_const]
  abel

theorem anchoredOverlapCoefficients_left (S T : Finset (Fin n)) (k l : Fin n)
    (hkl : k ≠ l) (hk : k ∉ S) :
    anchoredOverlapCoefficients S T k l k =
      -((S.card + if k ∈ T then 1 else 0 : ℕ) : ℤ) := by
  simp only [anchoredOverlapCoefficients, hk, if_false, hkl]
  split_ifs <;> push_cast <;> omega

theorem anchoredOverlapCoefficients_right (S T : Finset (Fin n)) (k l : Fin n)
    (hkl : k ≠ l) (hl : l ∉ T) :
    anchoredOverlapCoefficients S T k l l =
      ((T.card + if l ∈ S then 1 else 0 : ℕ) : ℤ) := by
  simp only [anchoredOverlapCoefficients, hl, if_false, Ne.symm hkl]
  split_ifs <;> push_cast <;> omega

theorem anchoredOverlapCoefficients_off_bounds (S T : Finset (Fin n)) (k l j : Fin n)
    (hk : j ≠ k) (hl : j ≠ l) :
    -1 ≤ anchoredOverlapCoefficients S T k l j ∧
      anchoredOverlapCoefficients S T k l j ≤ 1 := by
  simp only [anchoredOverlapCoefficients, hk, hl, if_false]
  split_ifs <;> omega

/-- Validity forces both anchor multiplicities to be at least two in a
nonzero common point, not merely the multiplier at the second anchor. -/
theorem anchored_overlap_card_multiplier_ge_two (g : Fin n → G) (hg : ValidTuple g)
    (S T : Finset (Fin n)) (k l : Fin n) (hkl : k ≠ l)
    (hk : k ∉ S) (hl : l ∉ T) (x : G) (hx : x ≠ 0)
    (hS : (∑ j ∈ S, (g j - g k)) = x) (hT : (∑ j ∈ T, (g j - g l)) = x) :
    2 ≤ S.card + if k ∈ T then 1 else 0 := by
  by_contra hsmall
  have hTpos : 0 < T.card := by
    by_contra hn
    have ht : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst T
    simp only [Finset.sum_empty] at hT
    exact hx hT.symm
  let c := anchoredOverlapCoefficients S T k l
  have hck := anchoredOverlapCoefficients_left S T k l hkl hk
  have hcl := anchoredOverlapCoefficients_right S T k l hkl hl
  have hpos : 0 < c l := by dsimp only [c]; omega
  have hcne : c ≠ 0 := by
    intro he
    have hzero : c l = 0 := congrFun he l
    omega
  have hcge (j : Fin n) : -1 ≤ c j := by
    by_cases hjk : j = k
    · subst j
      dsimp only [c]
      omega
    by_cases hjl : j = l
    · subst j
      omega
    exact (anchoredOverlapCoefficients_off_bounds S T k l j hjk hjl).1
  apply (validTuple_iff_no_zero_witness g).mp hg c
  refine ⟨hcne, hcge, anchoredOverlapCoefficients_sum S T k l, ?_⟩
  dsimp only [c]
  rw [anchoredOverlapCoefficients_value, hS, hT, sub_self]

/-- Each cube membership can be represented without its zero anchor. -/
theorem mem_anchoredCube_normalized {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k : Fin n) (x : ZMod N) (hx : x ∈ anchoredCube g k) :
    ∃ S : Finset (Fin n), k ∉ S ∧ (∑ j ∈ S, (g j - g k)) = x := by
  obtain ⟨S, _, hS⟩ := Finset.mem_image.mp hx
  refine ⟨S.erase k, by simp, ?_⟩
  calc
    (∑ j ∈ S.erase k, (g j - g k)) = ∑ j ∈ S, (g j - g k) := by
      apply Finset.sum_subset (Finset.erase_subset k S)
      intro j hj hnot
      by_cases hjk : j = k
      · simp [hjk]
      · exact (hnot (Finset.mem_erase.mpr ⟨hjk,hj⟩)).elim
    _ = x := hS

/-- This is the finite ternary-relation exclusion tested by the parallel search.
It is a sufficient condition; arbitrary ternary relations need not correspond
to common points because their subset-cardinality constraints were discarded. -/
def AnchoredPairRelationFree {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k l : Fin n) : Prop :=
  ∀ M : ℕ, 2 ≤ M → M ≤ n → ∀ e : Fin n → ℤ,
    e k = 0 → e l = (M : ℤ) →
    (∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) →
    (∑ j, e j • (g j - g k)) ≠ 0

theorem anchored_intersection_nonzero_multiplier {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (x : ZMod N) (hx : x ≠ 0) (hk : x ∈ anchoredCube g k) (hl : x ∈ anchoredCube g l) :
    ∃ M : ℕ, 2 ≤ M ∧ M ≤ n ∧ ∃ e : Fin n → ℤ,
      e k = 0 ∧ e l = (M : ℤ) ∧
      (∀ j, j ≠ k → j ≠ l → -1 ≤ e j ∧ e j ≤ 1) ∧
      (∑ j, e j • (g j - g k)) = 0 := by
  obtain ⟨S,hSk,hS⟩ := mem_anchoredCube_normalized g k x hk
  obtain ⟨T,hTl,hT⟩ := mem_anchoredCube_normalized g l x hl
  let M := T.card + if l ∈ S then 1 else 0
  have hMlow : 2 ≤ M := anchored_overlap_card_multiplier_ge_two g hg T S l k
    hkl.symm hTl hSk x hx hT hS
  have htcard := Finset.card_le_univ (insert l T)
  rw [Finset.card_insert_of_notMem hTl, Fintype.card_fin] at htcard
  have hMhigh : M ≤ n := by dsimp [M]; split_ifs <;> omega
  let c := anchoredOverlapCoefficients S T k l
  let e : Fin n → ℤ := fun j ↦ if j = k then 0 else c j
  refine ⟨M,hMlow,hMhigh,e,?_,?_,?_,?_⟩
  · simp [e]
  · simpa [e, c, M, hkl.symm] using anchoredOverlapCoefficients_right S T k l hkl hTl
  · intro j hjk hjl
    simpa [e,hjk] using anchoredOverlapCoefficients_off_bounds S T k l j hjk hjl
  · have hcval : (∑ j, c j • g j) = 0 := by
      dsimp only [c]
      rw [anchoredOverlapCoefficients_value,hS,hT,sub_self]
    have hcsum : (∑ j, c j) = 0 := anchoredOverlapCoefficients_sum S T k l
    calc
      (∑ j, e j • (g j-g k)) = ∑ j, c j • (g j-g k) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hjk : j=k <;> simp [e,hjk]
      _ = 0 := by
        simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hcval,hcsum,zero_smul,sub_zero]

theorem anchored_intersection_eq_singleton_of_relation_free {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (hfree : AnchoredPairRelationFree g k l) :
    anchoredCube g k ∩ anchoredCube g l = {0} := by
  ext x
  constructor
  · intro hx
    apply Finset.mem_singleton.mpr
    by_contra hne
    obtain ⟨M,hMlow,hMhigh,e,hek,hel,heb,hev⟩ :=
      anchored_intersection_nonzero_multiplier g hg k l hkl x hne
        (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
    exact hfree M hMlow hMhigh e hek hel heb hev
  · intro hx
    have hx0 : x=0 := Finset.mem_singleton.mp hx
    subst x
    apply Finset.mem_inter.mpr
    constructor <;> exact Finset.mem_image.mpr ⟨∅,Finset.mem_univ _,by simp⟩

/-- A relation-free anchor pair gives the full odd-stratum numerical bound,
even without assuming that the modulus is odd. Existence is an input. -/
theorem two_pow_sub_one_le_modulus_of_relation_free_pair {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (hfree : AnchoredPairRelationFree g k l) : 2^n-1 ≤ N := by
  have hn : 1 ≤ n := by have := k.isLt; omega
  have hk := two_pow_pred_le_anchoredCube_card g hg k
  have hl := two_pow_pred_le_anchoredCube_card g hg l
  have hc := Finset.card_union_add_card_inter (anchoredCube g k) (anchoredCube g l)
  rw [anchored_intersection_eq_singleton_of_relation_free g hg k l hkl hfree,
    Finset.card_singleton] at hc
  have hu : (anchoredCube g k ∪ anchoredCube g l).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (anchoredCube g k ∪ anchoredCube g l)
  have hp : 2^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ,Nat.mul_comm]
  omega

end MinModulus.Research
