import research.AnchoredOverlapMultipliers

/-! Cardinality compatibility turns multiplier relations into actual overlaps. -/
namespace MinModulus.Research
open Finset
variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- A zero anchored subset sum in a valid tuple contains only the zero anchor. -/
theorem subset_singleton_of_anchored_sum_eq_zero (g : Fin n → G) (hg : ValidTuple g)
    (k : Fin n) (S : Finset (Fin n)) (hs : (∑ j ∈ S, (g j - g k)) = 0) :
    S ⊆ {k} := by
  let e : Fin n → ℤ := fun j ↦ if j ∈ S.erase k then 1 else 0
  have he := ternary_anchor_relation_eq_zero g hg k e (by simp [e]) (by
    intro j
    dsimp only [e]
    split_ifs <;> omega) (by
    simp only [e,ite_smul,one_smul,zero_smul,Finset.sum_ite_mem,Finset.univ_inter]
    calc
      (∑ j ∈ S.erase k, (g j - g k)) = ∑ j ∈ S, (g j - g k) := by
        apply Finset.sum_subset (Finset.erase_subset k S)
        intro j hj hnot
        by_cases hjk : j = k
        · simp [hjk]
        · exact (hnot (Finset.mem_erase.mpr ⟨hjk,hj⟩)).elim
      _ = 0 := hs)
  intro j hj
  apply Finset.mem_singleton.mpr
  by_contra hjk
  have hz := congrFun he j
  simp [e,hjk,hj] at hz

/-- A disjoint signed support satisfying the two cardinality inequalities
can be completed to subsets representing a nonzero common cube point. -/
theorem exists_nonzero_overlap_of_compatible_relation {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n)
    (P Q : Finset (Fin n)) (hPQ : Disjoint P Q)
    (M : ℕ) (hM : 2 ≤ M) (hq : Q.card ≤ M) (hp : M + P.card ≤ n)
    (hrel : (∑ j ∈ P, (g j - g k)) - (∑ j ∈ Q, (g j - g k)) +
      M • (g l - g k) = 0) :
    ∃ x : ZMod N, x ≠ 0 ∧ x ∈ anchoredCube g k ∩ anchoredCube g l := by
  let F : Finset (Fin n) := Finset.univ \ (P ∪ Q)
  have hFcard : M - Q.card ≤ F.card := by
    dsimp only [F]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ,Fintype.card_fin,Finset.card_union_of_disjoint hPQ]
    omega
  obtain ⟨U,hUF,hUcard⟩ := Finset.exists_subset_card_eq hFcard
  have hPU : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro j hjP hjU
    exact (Finset.mem_sdiff.mp (hUF hjU)).2 (Finset.mem_union_left Q hjP)
  have hQU : Disjoint Q U := by
    apply Finset.disjoint_left.mpr
    intro j hjQ hjU
    exact (Finset.mem_sdiff.mp (hUF hjU)).2 (Finset.mem_union_right P hjQ)
  have hcard : Q.card + U.card = M := by omega
  have hshift (W : Finset (Fin n)) :
      (∑ j ∈ W, (g j - g l)) = (∑ j ∈ W, (g j - g k)) - W.card • (g l - g k) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,smul_sub]
    abel
  have heq : (∑ j ∈ P ∪ U, (g j - g k)) = ∑ j ∈ Q ∪ U, (g j - g l) := by
    apply sub_eq_zero.mp
    rw [Finset.sum_union hPU,Finset.sum_union hQU,hshift Q,hshift U]
    calc
      _ = (∑ j ∈ P, (g j - g k)) - (∑ j ∈ Q, (g j - g k)) +
          (Q.card + U.card) • (g l - g k) := by rw [add_nsmul]; abel
      _ = 0 := by rw [hcard]; exact hrel
  refine ⟨∑ j ∈ P ∪ U, (g j - g k),?_,?_⟩
  · intro hz
    have hzero : (∑ j ∈ Q ∪ U, (g j - g l)) = 0 := heq.symm.trans hz
    have hsmall := Finset.card_le_card (subset_singleton_of_anchored_sum_eq_zero g hg l (Q ∪ U) hzero)
    rw [Finset.card_union_of_disjoint hQU,Finset.card_singleton,hcard] at hsmall
    omega
  · apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨P ∪ U,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨Q ∪ U,Finset.mem_univ _,heq.symm⟩

/-- A signed relation whose supports can be completed to subsets. -/
def AnchoredCompatibleRelation {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (k l : Fin n) : Prop :=
  ∃ M : ℕ, 2 ≤ M ∧ ∃ P Q : Finset (Fin n),
    Disjoint P Q ∧ k ∉ P ∧ l ∉ P ∧ k ∉ Q ∧ l ∉ Q ∧
    Q.card ≤ M ∧ M + P.card ≤ n ∧
    (∑ j ∈ P, (g j - g k)) - (∑ j ∈ Q, (g j - g k)) + M • (g l - g k) = 0

theorem compatible_relation_of_nonzero_overlap {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (x : ZMod N) (hx : x ≠ 0) (hk : x ∈ anchoredCube g k) (hl : x ∈ anchoredCube g l) :
    AnchoredCompatibleRelation g k l := by
  obtain ⟨S,hSk,hS⟩ := mem_anchoredCube_normalized g k x hk
  obtain ⟨T,hTl,hT⟩ := mem_anchoredCube_normalized g l x hl
  let P := (S \ T).erase l
  let Q := (T \ S).erase k
  let b : ℕ := if l ∈ S then 1 else 0
  let M := T.card + b
  have hM : 2 ≤ M := anchored_overlap_card_multiplier_ge_two g hg T S l k
    hkl.symm hTl hSk x hx hT hS
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro j hjP hjQ
    have h1 := Finset.mem_sdiff.mp (Finset.mem_erase.mp hjP).2
    have h2 := Finset.mem_sdiff.mp (Finset.mem_erase.mp hjQ).2
    exact h1.2 h2.1
  have hPc : P.card + b = (S \ T).card := by
    by_cases hlS : l ∈ S
    · simpa [P,b,hlS] using Finset.card_erase_add_one
        (show l ∈ S \ T from Finset.mem_sdiff.mpr ⟨hlS,hTl⟩)
    · simp [P,b,hlS]
  have hq : Q.card ≤ M := by
    have hQT : Q ⊆ T := fun j hj ↦ (Finset.mem_sdiff.mp (Finset.mem_erase.mp hj).2).1
    have := Finset.card_le_card hQT
    dsimp [M]
    omega
  have hp : M + P.card ≤ n := by
    have hc := Finset.card_sdiff_add_card S T
    have hu := Finset.card_le_univ (S ∪ T)
    rw [Fintype.card_fin] at hu
    dsimp [M]
    omega
  refine ⟨M,hM,P,Q,hPQ,?_,?_,?_,?_,hq,hp,?_⟩
  · simp [P,hSk]
  · simp [P]
  · simp [Q]
  · simp [Q,hTl]
  have hPv : (∑ j ∈ S \ T, (g j - g k)) =
      (∑ j ∈ P, (g j - g k)) + b • (g l - g k) := by
    by_cases hlS : l ∈ S
    · simpa [P,b,hlS] using (Finset.sum_erase_add (S \ T) (fun j ↦ g j-g k)
        (show l ∈ S \ T from Finset.mem_sdiff.mpr ⟨hlS,hTl⟩)).symm
    · simp [P,b,hlS]
  have hQv : (∑ j ∈ T \ S, (g j - g k)) = ∑ j ∈ Q, (g j - g k) := by
    symm
    apply Finset.sum_subset (Finset.erase_subset k (T \ S))
    intro j hj hnot
    by_cases hjk : j = k
    · simp [hjk]
    · exact (hnot (Finset.mem_erase.mpr ⟨hjk,hj⟩)).elim
  have hshift : (∑ j ∈ T, (g j - g l)) =
      (∑ j ∈ T, (g j - g k)) - T.card • (g l - g k) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,smul_sub]
    abel
  calc
    _ = ((∑ j ∈ P, (g j - g k)) + b • (g l - g k) -
          (∑ j ∈ Q, (g j - g k))) + T.card • (g l - g k) := by
      dsimp only [M]
      rw [add_nsmul]
      abel
    _ = ((∑ j ∈ S \ T, (g j - g k)) -
          (∑ j ∈ T \ S, (g j - g k))) + T.card • (g l - g k) := by rw [hPv,hQv]
    _ = ((∑ j ∈ S, (g j - g k)) -
          (∑ j ∈ T, (g j - g k))) + T.card • (g l - g k) := by
      rw [Finset.sum_sdiff_sub_sum_sdiff]
    _ = (∑ j ∈ S, (g j - g k)) - (∑ j ∈ T, (g j - g l)) := by rw [hshift]; abel
    _ = 0 := by rw [hS,hT,sub_self]

/-- The refined relation test is an equivalence, with explicit cardinality bounds. -/
theorem compatible_relation_iff_nonzero_overlap {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l) :
    AnchoredCompatibleRelation g k l ↔
      ∃ x : ZMod N, x ≠ 0 ∧ x ∈ anchoredCube g k ∩ anchoredCube g l := by
  constructor
  · rintro ⟨M,hM,P,Q,hPQ,_,_,_,_,hq,hp,hrel⟩
    exact exists_nonzero_overlap_of_compatible_relation g hg k l P Q hPQ M hM hq hp hrel
  · rintro ⟨x,hx,hmem⟩
    exact compatible_relation_of_nonzero_overlap g hg k l hkl x hx
      (Finset.mem_inter.mp hmem).1 (Finset.mem_inter.mp hmem).2

theorem anchored_intersection_eq_singleton_iff_no_compatible_relation {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l) :
    anchoredCube g k ∩ anchoredCube g l = {0} ↔ ¬ AnchoredCompatibleRelation g k l := by
  constructor
  · intro heq hrel
    obtain ⟨x,hx,hmem⟩ := (compatible_relation_iff_nonzero_overlap g hg k l hkl).mp hrel
    rw [heq,Finset.mem_singleton] at hmem
    exact hx hmem
  · intro hrel
    ext x
    constructor
    · intro hx
      apply Finset.mem_singleton.mpr
      by_contra hne
      exact hrel ((compatible_relation_iff_nonzero_overlap g hg k l hkl).mpr ⟨x,hne,hx⟩)
    · intro hx
      have hx0 := Finset.mem_singleton.mp hx
      subst x
      apply Finset.mem_inter.mpr
      constructor <;> exact Finset.mem_image.mpr ⟨∅,Finset.mem_univ _,by simp⟩

/-- The full numerical bound needs only exclusion of cardinality-compatible
relations; existence of such an anchor pair is still an explicit hypothesis. -/
theorem two_pow_sub_one_le_modulus_of_no_compatible_relation {N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (k l : Fin n) (hkl : k ≠ l)
    (hfree : ¬ AnchoredCompatibleRelation g k l) : 2^n-1 ≤ N := by
  have hn : 1 ≤ n := by have := k.isLt; omega
  have hk := two_pow_pred_le_anchoredCube_card g hg k
  have hl := two_pow_pred_le_anchoredCube_card g hg l
  have hc := Finset.card_union_add_card_inter (anchoredCube g k) (anchoredCube g l)
  rw [(anchored_intersection_eq_singleton_iff_no_compatible_relation g hg k l hkl).mpr hfree,
    Finset.card_singleton] at hc
  have hu : (anchoredCube g k ∪ anchoredCube g l).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (anchoredCube g k ∪ anchoredCube g l)
  have hp : 2^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ,Nat.mul_comm]
  omega

end MinModulus.Research
