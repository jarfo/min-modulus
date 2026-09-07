import MinModulus.AffineChainForest

/-! Arbitrary-arity binary refinement gives signed-collision restrictions,
small dyadic-sided zero-relation corners, and exact one-corner packing
for long-chain forests. The original three-escape G1 residual supplies
all geometry and arithmetic data internally. Short-arm and positive-slack
arithmetic, and the unrestricted global G1/G2/G3 gates, remain open. -/

namespace MinModulus
open Finset

/-- Independent integer intervals realize every sum between their
endpoint sums. This allocation has arbitrary finite arity. -/
theorem exists_finite_interval_allocation
    {β : Type*} (s : Finset β) (lo hi : β → ℕ)
    (hle : ∀ a ∈ s, lo a ≤ hi a) {K : ℕ}
    (hlow : (∑ a ∈ s, lo a) ≤ K) (hhigh : K ≤ ∑ a ∈ s, hi a) :
    ∃ k : β → ℕ, (∀ a ∈ s, lo a ≤ k a ∧ k a ≤ hi a) ∧ (∑ a ∈ s, k a)=K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    refine ⟨lo,by simp,?_⟩
    simpa using (hhigh.antisymm (Nat.zero_le K)).symm
  | @insert a s ha ih =>
    have hla := hle a (Finset.mem_insert_self _ _)
    have hls : ∀ i ∈ s, lo i ≤ hi i := fun i hi ↦ hle i (Finset.mem_insert_of_mem hi)
    have hsum := Finset.sum_le_sum hls
    simp only [Finset.sum_insert ha] at hlow hhigh
    let R := min (∑ i ∈ s, hi i) (K-lo a)
    have hRlo : (∑ i ∈ s, lo i) ≤ R := by dsimp only [R]; omega
    have hRhi : R ≤ ∑ i ∈ s, hi i := min_le_left _ _
    have hR : R ≤ K := by dsimp only [R]; omega
    have hka : lo a ≤ K-R ∧ K-R ≤ hi a := by dsimp only [R]; omega
    obtain ⟨k,hk,hks⟩ := ih hls hRlo hRhi
    let k' := Function.update k a (K-R)
    have hsame : ∀ i ∈ s, k' i=k i := by
      intro i hi
      exact Function.update_of_ne (by intro he; subst i; exact ha hi) _ _
    refine ⟨k',?_,?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa only [k',Function.update_self] using hka
      · rw [hsame i hi]; exact hk i hi
    · rw [Finset.sum_insert ha]
      have hs : (∑ i ∈ s, k' i)=R := (Finset.sum_congr rfl hsame).trans hks
      rw [hs]
      simp only [k',Function.update_self]
      omega

/-- Arbitrarily many binary chains admit simultaneous refinement
to any joint coin count in their aggregate interval, preserving every
individual chain's integer weight. -/
theorem exists_chain_forest_representations_of_joint_budget
    {β : Type*} [Fintype β] (L X : β → ℕ) (u : β → ℕ → ℕ)
    (hu : ∀ a, val (L a) (u a)=X a) {K : ℕ}
    (hlow : (∑ a, dsum (L a) (u a)) ≤ K) (hhigh : K ≤ ∑ a, X a) :
    ∃ v : β → ℕ → ℕ, (∀ a, val (L a) (v a)=X a) ∧ (∑ a, dsum (L a) (v a))=K := by
  classical
  obtain ⟨k,hk,hks⟩ := exists_finite_interval_allocation Finset.univ
    (fun a ↦ dsum (L a) (u a)) X
    (fun a _ ↦ by simpa only [hu] using dsum_le_val (L a) (u a)) hlow hhigh
  have hex : ∀ a, ∃ v, val (L a) v=X a ∧ dsum (L a) v=k a := by
    intro a
    exact exists_dsum_eq ⟨u a,hu a,(hk a (Finset.mem_univ _)).1⟩ (hk a (Finset.mem_univ _)).2
  choose v hv hd using hex
  exact ⟨v,hv,by simpa only [hd] using hks⟩

/-- Nonstandard forest weights at the actual distinguished sum
contradict validity when their joint coin interval reaches the original
length. Every seed, affine offset and original coordinate is retained. -/
theorem not_validTuple_of_chain_forest_integer_weights
    {n : ℕ} {β : Type*} [Fintype β] (L X : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (u : β → ℕ → ℕ) (hu : ∀ a, val (L a) (u a)=X a)
    (hlow : (∑ a, dsum (L a) (u a)) ≤ n) (hhigh : n ≤ ∑ a, X a)
    (hneq : ∃ a, X a ≠ 2^(L a)-1)
    (hsum : (∑ a, X a • x a)=∑ a, (2^(L a)-1) • x a) : ¬ ValidTuple g := by
  classical
  intro hg
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  obtain ⟨v,hvval,hcard⟩ := exists_chain_forest_representations_of_joint_budget L X u hu hlow hhigh
  let c : Fin n → ℕ := fun i ↦ v (E.symm i).1 (E.symm i).2.val
  have hcs : ∀ a (i : Fin (L a)), c (E ⟨a,i⟩)=v a i.val := by
    intro a i
    change (fun p : Σ a : β, Fin (L a) ↦ v p.1 p.2.val) (E.symm (E ⟨a,i⟩))=v a i.val
    rw [E.symm_apply_apply]
  have hnreindex (f : Fin n → ℕ) :
      (∑ i, f i)=∑ a, ∑ j : Fin (L a), f (E ⟨a,j⟩) := by
    rw [← E.sum_comp f,Fintype.sum_sigma]
  have hgreindex (f : Fin n → G) :
      (∑ i, f i)=∑ a, ∑ j : Fin (L a), f (E ⟨a,j⟩) := by
    rw [← E.sum_comp f,Fintype.sum_sigma]
  have hc : (∑ i, c i)=n := by
    rw [hnreindex]
    simpa only [hcs,Fin.sum_univ_eq_sum_range,dsum] using hcard
  have hcoeff (a : β) : (∑ j : Fin (L a), v a j.val • (2^j.val • x a))=X a • x a := by
    simp only [smul_smul]
    rw [← Finset.sum_smul]
    have hw : (∑ j : Fin (L a), v a j.val*2^j.val)=X a := by
      exact (Fin.sum_univ_eq_sum_range (fun j ↦ v a j*2^j) (L a)).trans (hvval a)
    rw [hw]
  have hbase (a : β) : (∑ j : Fin (L a), 2^j.val • x a)=(2^(L a)-1) • x a := by
    rw [← Finset.sum_smul,sum_binary_powers]
  have htotal : (∑ i, c i • (g i+b))=∑ i, (g i+b) := by
    rw [hgreindex,hgreindex]
    simp only [hcs,hchain,hcoeff,hbase]
    exact hsum
  have hone := hv c hc htotal
  obtain ⟨a,ha⟩ := hneq
  apply ha
  rw [← hvval a]
  have hones : ∀ i < L a, v a i=1 := by
    intro i hi
    simpa only [hcs] using hone (E ⟨a,⟨i,hi⟩⟩)
  unfold val
  calc
    _=∑ i ∈ Finset.range (L a), 2^i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hones i (Finset.mem_range.mp hi),one_mul]
    _=2^(L a)-1 := sum_two_pow (L a)

/-- For any bounded signed seed relation, orient the move so that
it increases no more chains than it decreases. The resulting nonstandard
weights must have total weight BELOW the original tuple length.
Otherwise the saved binary coins supply an actual full-length rival. -/
theorem signed_weight_sum_lt_length_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
    (hdisjoint : ∀ a, d a=0 ∨ u a=0) (hpos : ∃ a, 0 < d a)
    (hcount : (Finset.univ.filter (fun a ↦ 0 < u a)).card ≤
      (Finset.univ.filter (fun a ↦ 0 < d a)).card)
    (hrel : (∑ a, d a • x a)=∑ a, u a • x a) :
    (∑ a, (2^(L a)-1-d a+u a)) < n := by
  classical
  let X : β → ℕ := fun a ↦ 2^(L a)-1-d a+u a
  have hrep : ∀ a, ∃ v, val (L a) v=X a ∧
      dsum (L a) v+(if 0 < d a then 1 else 0) ≤ L a+(if 0 < u a then 1 else 0) := by
    intro a
    have hp : 0 < 2^(L a) := by positivity
    by_cases hda : 0 < d a
    · have hua : u a=0 := (hdisjoint a).resolve_left (by omega)
      have hX : X a < 2^(L a)-1 := by dsimp only [X]; have := hd a; omega
      obtain ⟨v,_,hv,hvds⟩ := exists_rep_lt (L a) (X a) hX
      refine ⟨v,hv,?_⟩
      simp only [if_pos hda,hua,lt_self_iff_false,if_false,add_zero]
      have := hL a
      omega
    · have hda0 : d a=0 := by omega
      by_cases hua : 0 < u a
      · obtain ⟨v,_,hv,hvds⟩ := exists_binary_rep_all_ones_add_small (hL a) (hu a)
        refine ⟨v,?_,?_⟩
        · simpa only [X,hda0,Nat.sub_zero] using hv
        · simpa only [if_neg hda,if_pos hua,add_zero] using hvds
      · have hua0 : u a=0 := by omega
        have hX : X a < 2^(L a) := by simp only [X,hda0,hua0,Nat.sub_zero,add_zero]; omega
        obtain ⟨v,_,hv,hvds⟩ := exists_rep_le (L a) (X a) hX
        exact ⟨v,hv,by simpa only [if_neg hda,if_neg hua,add_zero] using hvds⟩
  choose v hv hcost using hrep
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hcostsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hcost a)
  simp only [Finset.sum_add_distrib] at hcostsum
  have hdcard : (∑ a, if 0 < d a then 1 else 0)=
      (Finset.univ.filter (fun a ↦ 0 < d a)).card := by simp
  have hucard : (∑ a, if 0 < u a then 1 else 0)=
      (Finset.univ.filter (fun a ↦ 0 < u a)).card := by simp
  rw [hdcard,hucard,hsize] at hcostsum
  have hlow : (∑ a, dsum (L a) (v a)) ≤ n := by omega
  have hsum : (∑ a, X a • x a)=∑ a, (2^(L a)-1) • x a := by
    apply add_right_cancel (b := ∑ a, d a • x a)
    rw [← Finset.sum_add_distrib]
    have hpoint : ∀ a, X a • x a+d a • x a=(2^(L a)-1) • x a+u a • x a := by
      intro a
      rw [← add_nsmul,← add_nsmul]
      congr 1
      have := hd a
      dsimp only [X]
      omega
    simp only [hpoint,Finset.sum_add_distrib,hrel]
  have hneq : ∃ a, X a ≠ 2^(L a)-1 := by
    obtain ⟨a,ha⟩ := hpos
    have hua : u a=0 := (hdisjoint a).resolve_left (by omega)
    refine ⟨a,?_⟩
    have := hd a
    dsimp only [X]
    omega
  by_contra hnot
  change ¬ (∑ a, X a) < n at hnot
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain v hv
    hlow (by omega) hneq hsum hg

/-- Every bounded nonzero nonnegative relation in an arbitrary actual
forest leaves only a small far corner. No three-chain cutoff is used. -/
theorem small_complement_of_zero_relation_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hpos : ∃ a, 0 < d a)
    (hrel : (∑ a, d a • x a)=0) : (∑ a, (2^(L a)-1-d a)) < n := by
  have hh := signed_weight_sum_lt_length_of_valid_chain_forest L hL g hg E x b hchain
    d (fun _ ↦ 0) hd (fun _ ↦ by positivity) (fun _ ↦ Or.inr rfl) hpos
    (by simp) (by simpa using hrel)
  simpa only [add_zero] using hh

/-- The small corner has total side length at most n+r-1 for r
chains. This is a dimension-uniform consequence of actual validity. -/
theorem corner_side_sum_le_length_add_roots_sub_one_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hpos : ∃ a, 0 < d a)
    (hrel : (∑ a, d a • x a)=0) :
    (∑ a, (2^(L a)-d a)) ≤ n+Fintype.card β-1 := by
  have hh := small_complement_of_zero_relation_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hrel
  have hp : ∀ a, 2^(L a)-d a=(2^(L a)-1-d a)+1 := by intro a; have := hd a; omega
  simp only [hp,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  omega

/-- In the coin-saving orientation of ANY mixed bounded relation,
EVERY increased chain has binary width strictly below the full tuple
length. Thus signed collisions are confined to genuinely short arms. -/
theorem increased_chain_width_lt_length_of_bounded_seed_relation
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
    (hdisjoint : ∀ a, d a=0 ∨ u a=0) (hpos : ∃ a, 0 < d a)
    (hcount : (Finset.univ.filter (fun a ↦ 0 < u a)).card ≤
      (Finset.univ.filter (fun a ↦ 0 < d a)).card)
    (hrel : (∑ a, d a • x a)=∑ a, u a • x a)
    (a : β) (ha : 0 < u a) : 2^(L a) < n := by
  have hs := signed_weight_sum_lt_length_of_valid_chain_forest L hL g hg E x b hchain
    d u hd hu hdisjoint hpos hcount hrel
  have hda : d a=0 := (hdisjoint a).resolve_right (by omega)
  have hsingle := Finset.single_le_sum (f := fun a ↦ 2^(L a)-1-d a+u a)
    (fun i (_ : i ∈ Finset.univ) ↦ Nat.zero_le _) (Finset.mem_univ a)
  have hp : 0 < 2^(L a) := by positivity
  rw [hda,Nat.sub_zero] at hsingle
  omega

/-- Balanced-support mixed relations are impossible at ANY arm lengths.
Both orientations fit the coin budget, and their total integer weights
average at least the original length. This works in arbitrary arity. -/
theorem balanced_support_seed_relation_ne_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
    (hdisjoint : ∀ a, d a=0 ∨ u a=0) (hdpos : ∃ a, 0 < d a) (hupos : ∃ a, 0 < u a)
    (hcount : (Finset.univ.filter (fun a ↦ 0 < u a)).card =
      (Finset.univ.filter (fun a ↦ 0 < d a)).card) :
    (∑ a, d a • x a) ≠ ∑ a, u a • x a := by
  intro he
  have h1 := signed_weight_sum_lt_length_of_valid_chain_forest L hL g hg E x b hchain
    d u hd hu hdisjoint hdpos hcount.le he
  have h2 := signed_weight_sum_lt_length_of_valid_chain_forest L hL g hg E x b hchain
    u d hu hd (fun a ↦ (hdisjoint a).symm) hupos hcount.ge he.symm
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbase : n ≤ ∑ a, (2^(L a)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro a _
    have := Nat.lt_two_pow_self (n := L a)
    omega
  have hp : ∀ a, (2^(L a)-1-d a+u a)+(2^(L a)-1-u a+d a)=2*(2^(L a)-1) := by
    intro a; have := hd a; have := hu a; omega
  have hs : (∑ a, (2^(L a)-1-d a+u a))+(∑ a, (2^(L a)-1-u a+d a))=
      2*(∑ a, (2^(L a)-1)) := by rw [← Finset.sum_add_distrib]; simp only [hp,Finset.mul_sum]
  omega

/-- If every arm has binary width at least the original length, no
bounded mixed-sign seed relation exists. There is no fixed arity,
unit, parity, modulus or subbinary assumption. -/
theorem mixed_seed_relation_ne_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (hlong : ∀ a, n ≤ 2^(L a))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
    (hdisjoint : ∀ a, d a=0 ∨ u a=0) (hdpos : ∃ a, 0 < d a) (hupos : ∃ a, 0 < u a) :
    (∑ a, d a • x a) ≠ ∑ a, u a • x a := by
  intro he
  classical
  rcases le_total (Finset.univ.filter (fun a ↦ 0 < u a)).card
      (Finset.univ.filter (fun a ↦ 0 < d a)).card with hc | hc
  · obtain ⟨a,ha⟩ := hupos
    have hh := increased_chain_width_lt_length_of_bounded_seed_relation L hL g hg E x b hchain
      d u hd hu hdisjoint hdpos hc he a ha
    exact (not_lt_of_ge (hlong a)) hh
  · obtain ⟨a,ha⟩ := hdpos
    have hh := increased_chain_width_lt_length_of_bounded_seed_relation L hL g hg E x b hchain
      u d hu hd (fun a ↦ (hdisjoint a).symm) hupos hc he.symm a ha
    exact (not_lt_of_ge (hlong a)) hh

/-- The full binary box has coordinatewise ordered fibres whenever
every actual chain is long. This is a uniform multi-dimensional packing
restriction, not an assumed two-chain classification. -/
theorem box_fibres_ordered_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (hlong : ∀ a, n ≤ 2^(L a))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ a, p a < 2^(L a)) (hq : ∀ a, q a < 2^(L a))
    (he : (∑ a, p a • x a)=∑ a, q a • x a) :
    (∀ a, p a ≤ q a) ∨ (∀ a, q a ≤ p a) := by
  classical
  by_contra hnot
  simp only [not_or,not_forall,not_le] at hnot
  obtain ⟨⟨a,ha⟩,⟨c,hc⟩⟩ := hnot
  let d := fun i ↦ p i-q i
  let u := fun i ↦ q i-p i
  have hd : ∀ i, d i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (hp i)
  have hu : ∀ i, u i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (hq i)
  have hdis : ∀ i, d i=0 ∨ u i=0 := by intro i; dsimp only [d,u]; omega
  have hrel : (∑ i, d i • x i)=∑ i, u i • x i := by
    have hpoint : ∀ i, p i • x i+u i • x i=q i • x i+d i • x i := by
      intro i; rw [← add_nsmul,← add_nsmul]; congr 1; dsimp only [d,u]; omega
    have hs : (∑ i, p i • x i)+(∑ i, u i • x i)=
        (∑ i, q i • x i)+(∑ i, d i • x i) := by
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
    rw [he] at hs
    exact (add_left_cancel hs).symm
  exact mixed_seed_relation_ne_of_valid_long_chain_forest L hL hlong g hg E x b hchain
    d u hd hu hdis ⟨a,by dsimp only [d]; omega⟩ ⟨c,by dsimp only [u]; omega⟩ hrel

/-- Subbinary cardinality forces a real nonnegative box relation when
all actual chains are long. Its far corner has total side length at most
n+r-1. No relation, unit or supplied packing certificate is assumed. -/
theorem exists_small_corner_relation_of_valid_subbinary_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (hlong : ∀ a, n ≤ 2^(L a))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hcard : Fintype.card G < 2^n) :
    ∃ d : β → ℕ, (∀ a, d a < 2^(L a)) ∧ (∃ a, 0 < d a) ∧
      (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+Fintype.card β-1 := by
  classical
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  let f : (∀ a, Fin (2^(L a))) → G := fun p ↦ ∑ a, (p a).val • x a
  have hbox : Fintype.card (∀ a, Fin (2^(L a)))=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  have hni : ¬ Function.Injective f := Fintype.not_injective_of_card_lt f (by rwa [hbox])
  simp only [Function.Injective,not_forall] at hni
  obtain ⟨p,q,he,hne⟩ := hni
  have build (p q : ∀ a, Fin (2^(L a))) (hne : p ≠ q) (he : f p=f q)
      (hle : ∀ a, (p a).val ≤ (q a).val) :
      ∃ d : β → ℕ, (∀ a, d a < 2^(L a)) ∧ (∃ a, 0 < d a) ∧
        (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+Fintype.card β-1 := by
    let d := fun a ↦ (q a).val-(p a).val
    have hd : ∀ a, d a < 2^(L a) := fun a ↦ (Nat.sub_le _ _).trans_lt (q a).isLt
    have hpos : ∃ a, 0 < d a := by
      by_contra hnot
      push Not at hnot
      apply hne
      funext a
      apply Fin.ext
      have h0 : (q a).val-(p a).val ≤ 0 := hnot a
      have h1 := hle a
      omega
    have hz : (∑ a, d a • x a)=0 := by
      apply add_left_cancel (a := f p)
      change (∑ a, (p a).val • x a)+(∑ a, d a • x a)=f p+0
      rw [← Finset.sum_add_distrib]
      have hp : ∀ a, (p a).val • x a+d a • x a=(q a).val • x a := by
        intro a; rw [← add_nsmul]; congr 1; exact Nat.add_sub_of_le (hle a)
      simp only [hp,add_zero]
      exact he.symm
    exact ⟨d,hd,hpos,hz,
      corner_side_sum_le_length_add_roots_sub_one_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hz⟩
  have he' : (∑ a, (p a).val • x a)=∑ a, (q a).val • x a := he
  rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain
      (fun a ↦ (p a).val) (fun a ↦ (q a).val) (fun a ↦ (p a).isLt) (fun a ↦ (q a).isLt) he' with h | h
  · exact build p q hne he h
  · exact build q p (Ne.symm hne) he.symm h

/-- Ordered box collisions give actual nonnegative seed relations,
in arbitrary finite arity and any abelian group. -/
theorem zero_relation_of_ordered_box_collision
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (x : β → G) (p q : β → ℕ) (hle : ∀ a, p a ≤ q a)
    (he : (∑ a, p a • x a)=∑ a, q a • x a) :
    (∑ a, (q a-p a) • x a)=0 := by
  apply add_left_cancel (a := ∑ a, p a • x a)
  rw [← Finset.sum_add_distrib]
  have hp : ∀ a, p a • x a+(q a-p a) • x a=q a • x a := by
    intro a; rw [← add_nsmul,Nat.add_sub_of_le (hle a)]
  simp only [hp,add_zero]
  exact he.symm

/-- If the full box is wide, its nonzero nonnegative zero relation
is UNIQUE. Ordered fibres and the small-complement inequality rule out
two distinct relations. The statement has arbitrary finite arity. -/
theorem unique_nonzero_box_relation_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (hlong : ∀ a, n ≤ 2^(L a)) (hwide : 2*n ≤ ∑ a, (2^(L a)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
    (hdpos : ∃ a, 0 < d a) (hupos : ∃ a, 0 < u a)
    (hdzero : (∑ a, d a • x a)=0) (huzero : (∑ a, u a • x a)=0) : d=u := by
  classical
  have aux (d u : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hu : ∀ a, u a < 2^(L a))
      (hdpos : ∃ a, 0 < d a) (hdzero : (∑ a, d a • x a)=0)
      (huzero : (∑ a, u a • x a)=0) (hle : ∀ a, d a ≤ u a) : d=u := by
    by_contra hne
    have hvpos : ∃ a, 0 < u a-d a := by
      by_contra hnot
      push Not at hnot
      apply hne
      funext a
      have := hnot a
      have := hle a
      omega
    have hv : ∀ a, u a-d a < 2^(L a) := fun a ↦ (Nat.sub_le _ _).trans_lt (hu a)
    have hvzero := zero_relation_of_ordered_box_collision x d u hle (hdzero.trans huzero.symm)
    have hs := small_complement_of_zero_relation_of_valid_chain_forest L hL g hg E x b hchain d hd hdpos hdzero
    have ht := small_complement_of_zero_relation_of_valid_chain_forest L hL g hg E x b hchain
      (fun a ↦ u a-d a) hv hvpos hvzero
    have hp : ∀ a, (2^(L a)-1) ≤ (2^(L a)-1-d a)+(2^(L a)-1-(u a-d a)) := by
      intro a; have := hd a; have := hu a; have := hle a; omega
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hp a)
    rw [Finset.sum_add_distrib] at hh
    omega
  rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain
      d u hd hu (hdzero.trans huzero.symm) with h | h
  · exact aux d u hd hu hdpos hdzero huzero h
  · exact (aux u d hu hd hupos huzero hdzero h).symm

/-- Removing the ONE upper corner translated by the unique relation
leaves an injective full binary box. Hence its whole binary deficit is
paid for by that corner's PRODUCT volume, in arbitrary finite arity. -/
theorem box_card_bound_of_valid_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (hlong : ∀ a, n ≤ 2^(L a)) (hwide : 2*n ≤ ∑ a, (2^(L a)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hdpos : ∃ a, 0 < d a)
    (hdzero : (∑ a, d a • x a)=0) :
    2^n ≤ Fintype.card G+∏ a, (2^(L a)-d a) := by
  classical
  let B := ∀ a, Fin (2^(L a))
  let C : B → Prop := fun p ↦ ∀ a, d a ≤ (p a).val
  let f : B → G := fun p ↦ ∑ a, (p a).val • x a
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let CEquiv : {p : B // C p} ≃ (∀ a, Fin (2^(L a)-d a)) :=
    { toFun := fun p a ↦ ⟨(p.val a).val-d a,by have := (p.val a).isLt; have := p.property a; omega⟩
      invFun := fun p ↦ ⟨fun a ↦ ⟨(p a).val+d a,by have := (p a).isLt; have := hd a; omega⟩,
        fun a ↦ Nat.le_add_left _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        funext a
        apply Fin.ext
        exact Nat.sub_add_cancel (p.property a)
      right_inv := by
        intro p
        funext a
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have hcorner : (Finset.univ.filter C).card=∏ a, (2^(L a)-d a) := by
    rw [← Fintype.card_subtype C,Fintype.card_congr CEquiv,Fintype.card_pi]
    simp only [Fintype.card_fin]
  let R := Finset.univ.filter (fun p : B ↦ ¬ C p)
  have hfi : Set.InjOn f (↑R : Set B) := by
    have aux (p q : B) (hq : ¬ C q) (he : f p=f q)
        (hle : ∀ a, (p a).val ≤ (q a).val) : p=q := by
      by_contra hne
      let u := fun a ↦ (q a).val-(p a).val
      have hu : ∀ a, u a < 2^(L a) := fun a ↦ (Nat.sub_le _ _).trans_lt (q a).isLt
      have hupos : ∃ a, 0 < u a := by
        by_contra hnot
        push Not at hnot
        apply hne
        funext a
        apply Fin.ext
        have h0 : (q a).val-(p a).val ≤ 0 := hnot a
        have := hle a
        omega
      have huzero := zero_relation_of_ordered_box_collision x
        (fun a ↦ (p a).val) (fun a ↦ (q a).val) hle he
      have heq := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
        g hg E x b hchain d u hd hu hdpos hupos hdzero huzero
      apply hq
      intro a
      have hh := congrFun heq a
      dsimp only [u] at hh
      omega
    intro p hp q hq he
    have hp' : ¬ C p := (Finset.mem_filter.mp hp).2
    have hq' : ¬ C q := (Finset.mem_filter.mp hq).2
    rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain
        (fun a ↦ (p a).val) (fun a ↦ (q a).val) (fun a ↦ (p a).isLt) (fun a ↦ (q a).isLt) he with h | h
    · exact aux p q hq' he h
    · exact (aux q p hp' he.symm h).symm
  have hR : R.card ≤ Fintype.card G := by
    rw [← Finset.card_image_of_injOn hfi]
    exact Finset.card_le_univ _
  have hpartition := Finset.card_filter_add_card_filter_not (s := Finset.univ) C
  rw [hcorner,Finset.card_univ,hbox] at hpartition
  change (∏ a, (2^(L a)-d a))+R.card=2^n at hpartition
  omega

/-- Every nonzero bounded forest zero relation has a POWER-OF-TWO
corner side. If every side were a non-power, the complement savings
would pay for a far-side full-length rival in arbitrary arity. -/
theorem exists_power_corner_side_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ a, d a < 2^(L a)) (hdpos : ∃ a, 0 < d a)
    (hdzero : (∑ a, d a • x a)=0) :
    ∃ a e, 2^(L a)-d a=2^e := by
  classical
  by_contra hnot
  have hnonpower : ∀ a, ¬ ∃ e, 2^(L a)-d a=2^e := by
    intro a he
    obtain ⟨e,he⟩ := he
    exact hnot ⟨a,e,he⟩
  have hdpositive : ∀ a, 0 < d a := by
    intro a
    by_contra hda
    have hz : d a=0 := by omega
    exact hnonpower a ⟨L a,by rw [hz,Nat.sub_zero]⟩
  let X := fun a ↦ 2^(L a)-1+d a
  have hrep : ∀ a, ∃ v, val (L a) v=X a ∧ dsum (L a) v ≤ L a := by
    intro a
    have hda := hd a
    have hdpos := hdpositive a
    obtain ⟨v,_,hv,hcost⟩ := exists_binary_rep_double_range_sub_nonpower (hL a)
      (by omega : 0 < 2^(L a)-d a) (by omega : 2^(L a)-d a < 2^(L a)) (hnonpower a)
    exact ⟨v,hv.trans (by dsimp only [X]; omega),hcost⟩
  choose v hv hcost using hrep
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hlow : (∑ a, dsum (L a) (v a)) ≤ n := by
    rw [← hsize]
    exact Finset.sum_le_sum (fun a _ ↦ hcost a)
  have hhigh : n ≤ ∑ a, X a := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro a _
    have := Nat.lt_two_pow_self (n := L a)
    dsimp only [X]
    omega
  have hneq : ∃ a, X a ≠ 2^(L a)-1 := by
    obtain ⟨a,ha⟩ := hdpos
    exact ⟨a,by dsimp only [X]; omega⟩
  have hsum : (∑ a, X a • x a)=∑ a, (2^(L a)-1) • x a := by
    simp only [X,add_nsmul,Finset.sum_add_distrib,hdzero,add_zero]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain v hv hlow hhigh hneq hsum hg

/-- Original critical three-escape G1 data now supply actual spanning
chains and a concrete arithmetic alternative: a genuinely short arm,
or an extracted nonnegative relation with a small three-dimensional
corner paying for the whole binary deficit, and at least one dyadic
corner side. Neither geometry nor the relation is a new premise. -/
theorem exists_short_arm_or_small_corner_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
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
      ((∃ a, 2^(L a) < n+1) ∨ ∃ d : A → ℕ, (∀ a, d a < 2^(L a)) ∧
        (∃ a, 0 < d a) ∧ (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+3 ∧
        (∃ a e, 2^(L a)-d a=2^e) ∧ 2^(n+1) ≤ 2^(s+1)*q+∏ a, (2^(L a)-d a)) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,?_⟩
  by_cases hlong : ∀ a, n+1 ≤ 2^(L a)
  · right
    have hN : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
      rw [ZMod.card]
      exact lt_of_lt_of_le hc (by unfold stratumBound; exact Nat.sub_le _ _)
    obtain ⟨d,hd,hpos,hzero,hcorner⟩ :=
      exists_small_corner_relation_of_valid_subbinary_long_chain_forest L hL hlong g hg E x b hchain hN
    have hAr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
    rw [hAr] at hcorner
    have hwide : 2*(n+1) ≤ ∑ a, (2^(L a)-1) := by
      have hh : (∑ _a : A, n) ≤ ∑ a, (2^(L a)-1) := by
        apply Finset.sum_le_sum
        intro a _
        have := hlong a
        omega
      simp only [Finset.sum_const,Finset.card_univ,hAr,smul_eq_mul] at hh
      omega
    have hp := box_card_bound_of_valid_long_chain_forest L hL hlong hwide g hg E x b hchain d hd hpos hzero
    rw [ZMod.card] at hp
    exact ⟨d,hd,hpos,hzero,by omega,
      exists_power_corner_side_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hzero,hp⟩
  · left
    simpa only [not_forall,not_le] using hlong

end MinModulus
