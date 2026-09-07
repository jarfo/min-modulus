import MinModulus.ChainForestExteriorPacking
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-! A single upper simplex contains one side of every collision for
ANY actual r-chain forest, including all short arms. Its stars-and-bars
count gives 2^n <= |G|+binomial(n+r-1,r); a truncated-box estimate keeps
the actual short widths as well. No relation, all-long condition, parity,
or unit is supplied. Original three-escape G1 closes below the binomial
window and in every higher two-adic stratum. The smaller window and
unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- Every nontrivial box collision has one upper and one lower
endpoint whose COMBINED distances from the respective corners total
less than n. This exact joint bound retains the full signed coin-budget
information at arbitrary arm lengths and finite arity. -/
theorem box_collision_joint_distance_lt_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ i, p i < 2^(L i)) (hq : ∀ i, q i < 2^(L i))
    (hne : p ≠ q) (he : (∑ i, p i • x i)=∑ i, q i • x i) :
    (∑ i, (2^(L i)-1-p i))+(∑ i, q i) < n ∨
      (∑ i, (2^(L i)-1-q i))+(∑ i, p i) < n := by
  classical
  let d := fun i ↦ p i-q i
  let u := fun i ↦ q i-p i
  have hd : ∀ i, d i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (hp i)
  have hu : ∀ i, u i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (hq i)
  have hdis : ∀ i, d i=0 ∨ u i=0 := by intro i; dsimp only [d,u]; omega
  have hrel : (∑ i, d i • x i)=∑ i, u i • x i := by
    have hpoint : ∀ i, p i • x i+u i • x i=q i • x i+d i • x i := by
      intro i
      rw [← add_nsmul,← add_nsmul]
      congr 1
      dsimp only [d,u]
      omega
    have hs : (∑ i, p i • x i)+(∑ i, u i • x i)=
        (∑ i, q i • x i)+(∑ i, d i • x i) := by
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
    rw [he] at hs
    exact (add_left_cancel hs).symm
  have hpos : (∃ i, 0 < d i) ∨ ∃ i, 0 < u i := by
    by_contra hnot
    simp only [not_or,not_exists,not_lt] at hnot
    apply hne
    funext i
    have hd0 := hnot.1 i
    have hu0 := hnot.2 i
    dsimp only [d,u] at hd0 hu0
    omega
  have oriented (d u : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hu : ∀ i, u i < 2^(L i))
      (hdis : ∀ i, d i=0 ∨ u i=0) (hpos : (∃ i, 0 < d i) ∨ ∃ i, 0 < u i)
      (hcount : (Finset.univ.filter (fun i ↦ 0 < u i)).card ≤
        (Finset.univ.filter (fun i ↦ 0 < d i)).card)
      (hrel : (∑ i, d i • x i)=∑ i, u i • x i) :
      (∑ i, (2^(L i)-1-d i+u i)) < n := by
    have hdpos : ∃ i, 0 < d i := by
      rcases hpos with h | ⟨i,hi⟩
      · exact h
      · have huCard : 0 < (Finset.univ.filter (fun i ↦ 0 < u i)).card :=
          Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
        obtain ⟨j,hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le huCard hcount)
        exact ⟨j,(Finset.mem_filter.mp hj).2⟩
    exact signed_weight_sum_lt_length_of_valid_chain_forest L hL
      g hg E x b hchain d u hd hu hdis hdpos hcount hrel

  rcases le_total (Finset.univ.filter (fun i ↦ 0 < u i)).card
      (Finset.univ.filter (fun i ↦ 0 < d i)).card with hc | hc
  · left
    have hs := oriented d u hd hu hdis hpos hc hrel
    have hpoint : ∀ i, 2^(L i)-1-d i+u i=2^(L i)-1-p i+q i := by
      intro i
      have := hp i
      dsimp only [d,u]
      omega
    simpa only [hpoint,Finset.sum_add_distrib] using hs
  · right
    have hs := oriented u d hu hd (fun i ↦ (hdis i).symm) hpos.symm hc hrel.symm
    have hpoint : ∀ i, 2^(L i)-1-u i+d i=2^(L i)-1-q i+p i := by
      intro i
      have := hq i
      dsimp only [d,u]
      omega
    simpa only [hpoint,Finset.sum_add_distrib] using hs

/-- Every nontrivial collision meets the upper simplex. The stronger
joint-distance theorem also locates its other endpoint near the bottom. -/
theorem box_collision_meets_upper_simplex_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ i, p i < 2^(L i)) (hq : ∀ i, q i < 2^(L i))
    (hne : p ≠ q) (he : (∑ i, p i • x i)=∑ i, q i • x i) :
    (∑ i, (2^(L i)-1-p i)) < n ∨ (∑ i, (2^(L i)-1-q i)) < n := by
  exact (box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain p q hp hq hne he).imp
    (fun h ↦ by omega) (fun h ↦ by omega)

/-- The stronger upper-simplex collision law also gives a rectangular
corner with short arms kept in full. -/
theorem box_collision_meets_truncated_corner_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ i, p i < 2^(L i)) (hq : ∀ i, q i < 2^(L i))
    (hne : p ≠ q) (he : (∑ i, p i • x i)=∑ i, q i • x i) :
    (∀ i, 2^(L i)-n ≤ p i) ∨ (∀ i, 2^(L i)-n ≤ q i) := by
  have aux (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
      (hs : (∑ i, (2^(L i)-1-p i)) < n) : ∀ i, 2^(L i)-n ≤ p i := by
    intro i
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1-p i)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have := hp i
    omega
  exact (box_collision_meets_upper_simplex_of_valid_chain_forest L hL g hg E x b hchain p q hp hq hne he).imp
    (aux p hp) (aux q hq)

/-- Removing a single truncated upper corner makes the entire
binary box injective for EVERY actual valid chain forest. Short-arm
coordinates are retained in full; long-arm corner sides have length n.
No zero relation or classification of mixed fibres is assumed. -/
theorem truncated_corner_box_card_bound_of_valid_chain_forest
    {n : ℕ} (_hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2^n ≤ Fintype.card G+∏ i, min n (2^(L i)) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ ∀ i, 2^(L i)-n ≤ (p i).val
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let CE : {p : B // C p} ≃ (∀ i, Fin (min n (2^(L i)))) :=
    { toFun := fun p i ↦ ⟨(p.val i).val-(2^(L i)-n),by
        have := (p.val i).isLt
        have := p.property i
        omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+(2^(L i)-n),by
        have := (p i).isLt
        omega⟩,fun i ↦ Nat.le_add_left _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact Nat.sub_add_cancel (p.property i)
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have hcorner : Fintype.card {p : B // C p}=∏ i, min n (2^(L i)) := by
    rw [Fintype.card_congr CE,Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hR : Fintype.card R=2^n-(∏ i, min n (2^(L i))) := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox,hcorner]
  have hi : Function.Injective f := by
    intro p q heq
    by_contra hne
    have hvalues : (fun i ↦ (p.val i).val) ≠ (fun i ↦ (q.val i).val) := by
      intro h
      apply hne
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun h i)
    rcases box_collision_meets_truncated_corner_of_valid_chain_forest L hL
        g hg E x b hchain (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val)
        (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) hvalues heq with hp | hq
    · exact p.property hp
    · exact q.property hq
  have hh := Fintype.card_le_of_injective f hi
  rw [hR] at hh
  have hvol : (∏ i, min n (2^(L i))) ≤ 2^n := by
    rw [← hcorner,← hbox]
    exact Fintype.card_subtype_le C
  omega

/-- Arbitrary valid r-chain forests have a polynomial rather than
exponential binary deficit, with ALL arm lengths allowed. -/
theorem polynomial_gap_card_bound_of_valid_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2^n ≤ Fintype.card G+n^(Fintype.card β) := by
  have hh := truncated_corner_box_card_bound_of_valid_chain_forest hn L hL g hg E x b hchain
  have hp := Finset.prod_le_pow_card Finset.univ (fun i ↦ min n (2^(L i))) n
    (fun i _ ↦ min_le_left _ _)
  simp only [Finset.card_univ] at hp
  omega

/-- Injective nonnegative coordinate profiles with total below n
are counted by stars and bars after adding one slack coordinate. -/
theorem card_le_choose_of_injective_small_sum_profiles
    {n : ℕ} (hn : 0 < n) {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℕ) (hf : Function.Injective f)
    (hs : ∀ a, (∑ i, f a i) < n) :
    Fintype.card α ≤ (n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  let H := {v : Option β → ℕ // (∑ i, v i)=n-1}
  let e : Sym (Option β) (n-1) ≃ H := Sym.equivNatSumOfFintype (Option β) (n-1)
  letI : Fintype H := Fintype.ofEquiv (Sym (Option β) (n-1)) e
  let F : α → H := fun a ↦ ⟨fun i ↦ i.elim (n-1-∑ j, f a j) (f a),by
    rw [Fintype.sum_option]
    simp only [Option.elim_none,Option.elim_some]
    exact Nat.sub_add_cancel (by have := hs a; omega)⟩
  have hF : Function.Injective F := by
    intro a b he
    apply hf
    funext i
    exact congrArg (fun z : H ↦ z.val (some i)) he
  have hc : Fintype.card H=(n+Fintype.card β-1).choose (n-1) := by
    rw [← Fintype.card_congr e,Sym.card_sym_eq_choose,Fintype.card_option]
    congr 1
    omega
  have hsym : (n+Fintype.card β-1).choose (n-1)=
      (n+Fintype.card β-1).choose (Fintype.card β) := by
    have hh := Nat.choose_symm (show n-1 ≤ n+Fintype.card β-1 by omega)
    have hsub : n+Fintype.card β-1-(n-1)=Fintype.card β := by omega
    rw [hsub] at hh
    exact hh.symm
  have hh := Fintype.card_le_of_injective F hF
  rwa [hc,hsym] at hh

/-- The upper simplex, rather than the whole rectangular corner,
pays for every collision in an arbitrary actual forest. Any avoided
ambient residues can be charged additively. The error is a binomial
coefficient, with no all-long or supplied-relation hypothesis. -/
theorem binomial_gap_with_avoided_set_of_valid_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (F : Finset G) (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) →
      (∑ i, p i • x i) ≠ z) :
    2^n+F.card ≤ Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ (∑ i, (2^(L i)-1-(p i).val)) < n
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let dist : {p : B // C p} → β → ℕ := fun p i ↦ 2^(L i)-1-(p.val i).val
  have hdist : Function.Injective dist := by
    intro p q he
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh : 2^(L i)-1-(p.val i).val=2^(L i)-1-(q.val i).val := congrFun he i
    have := (p.val i).isLt
    have := (q.val i).isLt
    omega
  have hcorner := card_le_choose_of_injective_small_sum_profiles hn dist hdist (fun p ↦ p.property)
  have hR : Fintype.card R=2^n-Fintype.card {p : B // C p} := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox]
  have hi : Function.Injective f := by
    intro p q heq
    by_contra hne
    have hvalues : (fun i ↦ (p.val i).val) ≠ (fun i ↦ (q.val i).val) := by
      intro h
      apply hne
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun h i)
    rcases box_collision_meets_upper_simplex_of_valid_chain_forest L hL
        g hg E x b hchain (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val)
        (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) hvalues heq with hp | hq
    · exact p.property hp
    · exact q.property hq
  let f' : R → {z : G // z ∉ F} := fun p ↦ ⟨f p,by
    intro hp
    exact havoid (f p) hp (fun i ↦ (p.val i).val) (fun i ↦ (p.val i).isLt) rfl⟩
  have hi' : Function.Injective f' := by
    intro p q he
    exact hi (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f' hi'
  have hremain : Fintype.card {z : G // z ∉ F}=Fintype.card G-F.card := by
    rw [Fintype.card_subtype_compl (fun z : G ↦ z ∈ F)]
    simp only [Fintype.card_coe]
  rw [hR,hremain] at hh
  have hFcard : F.card ≤ Fintype.card G := Finset.card_le_univ F
  have hcorner_le : Fintype.card {p : B // C p} ≤ 2^n := by
    rw [← hbox]
    exact Fintype.card_subtype_le C
  omega

/-- A valid n-tuple arranged in r actual doubling chains has ambient
cardinality at least 2^n-binomial(n+r-1,r), even with arbitrarily short
arms. This is a near-binary estimate, not the sharp global conjecture. -/
theorem binomial_gap_card_bound_of_valid_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2^n ≤ Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  simpa only [Finset.card_empty,add_zero] using
    binomial_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain ∅ (by simp)

/-- The binomial gap is extracted from the actual affine doubling
map at arbitrary escape count. Chains are obtained internally from
injectivity and absence of cycles, with no normal-form premise. -/
theorem binomial_gap_of_injective_acyclic_affine_doubling
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : G) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b)) :
    2^n ≤ Fintype.card G+(n+A.card-1).choose A.card := by
  obtain ⟨L,hL,_,E,x,hchain,_⟩ := exists_affine_chain_forest_of_injective_acyclic_doubling
    g hinj A b hclosed hacyclic
  simpa only [Fintype.card_coe] using
    binomial_gap_card_bound_of_valid_chain_forest hn L hL g hg E x b hchain

/-- Every original three-escape G1 tuple with no half child lies
in a cubic-width window below 2^k, including ALL short-arm cases. The
actual forest is extracted and no relation certificate is assumed. -/
theorem binomial_gap_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    2^(n+1) ≤ 2^(s+1)*q+(n+3).choose 3 := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,_,E,x,hchain,_,_⟩ :=
    exists_actual_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hh := binomial_gap_card_bound_of_valid_chain_forest (by omega) L hL g hg E x b hchain
  simpa only [ZMod.card,Fintype.card_coe,hcard,show n+1+3-1=n+3 by omega] using hh

/-- Direct original G1 descent below the explicit binomial window.
This includes arbitrary arm lengths rather than passing short arms
to a separate assumed gate. The near-endpoint window remains open. -/
theorem admitsValidTuple_half_of_critical_three_escape_below_binomial_window
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hgap : 2^(s+1)*q+(n+3).choose 3 < 2^(n+1)) :
    AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hh := binomial_gap_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  omega

/-- A positive subbinary multiple of 2^s is separated from 2^n by
at least one full multiple of 2^s. No validity or oddness is needed. -/
theorem two_pow_le_gap_of_subbinary_multiple
    {n s q : ℕ} (hq : 0 < q) (hsub : 2^s*q < 2^n) :
    2^s ≤ 2^n-2^s*q := by
  have hbase : 2^s ≤ 2^s*q := by
    have hh := Nat.mul_le_mul_left (2^s) (show 1 ≤ q by omega)
    simpa only [mul_one] using hh
  have hs : s ≤ n := by
    by_contra hnot
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show n ≤ s by omega)
    omega
  have hdiv : 2^s ∣ 2^n-2^s*q := Nat.dvd_sub
    (pow_dvd_pow 2 hs) (dvd_mul_right (2^s) q)
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hsub) hdiv

/-- Every subbinary cyclic r-chain forest has its actual two-adic
step bounded by the binomial error. This is unconditional for the
forest class, including short arms and arbitrary seed multipliers. -/
theorem two_pow_stratum_le_binomial_of_valid_chain_forest
    {n s q : ℕ} (hn : 0 < n) (hq : Odd q)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^s*q)) (b : ZMod (2^s*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^s*q < 2^n) :
    2^s ≤ (n+Fintype.card β-1).choose (Fintype.card β) := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hh := binomial_gap_card_bound_of_valid_chain_forest hn L hL g hg E x b hchain
  rw [ZMod.card] at hh
  have hgap := two_pow_le_gap_of_subbinary_multiple hq.pos hsub
  omega

/-- Every original three-escape G1 case in these high strata has a
half child, regardless of its arm lengths or slack. Only the lower
strata fitting inside the binomial window remain in this class. -/
theorem admitsValidTuple_half_of_critical_three_escape_high_stratum
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hhigh : (n+3).choose 3 < 2^(s+1)) :
    AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hh := binomial_gap_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  have hgap := two_pow_le_gap_of_subbinary_multiple hq.pos hsub
  omega

end MinModulus
