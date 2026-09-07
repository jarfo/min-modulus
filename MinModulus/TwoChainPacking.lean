import MinModulus.TwoChainRelations

/-! Subbinary cardinality extracts a unique nonnegative rectangle
relation, and one small dyadic-sided corner pays for the whole binary
deficit. This proves a uniform near-binary bound for actual two chains;
the sharp cyclic bound and unrestricted geometry extraction stay open. -/

namespace MinModulus
open Finset

/-- The complementary-weight bound also holds for nonzero relations on
either axis. Swapping the actual chains supplies the missing endpoint. -/
theorem small_corner_of_nonzero_relation_of_valid_two_chains
    {A L d u : ℕ} (hdA : d < 2^A) (huL : u < 2^L) (hne : d ≠ 0 ∨ u ≠ 0)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : d • x+u • y=0) : (2^A-d)+(2^L-u) ≤ A+L+1 := by
  by_cases hd : d=0
  · have hu : 0 < u := by omega
    let f : Fin (L+A) → G := fun i ↦ g (finAddFlip i)
    have hf : ValidTuple f := validTuple_embedding finAddFlip.toEmbedding g hg
    have hl : ∀ i : Fin L, f (Fin.castAdd A i)=2^i.val • y := by
      intro i; simp only [f,finAddFlip_apply_castAdd,hright]
    have hr : ∀ i : Fin A, f (Fin.natAdd L i)=2^i.val • x := by
      intro i; simpa only [f,finAddFlip_apply_natAdd] using hleft i
    have hs := small_complement_of_zero_relation_of_valid_two_chains hu huL hdA
      f hf y x hl hr (by simpa only [add_comm] using hrel)
    omega
  · have hs := small_complement_of_zero_relation_of_valid_two_chains
      (Nat.pos_of_ne_zero hd) hdA huL g hg x y hleft hright hrel
    omega

/-- Subtract comparable coordinates of a rectangle collision to obtain
an actual nonnegative zero relation, with no cyclic normalization. -/
theorem zero_relation_of_ordered_rectangle_collision
    {G : Type*} [AddCommGroup G] (x y : G)
    {X Y X' Y' : ℕ} (hX : X ≤ X') (hY : Y ≤ Y')
    (heq : X • x+Y • y=X' • x+Y' • y) :
    (X'-X) • x+(Y'-Y) • y=0 := by
  have hx : X • x+(X'-X) • x=X' • x := by rw [← add_nsmul,Nat.add_sub_of_le hX]
  have hy : Y • y+(Y'-Y) • y=Y' • y := by rw [← add_nsmul,Nat.add_sub_of_le hY]
  apply add_left_cancel (a := X • x+Y • y)
  calc
    _=X' • x+Y' • y := by rw [← hx,← hy]; abel
    _=X • x+Y • y := heq.symm
    _=_ := by rw [add_zero]

/-- Subbinary cardinality itself forces a nonzero relation in the
nonnegative binary rectangle. Ordered fibres exclude mixed signs. -/
theorem exists_nonzero_rectangle_relation_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L)) :
    ∃ d u : ℕ, d < 2^A ∧ u < 2^L ∧ (d ≠ 0 ∨ u ≠ 0) ∧
      d • x+u • y=0 ∧ (2^A-d)+(2^L-u) ≤ A+L+1 := by
  classical
  let f : Fin (2^A) × Fin (2^L) → G := fun p ↦ p.1.val • x+p.2.val • y
  have hn : ¬ Function.Injective f := Fintype.not_injective_of_card_lt f (by
    simpa only [Fintype.card_prod,Fintype.card_fin,← pow_add] using hcard)
  simp only [Function.Injective,not_forall] at hn
  obtain ⟨p,q,he,hne⟩ := hn
  have he' : p.1.val • x+p.2.val • y=q.1.val • x+q.2.val • y := he
  have build : ∀ p q : Fin (2^A) × Fin (2^L), p ≠ q →
      p.1.val • x+p.2.val • y=q.1.val • x+q.2.val • y →
      p.1.val ≤ q.1.val → p.2.val ≤ q.2.val →
      ∃ d u : ℕ, d < 2^A ∧ u < 2^L ∧ (d ≠ 0 ∨ u ≠ 0) ∧
        d • x+u • y=0 ∧ (2^A-d)+(2^L-u) ≤ A+L+1 := by
    intro p q hpq he hx hy
    have hne : q.1.val-p.1.val ≠ 0 ∨ q.2.val-p.2.val ≠ 0 := by
      by_contra h
      push Not at h
      apply hpq
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hd : q.1.val-p.1.val < 2^A := lt_of_le_of_lt (Nat.sub_le _ _) q.1.isLt
    have hu : q.2.val-p.2.val < 2^L := lt_of_le_of_lt (Nat.sub_le _ _) q.2.isLt
    have hz := zero_relation_of_ordered_rectangle_collision x y hx hy he
    exact ⟨_,_,hd,hu,hne,hz,
      small_corner_of_nonzero_relation_of_valid_two_chains hd hu hne g hg x y hleft hright hz⟩
  rcases rectangle_fibres_ordered_of_valid_two_chains hA hL g hg x y hleft hright
    p.1.isLt p.2.isLt q.1.isLt q.2.isLt he' with h | h
  · exact build p q hne he' h.1 h.2
  · exact build q p (Ne.symm hne) he'.symm h.1 h.2

/-- Two distinct nonzero corner relations would yield a third relation
by subtraction. The two large coordinate sums cannot fit one rectangle. -/
theorem unique_nonzero_rectangle_relation_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hwide : 2*(A+L) ≤ (2^A-1)+(2^L-1))
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    {d u d' u' : ℕ} (hd : d < 2^A) (hu : u < 2^L) (hne : d ≠ 0 ∨ u ≠ 0)
    (hd' : d' < 2^A) (hu' : u' < 2^L) (hne' : d' ≠ 0 ∨ u' ≠ 0)
    (hz : d • x+u • y=0) (hz' : d' • x+u' • y=0) : d=d' ∧ u=u' := by
  have aux : ∀ {d u d' u' : ℕ}, d < 2^A → u < 2^L → (d ≠ 0 ∨ u ≠ 0) →
      d' < 2^A → u' < 2^L → d • x+u • y=0 → d' • x+u' • y=0 →
      d ≤ d' → u ≤ u' → d=d' ∧ u=u' := by
    intro d u d' u' hd hu hne hd' hu' hz hz' hdd huu
    by_contra hnot
    have hdiff : d'-d ≠ 0 ∨ u'-u ≠ 0 := by omega
    have hdz : (d'-d) • x+(u'-u) • y=0 :=
      zero_relation_of_ordered_rectangle_collision x y hdd huu (hz.trans hz'.symm)
    have hs := small_corner_of_nonzero_relation_of_valid_two_chains hd hu hne
      g hg x y hleft hright hz
    have hs' := small_corner_of_nonzero_relation_of_valid_two_chains
      (show d'-d < 2^A by omega) (show u'-u < 2^L by omega) hdiff
      g hg x y hleft hright hdz
    omega
  rcases rectangle_fibres_ordered_of_valid_two_chains hA hL g hg x y hleft hright
    hd hu hd' hu' (hz.trans hz'.symm) with h | h
  · exact aux hd hu hne hd' hu' hz hz' h.1 h.2
  · have he := aux hd' hu' hne' hd hu hz' hz h.1 h.2
    exact ⟨he.1.symm,he.2.symm⟩

/-- Five total coordinates already guarantee the rectangle-width
inequality needed for uniqueness; no arm-length cutoff remains. -/
theorem two_chain_rectangle_wide_of_five_le
    {A L : ℕ} (hn : 5 ≤ A+L) : 2*(A+L) ≤ (2^A-1)+(2^L-1) := by
  have base (t : ℕ) : 2*t ≤ 2^t := Nat.mul_le_pow (by decide) t
  have extra : ∀ t : ℕ, 3 ≤ t → 2*t+2 ≤ 2^t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => norm_num
    | succ t ht ih => rw [pow_succ']; omega
  rcases le_total 3 A with ha | ha
  · have h := extra A ha
    have h' := base L
    have hp : 0 < 2^L := by positivity
    omega
  · by_cases hA : A=3
    · have h := extra A (by omega)
      have h' := base L
      have hp : 0 < 2^L := by positivity
      omega
    · have h := extra L (by omega)
      have h' := base A
      have hp : 0 < 2^A := by positivity
      omega

/-- Remove the upper corner translated by the unique zero relation.
The remaining rectangle embeds in the actual group, so its entire
binary deficit is paid for by that one corner, not by many collisions. -/
theorem rectangle_card_bound_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    {d u : ℕ} (hd : d < 2^A) (hu : u < 2^L) (hne : d ≠ 0 ∨ u ≠ 0)
    (hz : d • x+u • y=0) :
    2^(A+L) ≤ Fintype.card G+(2^A-d)*(2^L-u) := by
  classical
  let B : Finset (ℕ × ℕ) := (range (2^A)) ×ˢ (range (2^L))
  let C : Finset (ℕ × ℕ) := (Ico d (2^A)) ×ˢ (Ico u (2^L))
  let f : ℕ × ℕ → G := fun p ↦ p.1 • x+p.2 • y
  have hCB : C ⊆ B := by
    intro p hp
    simp only [C,mem_product,mem_Ico] at hp
    exact mem_product.mpr ⟨mem_range.mpr hp.1.2,mem_range.mpr hp.2.2⟩
  have hw := two_chain_rectangle_wide_of_five_le hn
  have hfi : Set.InjOn f (↑(B \ C) : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    have hpb := (mem_sdiff.mp hp).1
    have hqb := (mem_sdiff.mp hq).1
    simp only [B,mem_product,mem_range] at hpb hqb
    have aux : ∀ p q : ℕ × ℕ, p ∈ B \ C → q ∈ B \ C → f p=f q →
        p.1 ≤ q.1 → p.2 ≤ q.2 → p=q := by
      intro p q hp hq he hpq hpq'
      by_contra hnot
      have hqb := (mem_sdiff.mp hq).1
      simp only [B,mem_product,mem_range] at hqb
      have hdiff : q.1-p.1 ≠ 0 ∨ q.2-p.2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hnot (Prod.ext (by omega) (by omega))
      have hzero := zero_relation_of_ordered_rectangle_collision x y hpq hpq' he
      have heq := unique_nonzero_rectangle_relation_of_valid_two_chains hA hL hw
        g hg x y hleft hright hd hu hne
        (show q.1-p.1 < 2^A by omega) (show q.2-p.2 < 2^L by omega) hdiff hz hzero
      apply (mem_sdiff.mp hq).2
      simp only [C,mem_product,mem_Ico]
      exact ⟨⟨by omega,hqb.1⟩,⟨by omega,hqb.2⟩⟩
    rcases rectangle_fibres_ordered_of_valid_two_chains hA hL g hg x y hleft hright
      hpb.1 hpb.2 hqb.1 hqb.2 he with h | h
    · exact aux p q hp hq he h.1 h.2
    · exact (aux q p hq hp he.symm h.1 h.2).symm
  have hc : (B \ C).card ≤ Fintype.card G := by
    rw [← card_image_of_injOn hfi]
    exact card_le_univ _
  rw [card_sdiff_of_subset hCB] at hc
  simp only [B,C,card_product,card_range,Nat.card_Ico,← pow_add] at hc
  omega

/-- Actual subbinary two-chain data force a single small corner paying
for the whole group-cardinality deficit, with a dyadic side. Axial
relations are included: their unremoved side is itself a binary range. -/
theorem exists_deficit_corner_of_valid_subbinary_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L)) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ 2^A ∧ 0 < b ∧ b ≤ 2^L ∧
      a+b ≤ A+L+1 ∧ 2^(A+L) ≤ Fintype.card G+a*b ∧
      ((∃ e, a=2^e) ∨ ∃ f, b=2^f) ∧
      (2^A-a) • x+(2^L-b) • y=0 := by
  obtain ⟨d,u,hd,hu,hne,hz,hs⟩ :=
    exists_nonzero_rectangle_relation_of_valid_two_chains hA hL g hg x y hleft hright hcard
  have hb := rectangle_card_bound_of_valid_two_chains hA hL hn g hg x y hleft hright hd hu hne hz
  refine ⟨2^A-d,2^L-u,by omega,Nat.sub_le _ _,by omega,Nat.sub_le _ _,hs,hb,?_,?_⟩
  · by_cases hd0 : d=0
    · exact Or.inl ⟨A,by simp [hd0]⟩
    · by_cases hu0 : u=0
      · exact Or.inr ⟨L,by simp [hu0]⟩
      · exact power_deficit_of_zero_relation_of_valid_two_chains hA hL
          (Nat.pos_of_ne_zero hd0) hd (Nat.pos_of_ne_zero hu0) hu g hg x y hleft hright hz
  · simpa only [Nat.sub_sub_self hd.le,Nat.sub_sub_self hu.le] using hz

/-- A uniform near-binary lower bound for actual two chains in ANY
finite abelian group. This is weaker than the conjectured cyclic bound,
but removes a quadratic, not exponential, deficit in all dimensions. -/
theorem near_binary_card_bound_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y) :
    4*2^(A+L) ≤ 4*Fintype.card G+(A+L+1)^2 := by
  by_cases hc : Fintype.card G < 2^(A+L)
  · obtain ⟨a,b,_,_,_,_,hs,hb,_,_⟩ :=
      exists_deficit_corner_of_valid_subbinary_two_chains hA hL hn g hg x y hleft hright hc
    have hsquare : (a+b)^2 ≤ (A+L+1)^2 := Nat.pow_le_pow_left hs 2
    have hab : 4*a*b ≤ (a+b)^2 := by nlinarith [sq_nonneg ((a:ℤ)-(b:ℤ))]
    nlinarith
  · omega

/-- Actual affine/reindexed two chains inherit the extracted corner,
including its seed relation and full deficit payment. -/
theorem exists_deficit_corner_of_valid_affine_subbinary_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (c x y : G)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+c=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+c=2^i.val • y)
    (hcard : Fintype.card G < 2^(A+L)) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ 2^A ∧ 0 < b ∧ b ≤ 2^L ∧
      a+b ≤ A+L+1 ∧ 2^(A+L) ≤ Fintype.card G+a*b ∧
      ((∃ e, a=2^e) ∨ ∃ f, b=2^f) ∧
      (2^A-a) • x+(2^L-b) • y=0 := by
  have hv : ValidTuple (fun i ↦ g (E i)+c) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-c)
  exact exists_deficit_corner_of_valid_subbinary_two_chains hA hL hn _ hv x y hleft hright hcard

/-- The uniform near-binary group bound applies to the original tuple,
with its affine offset and permutation retained as actual data. -/
theorem near_binary_card_bound_of_valid_affine_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (A+L) → G) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (c x y : G)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+c=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+c=2^i.val • y) :
    4*2^(A+L) ≤ 4*Fintype.card G+(A+L+1)^2 := by
  have hv : ValidTuple (fun i ↦ g (E i)+c) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-c)
  exact near_binary_card_bound_of_valid_two_chains hA hL hn _ hv x y hleft hright

end MinModulus
