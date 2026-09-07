import MinModulus.FewEscapeCycleBudget

/-! General binary-rectangle restrictions extracted from valid actual
two-chain tuples. These do not assume, or establish, a full chain/fork
classification of arbitrary multi-escape tuples. -/

namespace MinModulus
open Finset

/-- A positive shift below one binary range costs at most one extra
coin beyond the chain length. The endpoint one below the next all-ones
weight is essential. -/
theorem exists_binary_rep_all_ones_add_small
    {A d : ℕ} (hA : 0 < A) (hd : d < 2^A) :
    ∃ u, Supp A u ∧ val A u=2^A-1+d ∧ dsum A u ≤ A+1 := by
  by_cases hA1 : A=1
  · subst A
    refine ⟨fun i ↦ if i=0 then 1+d else 0,?_,?_,?_⟩
    · intro i hi; simp [show i ≠ 0 by omega]
    · simp [val]
    · simp [dsum]; omega
  · have hw : 0 < A-1 := by omega
    have hform : A-1+1=A := by omega
    have hpow : 2^A=2*2^(A-1) := by
      calc
        2^A=2^((A-1)+1) := congrArg (fun t ↦ 2^t) hform.symm
        _=_ := pow_succ' 2 (A-1)
    obtain ⟨u,hs,hu,hdu⟩ := exists_binary_rep_below_top_multiple_sub_one
      (w := A-1) (c := 4) hw (by omega) (show 2^A-1+d < 4*2^(A-1)-1 by omega)
    refine ⟨u,?_,?_,?_⟩
    · simpa only [hform] using hs
    · simpa only [hform] using hu
    · rw [hform] at hdu
      omega

/-- Opposite two-chain weight shifts preserve the actual tuple sum
whenever the corresponding bounded positive seed multiples agree. -/
theorem two_chain_opposite_shift_sum_identities
    {X Y d u : ℕ} (hd : d ≤ X) (hu : u ≤ Y)
    {G : Type*} [AddCommGroup G] (x y : G) (hrel : d • x=u • y) :
    ((X+d) • x+(Y-u) • y=X • x+Y • y) ∧
      ((X-d) • x+(Y+u) • y=X • x+Y • y) := by
  have hX : (X-d) • x+d • x=X • x := by rw [← add_nsmul,Nat.sub_add_cancel hd]
  have hY : (Y-u) • y+u • y=Y • y := by rw [← add_nsmul,Nat.sub_add_cancel hu]
  constructor
  · rw [add_nsmul,hrel,← hY]
    abel
  · rw [add_nsmul,← hrel,← hX]
    abel

/-- ANY positive relation inside the two binary ranges contradicts
validity. Both opposite shifts fit the coin budget, and one necessarily
has enough total integer weight for full-length refinement. No merge,
unit, cyclicity, modulus, or arm-size comparison is assumed. -/
theorem positive_bounded_seed_relation_ne_of_valid_two_chains
    {A L d u : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hd : 0 < d) (hdA : d < 2^A) (hu : 0 < u) (huL : u < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y) : d • x ≠ u • y := by
  intro hrel
  have hAp : 0 < 2^A := by positivity
  have hLp : 0 < 2^L := by positivity
  obtain ⟨hsum1,hsum2⟩ := two_chain_opposite_shift_sum_identities
    (show d ≤ 2^A-1 by omega) (show u ≤ 2^L-1 by omega) x y hrel
  obtain ⟨p,_,hp,hdp⟩ := exists_binary_rep_all_ones_add_small hA hdA
  obtain ⟨q,_,hq,hdq⟩ := exists_rep_lt L (2^L-1-u) (by omega)
  obtain ⟨p',_,hp',hdp'⟩ := exists_rep_lt A (2^A-1-d) (by omega)
  obtain ⟨q',_,hq',hdq'⟩ := exists_binary_rep_all_ones_add_small hL huL
  by_cases hw : A+L ≤ (2^A-1+d)+(2^L-1-u)
  · exact not_validTuple_of_two_chain_integer_weights g x y hleft hright p q hp hq
      (by omega) hw (by omega) hsum1 hg
  · have hbase : A+L ≤ (2^A-1)+(2^L-1) := by
      have h1 := Nat.lt_two_pow_self (n := A)
      have h2 := Nat.lt_two_pow_self (n := L)
      omega
    have hw' : A+L ≤ (2^A-1-d)+(2^L-1+u) := by omega
    exact not_validTuple_of_two_chain_integer_weights g x y hleft hright p' q' hp' hq'
      (by omega) hw' (by omega) hsum2 hg

/-- A bounded positive zero-sum relation can only remove almost the
entire binary weight rectangle: its complementary weights sum to less
than the tuple length. -/
theorem small_complement_of_zero_relation_of_valid_two_chains
    {A L d u : ℕ} (hd : 0 < d) (hdA : d < 2^A) (huL : u < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : d • x+u • y=0) : (2^A-1-d)+(2^L-1-u) < A+L := by
  have hAp : 0 < 2^A := by positivity
  have hLp : 0 < 2^L := by positivity
  have hX : (2^A-1-d) • x+d • x=(2^A-1) • x := by
    rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
  have hY : (2^L-1-u) • y+u • y=(2^L-1) • y := by
    rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
  have hsum : (2^A-1-d) • x+(2^L-1-u) • y=(2^A-1) • x+(2^L-1) • y := by
    rw [← hX,← hY]
    calc
      _=((2^A-1-d) • x+(2^L-1-u) • y)+(d • x+u • y) := by rw [hrel,add_zero]
      _=_ := by abel
  by_contra hnot
  exact not_validTuple_of_two_chain_small_integer_weights g x y hleft hright
    (by omega) (by omega) (by omega) (by omega) hsum hg

/-- Add one complete binary range using exactly two top coins. -/
theorem exists_binary_rep_add_two_top_coins
    {A : ℕ} (hA : 0 < A) (u : ℕ → ℕ) (hs : Supp A u) :
    ∃ v, Supp A v ∧ val A v=val A u+2^A ∧ dsum A v=dsum A u+2 := by
  let v : ℕ → ℕ := fun i ↦ u i+(if i=A-1 then 2 else 0)
  have ht : A-1 < A := by omega
  have hpow : 2*2^(A-1)=2^A := by
    rw [← pow_succ',show A-1+1=A by omega]
  refine ⟨v,?_,?_,?_⟩
  · intro i hi
    simp only [v,hs i hi,if_neg (show i ≠ A-1 by omega),add_zero]
  · simp only [v,val,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_range,if_pos ht,hpow]
  · simp only [v,dsum,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_range,if_pos ht]

/-- A non-power deficit saves the two coins needed to add a complete
range. Thus the far-side complementary weight still fits one chain. -/
theorem exists_binary_rep_double_range_sub_nonpower
    {A a : ℕ} (hA : 0 < A) (ha : 0 < a) (haA : a < 2^A)
    (hpow : ¬ ∃ e, a=2^e) :
    ∃ u, Supp A u ∧ val A u=2^A+(2^A-1-a) ∧ dsum A u ≤ A := by
  have hA2 : 2 ≤ A := by
    by_contra h
    have hA1 : A=1 := by omega
    have hbound : a < 2 := by simpa only [hA1,pow_one] using haA
    have ha1 : a=1 := by omega
    exact hpow ⟨0,by simp [ha1]⟩
  obtain ⟨u,hs,hu,hdu⟩ := exists_rep_compl A a haA (by omega) hpow
  obtain ⟨v,hv,hval,hcard⟩ := exists_binary_rep_add_two_top_coins hA u hs
  refine ⟨v,hv,?_,?_⟩
  · rw [hval,hu,Nat.add_comm]
  · omega

/-- Every interior zero relation has a POWER-OF-TWO corner deficit
in at least one coordinate. If both deficits were non-powers, two
complement savings would pay for a full-length far-side rival. -/
theorem power_deficit_of_zero_relation_of_valid_two_chains
    {A L d u : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hd : 0 < d) (hdA : d < 2^A) (hu : 0 < u) (huL : u < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : d • x+u • y=0) :
    (∃ e, 2^A-d=2^e) ∨ ∃ f, 2^L-u=2^f := by
  by_contra hnot
  push Not at hnot
  have hpa : ¬ ∃ e, 2^A-d=2^e := by simpa using hnot.1
  have hpb : ¬ ∃ f, 2^L-u=2^f := by simpa using hnot.2
  obtain ⟨p,_,hp,hdp⟩ := exists_binary_rep_double_range_sub_nonpower hA
    (show 0 < 2^A-d by omega) (show 2^A-d < 2^A by omega) hpa
  obtain ⟨q,_,hq,hdq⟩ := exists_binary_rep_double_range_sub_nonpower hL
    (show 0 < 2^L-u by omega) (show 2^L-u < 2^L by omega) hpb
  have hp' : val A p=2^A-1+d := hp.trans (by omega)
  have hq' : val L q=2^L-1+u := hq.trans (by omega)
  have hsum : (2^A-1+d) • x+(2^L-1+u) • y=(2^A-1) • x+(2^L-1) • y := by
    simp only [add_nsmul]
    calc
      _=((2^A-1) • x+(2^L-1) • y)+(d • x+u • y) := by abel
      _=_ := by rw [hrel,add_zero]
  have hhigh : A+L ≤ (2^A-1+d)+(2^L-1+u) := by
    have h1 := Nat.lt_two_pow_self (n := A)
    have h2 := Nat.lt_two_pow_self (n := L)
    omega
  exact not_validTuple_of_two_chain_integer_weights g x y hleft hright p q hp' hq'
    (by omega) hhigh (by omega) hsum hg

/-- Affine/reindexed actual two-chain data inherit the small corner
and dyadic-deficit constraints. These are extracted patterns for the
acyclic multi-escape problem, not a new conjectural input. -/
theorem corner_constraints_of_zero_relation_of_valid_affine_two_chains
    {A L d u : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hd : 0 < d) (hdA : d < 2^A) (hu : 0 < u) (huL : u < 2^L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b x y : G)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hrel : d • x+u • y=0) :
    (2^A-d)+(2^L-u) ≤ A+L+1 ∧
      ((∃ e, 2^A-d=2^e) ∨ ∃ f, 2^L-u=2^f) := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  refine ⟨?_,power_deficit_of_zero_relation_of_valid_two_chains hA hL hd hdA hu huL
    _ hv x y hleft hright hrel⟩
  have hsmall := small_complement_of_zero_relation_of_valid_two_chains hd hdA huL _ hv x y hleft hright hrel
  omega

/-- Fibres of the full binary weight rectangle are coordinatewise
ordered. A crossed collision would be a forbidden bounded positive
seed relation. This supplies a general cyclic-packing restriction
without assuming a particular collision or a unit normalization. -/
theorem rectangle_fibres_ordered_of_valid_two_chains
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    {X Y X' Y' : ℕ} (hX : X < 2^A) (hY : Y < 2^L)
    (hX' : X' < 2^A) (hY' : Y' < 2^L)
    (heq : X • x+Y • y=X' • x+Y' • y) :
    (X ≤ X' ∧ Y ≤ Y') ∨ (X' ≤ X ∧ Y' ≤ Y) := by
  have aux : ∀ {X Y X' Y' : ℕ}, X < 2^A → Y < 2^L → X' < 2^A → Y' < 2^L →
      X • x+Y • y=X' • x+Y' • y → X < X' → Y ≤ Y' := by
    intro X Y X' Y' _ hY hX' _ heq hXX
    by_contra hYY
    have hdx : X • x+(X'-X) • x=X' • x := by rw [← add_nsmul,Nat.add_sub_of_le (by omega)]
    have huy : Y' • y+(Y-Y') • y=Y • y := by rw [← add_nsmul,Nat.add_sub_of_le (by omega)]
    have hrel : (X'-X) • x=(Y-Y') • y := by
      apply add_left_cancel (a := X • x+Y' • y)
      calc
        _=X' • x+Y' • y := by rw [← hdx]; abel
        _=X • x+Y • y := heq.symm
        _=_ := by rw [← huy]; abel
    exact positive_bounded_seed_relation_ne_of_valid_two_chains hA hL
      (show 0 < X'-X by omega) (show X'-X < 2^A by omega)
      (show 0 < Y-Y' by omega) (show Y-Y' < 2^L by omega) g hg x y hleft hright hrel
  rcases lt_trichotomy X X' with hlt | he | hgt
  · exact Or.inl ⟨hlt.le,aux hX hY hX' hY' heq hlt⟩
  · rcases le_total Y Y' with hy | hy
    · exact Or.inl ⟨he.le,hy⟩
    · exact Or.inr ⟨he.ge,hy⟩
  · exact Or.inr ⟨hgt.le,aux hX' hY' hX hY heq.symm hgt⟩

end MinModulus
