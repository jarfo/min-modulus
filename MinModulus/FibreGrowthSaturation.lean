import MinModulus.FibreMultiplicityGrowth
import MinModulus.TripleFibreCorrectionParity

namespace MinModulus
open Finset
open scoped Classical

/-- Separated integer weights in a closed interval consume one full
step for each point after the first. -/
theorem separated_weight_card_bound {α : Type*} (S : Finset α) (w : α → ℕ)
    (a c D : ℕ) (hD : 0 < D) (hac : a ≤ c)
    (hlo : ∀ x ∈ S, a ≤ w x) (hhi : ∀ x ∈ S, w x ≤ c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → w x+D ≤ w y ∨ w y+D ≤ w x) :
    (S.card-1)*D+a ≤ c := by
  classical
  have hinj := Finset.card_le_card_of_injOn (s:=S) (t:=Finset.range ((c-a)/D+1))
    (fun x ↦ (w x-a)/D) (by
      intro x hx
      apply Finset.mem_range.mpr
      change (w x-a)/D < (c-a)/D+1
      have h := Nat.div_le_div_right (Nat.sub_le_sub_right (hhi x hx) a) (c:=D)
      omega) (by
      intro x hx y hy heq
      change (w x-a)/D=(w y-a)/D at heq
      by_contra hne
      have hstep {x y : α} (hx : x ∈ S) (hy : y ∈ S) (h : w x+D ≤ w y) :
          (w x-a)/D < (w y-a)/D := by
        have hsub : (w x-a)+D ≤ w y-a := by have := hlo x hx; omega
        have hh := Nat.div_le_div_right hsub (c:=D)
        rw [Nat.add_div_right _ hD] at hh
        omega
      rcases hsep x hx y hy hne with h | h
      · have hh := hstep hx hy h; omega
      · have hh := hstep hy hx h; omega)
  rw [Finset.card_range] at hinj
  have hp : (S.card-1)*D ≤ c-a :=
    (Nat.le_div_iff_mul_le hD).mp (Nat.sub_le_of_le_add hinj)
  omega

/-- A lower bound on all subset weights in a nonempty fibre strengthens
the global growth bound by that entire lower weight. -/
theorem fibre_growth_bound_with_weight_floor
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (a : ℕ) (ha : a ≤ ∑ i, 2^(r i))
    (hlo : ∀ U : Finset (Fin n), (∑ i ∈ U, (g i+b))=z → a ≤ ∑ i ∈ U, 2^(r i)) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1)+a ≤ ∑ i, 2^(r i) := by
  apply separated_weight_card_bound _ (fun U ↦ ∑ i ∈ U, 2^(r i)) a _ _ (by omega) ha
  · intro U hU
    exact hlo U (Finset.mem_filter.mp hU).2
  · intro U _
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ Nat.zero_le _)
  · intro U hU V hV hne
    have he := (Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm
    rcases lt_trichotomy U.card V.card with h | h | h
    · exact Or.inl (ranked_weight_separation_of_unequal_collision g hg b r hp V U he.symm h)
    · exact (hne (tuple_subset_fibre_cardinality_injective g hg b z hU hV h)).elim
    · exact Or.inr (ranked_weight_separation_of_unequal_collision g hg b r hp U V he h)

/-- Every nonzero fibre leaves strict slack in the global weight bound. -/
theorem fibre_growth_bound_strict_of_value_ne_zero
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hn : 0 < n) (hz : z ≠ 0) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1) < ∑ i, 2^(r i) := by
  have hbase := dimension_le_total_ranked_weight r
  have h := fibre_growth_bound_with_weight_floor g hg b z r hp 1 (by omega) (by
    intro U hU
    have hne : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      simp only [he,Finset.sum_empty] at hU
      exact hz hU.symm
    have hpos : 0 < ∑ i ∈ U, 2^(r i) :=
      Finset.sum_pos (fun _ _ ↦ pow_pos (by decide : 0 < (2 : ℕ)) _) hne
    omega)
  omega

/-- Saturation forces both endpoint subsets into the fibre: its value
and the total shifted sum must both be zero. -/
theorem zero_value_and_total_of_fibre_growth_saturation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hn : 0 < n)
    (heq : ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1)=∑ i, 2^(r i)) :
    z=0 ∧ (∑ i, (g i+b))=0 := by
  have hz : z=0 := by
    by_contra h
    have hh := fibre_growth_bound_strict_of_value_ne_zero g hg b z r hp hn h
    omega
  refine ⟨hz,?_⟩
  by_contra htotal
  have hne : (∑ i, (g i+b))-z ≠ 0 := by simpa only [hz,sub_zero] using htotal
  have hh := fibre_growth_bound_strict_of_value_ne_zero g hg b ((∑ i, (g i+b))-z) r hp hn hne
  have hc := tuple_binary_fibre_card_eq_complementary_value g b z
  rw [← hc] at hh
  omega

/-- A saturated fibre has even cardinality, by complementation at zero. -/
theorem even_fibre_card_of_growth_saturation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hn : 0 < n)
    (heq : ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1)=∑ i, 2^(r i)) :
    Even (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by
  obtain ⟨hz,ht⟩ := zero_value_and_total_of_fibre_growth_saturation g hg b z r hp hn heq
  exact even_tuple_binary_midpoint_fibre_card hn g b z (by simp [hz,ht])

/-- An odd fibre never saturates the predecessor-weight bound. -/
theorem fibre_growth_bound_strict_of_odd_card
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hn : 0 < n)
    (hodd : Odd (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1) < ∑ i, 2^(r i) := by
  have hle := fibre_card_sub_one_mul_growth_step_le_total_weight g hg b z r hp
  apply lt_of_le_of_ne hle
  intro heq
  have heven := Nat.even_iff.mp (even_fibre_card_of_growth_saturation g hg b z r hp hn heq)
  have ho := Nat.odd_iff.mp hodd
  omega

/-- Complement parity rules out the previously possible equality in
the total-weight bound for every fibre of size at least three. -/
theorem total_ranked_weight_add_three_le_twice_dimension_of_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (htriple : 3 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    (∑ i, 2^(r i))+3 ≤ 2*n := by
  have hbase := dimension_le_total_ranked_weight r
  have hbound := total_ranked_weight_add_two_le_twice_dimension_of_triple_fibre g hg b z r hp htriple
  have hn : 0 < n := by omega
  have hf := fibre_card_sub_one_mul_growth_step_le_total_weight g hg b z r hp
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  let W := ∑ i, 2^(r i)
  let D := W-n+1
  change 3 ≤ m at htriple
  change (m-1)*D ≤ W at hf
  change W+3 ≤ 2*n
  change W+2 ≤ 2*n at hbound
  change n ≤ W at hbase
  by_contra h
  have he : W+2=2*n := by omega
  have hD : 0 < D := by dsimp [D]; omega
  have hWD : W=2*D := by dsimp [D]; omega
  have hm : m=3 := by
    have hm1 : m-1+1=m := by omega
    nlinarith [hf]
  have hodd : Odd (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by
    change Odd m
    rw [hm]
    decide
  have hs := fibre_growth_bound_strict_of_odd_card g hg b z r hp hn hodd
  change (m-1)*D < W at hs
  rw [hm] at hs
  norm_num at hs
  omega

/-- The total-weight test for two-point fibres now includes equality. -/
theorem subset_fibre_card_le_two_of_total_ranked_weight_ge
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hweight : 2*n ≤ (∑ i, 2^(r i))+2) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have hh := total_ranked_weight_add_three_le_twice_dimension_of_triple_fibre g hg b z r hp (by omega)
  omega

/-- Exact collision-core accounting also extends to the former
aggregate-weight equality boundary. -/
theorem intrinsic_loss_eq_core_cube_sum_of_total_ranked_weight_ge
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hweight : 2*n ≤ (∑ i, 2^(r i))+2) :
    tupleBinaryCollisionLoss g b=∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_total_ranked_weight_ge g hg b r hp hweight)

end MinModulus
