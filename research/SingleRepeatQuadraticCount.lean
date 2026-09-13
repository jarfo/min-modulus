import research.QuarticCollisionBounds

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The quadratic counting inequality is exact at fibre sizes two and
three, and valid at every size. No tuple validity is needed. -/
theorem two_single_repeat_incidence_le_three_values_add_pair_collisions
    {n N k : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (Y : Finset (ZMod N)) :
    2*(∑ x ∈ Y, (singleRepeatFibre g k x).card) ≤
      3*((repeatedCoinCover g (k+2)) ∩ Y).card +
        ∑ x ∈ Y, ((singleRepeatFibre g k x).card).choose 2 := by
  classical
  have hnum (r : ℕ) : 2*r ≤ 3+r.choose 2 := by
    rcases r with _ | r
    · simp
    rcases r with _ | r
    · simp
    rw [Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    omega
  have hpoint (x : ZMod N) : 2*(singleRepeatFibre g k x).card ≤
      3*(if x ∈ repeatedCoinCover g (k+2) then 1 else 0) +
        ((singleRepeatFibre g k x).card).choose 2 := by
    by_cases hx : x ∈ repeatedCoinCover g (k+2)
    · simpa only [if_pos hx,mul_one] using hnum (singleRepeatFibre g k x).card
    · have hz : singleRepeatFibre g k x=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hx (mem_repeatedCoinCover_of_single_repeat g x a ha)
      simp [hz]
  have hocc : (∑ x ∈ Y, (if x ∈ repeatedCoinCover g (k+2) then 1 else 0)) =
      ((repeatedCoinCover g (k+2)) ∩ Y).card := by
    calc
      _ = (Y.filter (fun x ↦ x ∈ repeatedCoinCover g (k+2))).card := by
        simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      _ = _ := by
        congr 1
        ext x
        simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
  calc
    _ = ∑ x ∈ Y, 2*(singleRepeatFibre g k x).card := Finset.mul_sum ..
    _ ≤ ∑ x ∈ Y, (3*(if x ∈ repeatedCoinCover g (k+2) then 1 else 0) +
        ((singleRepeatFibre g k x).card).choose 2) :=
      Finset.sum_le_sum (fun x _ ↦ hpoint x)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hocc]

/-- The stronger quadratic incidence bound applies in every even degree. -/
theorem single_repeat_outside_doubled_cover_quadratic_count
    {n N k : ℕ} [NeZero N] (hk : 1 ≤ k) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    let E := (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x)
    2*((n-(2*k+2))*n.choose (2*k)) ≤
      3*((repeatedCoinCover g (2*k+2)) \ E).card +
        ∑ x ∈ Eᶜ, ((singleRepeatFibre g (2*k) x).card).choose 2 := by
  classical
  intro E
  have hlo := single_repeat_outside_doubled_cover_incidence_lower_bound hk hN g hg
  have hhi := two_single_repeat_incidence_le_three_values_add_pair_collisions g Eᶜ (k := 2*k)
  have heq : (repeatedCoinCover g (2*k+2)) ∩ Eᶜ =
      (repeatedCoinCover g (2*k+2)) \ E := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_compl,Finset.mem_sdiff]
  rw [heq] at hhi
  exact (Nat.mul_le_mul_left 2 hlo).trans hhi

/-- A weaker explicit sparsity condition suffices for the outside quartic
count when using the quadratic inequality exact at sizes two and three. -/
theorem quartic_outside_card_of_quadratic_sparsity
    {n N : ℕ} [NeZero N] (hn : 12 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsparse : (n-9)*(disjointDoubledDifferencePairs g).card ≤
      (n-12)*n.choose 2) :
    n.choose 3 ≤ ((repeatedCoinCover g 4) \
      (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)).card := by
  classical
  let E := (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)
  have hinj : ∀ u v : ZMod N, u+u=v+v → u=v := by
    intro u v he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [Nat.cast_ofNat,two_mul] using he
  have hlo := single_repeat_outside_doubled_cover_quadratic_count (k := 1)
    (by decide) hN g hg
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at hlo
  have hhi := quartic_pair_collision_sum_le hinj g hg (by omega) Eᶜ
  have hcombined := hlo.trans (Nat.add_le_add_left hhi
    (3*((repeatedCoinCover g 4) \ E).card))
  have hfour : n-4+4=n := by omega
  have htwelve : n-12+12=n := by omega
  have htwo : n-2+2=n := by omega
  have hchoose := Nat.choose_succ_right_eq n 2
  change n.choose 3*3=n.choose 2*(n-2) at hchoose
  change n.choose 3 ≤ ((repeatedCoinCover g 4) \ E).card
  nlinarith

/-- The quadratic collision inequality yields the absolute quartic
bound under its weaker, explicitly stated sparsity hypothesis. -/
theorem absolute_quartic_bound_of_quadratic_sparsity
    {n N : ℕ} [NeZero N] (hn : 12 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsparse : (n-9)*(disjointDoubledDifferencePairs g).card ≤
      (n-12)*n.choose 2) :
    (n+1).choose 2+n.choose 3 ≤ (repeatedCoinCover g 4).card := by
  classical
  let E := (actualFibreCoinCover g 2).image (fun x ↦ 2 • x)
  have hsub : E ⊆ repeatedCoinCover g 4 :=
    doubled_coin_cover_subset_repeated_coin_cover (k := 2) (by decide) g
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro a b he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using he
  have hE : E.card=(n+1).choose 2 := by
    rw [Finset.card_image_of_injective _ hd,two_coin_card_eq_of_odd hN g hg]
  have hout := quartic_outside_card_of_quadratic_sparsity hn hN g hg hsparse
  change n.choose 3 ≤ ((repeatedCoinCover g 4) \ E).card at hout
  rw [Finset.card_sdiff_of_subset hsub] at hout
  have hcard := Finset.card_le_card hsub
  omega

end MinModulus.Research
