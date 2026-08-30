/-
# The quadratic wedge: `m(m-1) ≤ 6(|G| - 2^m + m + 14)`

Second rung of the wedge program (see `OddOrder.lean` for the linear wedge
`bottom_wedge`).  A dissociated family `h : Fin m → G` with injective doubling
and no single-headed witness of head `2` or `3` ("SHC") is studied through the
action of `τ = 2 • h x` on the set `H₂` of pair sums `h y + h z`.

* `survival22`: two distinct disjoint `(2,2)`-representations of one value
  must satisfy `|M₁ ∩ P₂| + |M₂ ∩ P₁| ≥ 2`, else their difference is a
  single-headed or `±1` witness;
* `cluster22`: a pairwise-surviving family of such representations has at
  most `13` members (the paper proof gives `7`);
* the charging argument: every pair sum reaches, within two `τ`-steps, either
  a jump (a disjoint `(2,2)`-representation of `τ`) or an escape from `H₂`;
  jumps number at most `13`, escapes at most `m + (|G| - 2^m) + 1`.

Result: `m(m-1) ≤ 6·(m + (|G| - 2^m) + 14)`, so no SHC family exists in odd
order `2^m + r` once `r < m(m-1)/6 - m - 14`.
-/
import MinModulus.OddOrder

namespace MinModulus

open Finset

section QuadraticWedge

variable {G : Type*} [AddCommGroup G] {m : ℕ}

/-- The SHC hypotheses bundled: dissociation, no single-head-2 witness, no
single-head-3 witness, injective doubling. -/
structure SHC (h : Fin m → G) : Prop where
  inj2 : ∀ x y : G, x + x = y + y → x = y
  dis : Function.Injective fun S : Finset (Fin m) => ∑ j ∈ S, h j
  sh2 : ∀ (x : Fin m) (P M : Finset (Fin m)), x ∉ P → x ∉ M → Disjoint P M →
    P.card + 1 ≤ M.card → 2 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j
  sh3 : ∀ (x : Fin m) (P M : Finset (Fin m)), x ∉ P → x ∉ M → Disjoint P M →
    P.card + 2 ≤ M.card → 3 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j

/-- Validity of an anchored tuple implies the SHC conditions for its translated
differences.  This is the bridge from the original min-modulus problem to the
linear and quadratic wedge theorems: dissociation is `ssum_injective`, while a
forbidden head-`2` or head-`3` relation pads at the anchor to a zero witness. -/
theorem shc_diff_of_valid (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hinj2 : ∀ x y : G, x + x = y + y → x = y) : SHC (diff g) := by
  refine ⟨hinj2, ssum_injective g hg, ?_, ?_⟩
  · intro x P M hxP hxM hPM hcard heq
    refine validTuple_no_diff_relation g hg
      (d := fun j => (if j = x then 2 else 0) + (if j ∈ P then 1 else 0)
        - (if j ∈ M then 1 else 0)) ?_ ?_ ?_ ?_
    · intro h0
      have h1 := congrFun h0 x
      simp [hxP, hxM] at h1
    · intro j
      show (-1 : ℤ) ≤ (if j = x then 2 else 0) + (if j ∈ P then 1 else 0)
        - (if j ∈ M then 1 else 0)
      split_ifs <;> omega
    · have hsum :
          (∑ j, ((if j = x then (2 : ℤ) else 0) + (if j ∈ P then 1 else 0)
            - (if j ∈ M then 1 else 0))) = 2 + (P.card : ℤ) - (M.card : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' univ x fun _ => (2 : ℤ)]
        simp
      rw [hsum]
      have hcard' : (P.card : ℤ) + 1 ≤ (M.card : ℤ) := by exact_mod_cast hcard
      omega
    · have hterm : ∀ j,
          ((if j = x then (2 : ℤ) else 0) + (if j ∈ P then 1 else 0)
            - (if j ∈ M then 1 else 0)) • diff g j
          = ((if j = x then (2 : ℤ) else 0) • diff g j
              + (if j ∈ P then (1 : ℤ) else 0) • diff g j)
            - (if j ∈ M then (1 : ℤ) else 0) • diff g j := by
          intro j
          rw [sub_smul, add_smul]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, sum_single_smul, sum_indicator_smul,
        sum_indicator_smul]
      have heq' : (2 : ℤ) • diff g x + ∑ j ∈ P, diff g j = ∑ j ∈ M, diff g j := by
        simpa [two_zsmul, two_nsmul] using heq
      rw [heq', sub_self]
  · intro x P M hxP hxM hPM hcard heq
    refine validTuple_no_diff_relation g hg
      (d := fun j => (if j = x then 3 else 0) + (if j ∈ P then 1 else 0)
        - (if j ∈ M then 1 else 0)) ?_ ?_ ?_ ?_
    · intro h0
      have h1 := congrFun h0 x
      simp [hxP, hxM] at h1
    · intro j
      show (-1 : ℤ) ≤ (if j = x then 3 else 0) + (if j ∈ P then 1 else 0)
        - (if j ∈ M then 1 else 0)
      split_ifs <;> omega
    · have hsum :
          (∑ j, ((if j = x then (3 : ℤ) else 0) + (if j ∈ P then 1 else 0)
            - (if j ∈ M then 1 else 0))) = 3 + (P.card : ℤ) - (M.card : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' univ x fun _ => (3 : ℤ)]
        simp
      rw [hsum]
      have hcard' : (P.card : ℤ) + 2 ≤ (M.card : ℤ) := by exact_mod_cast hcard
      omega
    · have hterm : ∀ j,
          ((if j = x then (3 : ℤ) else 0) + (if j ∈ P then 1 else 0)
            - (if j ∈ M then 1 else 0)) • diff g j
          = ((if j = x then (3 : ℤ) else 0) • diff g j
              + (if j ∈ P then (1 : ℤ) else 0) • diff g j)
            - (if j ∈ M then (1 : ℤ) else 0) • diff g j := by
          intro j
          rw [sub_smul, add_smul]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, sum_single_smul, sum_indicator_smul,
        sum_indicator_smul]
      have heq' : (3 : ℤ) • diff g x + ∑ j ∈ P, diff g j = ∑ j ∈ M, diff g j := by
        have hthree : (3 : ℤ) • diff g x = diff g x + (diff g x + diff g x) := by
          calc
            (3 : ℤ) • diff g x = ((1 : ℤ) + 2) • diff g x := by norm_num
            _ = (1 : ℤ) • diff g x + (2 : ℤ) • diff g x := by rw [add_zsmul]
            _ = diff g x + (diff g x + diff g x) := by rw [one_zsmul, two_zsmul]
        rw [hthree]
        simpa [three_nsmul] using heq
      rw [heq', sub_self]

/-- The linear wedge stated directly for a valid tuple. -/
theorem bottom_wedge_of_valid [Fintype G] (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (hinj2 : ∀ x y : G, x + x = y + y → x = y) :
    2 ^ (m + 1) + m ≤ 2 * Fintype.card G + 2 := by
  have hs := shc_diff_of_valid g hg hinj2
  exact bottom_wedge (diff g) hs.inj2 hs.dis hs.sh2 hs.sh3

variable {h : Fin m → G}

/-- Subset sums of two disjoint sets add. -/
private lemma sum_union_disj (S T : Finset (Fin m)) (hST : Disjoint S T) :
    (∑ j ∈ S ∪ T, h j) = (∑ j ∈ S, h j) + ∑ j ∈ T, h j :=
  Finset.sum_union hST

/-- **Survival lemma.**  Two distinct disjoint `(2,2)`-representations
`(M₁,P₁), (M₂,P₂)` of one value satisfy `|M₁ ∩ P₂| + |M₂ ∩ P₁| ≥ 2`:
otherwise `σ M₁ + σ P₂ = σ M₂ + σ P₁` is a cube collision (no common element)
or, with a single common element `u`, the single-double witness
`2 • h u + σ(rest) = σ(M₂ ∪ P₁)`. -/
theorem survival22 (hs : SHC h) {v : G} {M₁ P₁ M₂ P₂ : Finset (Fin m)}
    (hM₁ : M₁.card = 2) (hP₁ : P₁.card = 2) (hM₂ : M₂.card = 2) (hP₂ : P₂.card = 2)
    (hd₁ : Disjoint M₁ P₁) (hd₂ : Disjoint M₂ P₂)
    (hv₁ : (∑ j ∈ M₁, h j) - ∑ j ∈ P₁, h j = v)
    (hv₂ : (∑ j ∈ M₂, h j) - ∑ j ∈ P₂, h j = v)
    (hne : M₁ ≠ M₂ ∨ P₁ ≠ P₂) :
    2 ≤ (M₁ ∩ P₂).card + (M₂ ∩ P₁).card := by
  classical
  set σ : Finset (Fin m) → G := fun S => ∑ j ∈ S, h j with hσ
  -- the cross relation
  have hcross : σ M₁ + σ P₂ = σ M₂ + σ P₁ := by
    have := hv₁.trans hv₂.symm
    -- σ M₁ - σ P₁ = σ M₂ - σ P₂
    rw [sub_eq_sub_iff_add_eq_add] at this
    exact this
  -- union/intersection form: σ(M₁ ∪ P₂) + σ(M₁ ∩ P₂) = σ(M₂ ∪ P₁) + σ(M₂ ∩ P₁)
  have hui : σ (M₁ ∪ P₂) + σ (M₁ ∩ P₂) = σ (M₂ ∪ P₁) + σ (M₂ ∩ P₁) := by
    rw [hσ]
    simp only
    rw [Finset.sum_union_inter, Finset.sum_union_inter]
    exact hcross
  -- one common element yields a single-double witness
  have kill : ∀ (A B : Finset (Fin m)) (u : Fin m), A.card = 3 → B.card = 4 → u ∈ A →
      u ∉ B → σ A + h u = σ B → False := by
    intro A B u hA hB huA huB heq
    -- σ A = h u + σ (A.erase u)
    have h1 : σ A = h u + σ (A.erase u) := by
      rw [hσ]; exact (Finset.add_sum_erase A h huA).symm
    -- cancel the common part C = (A.erase u) ∩ B
    have h2 : σ (A.erase u) = σ ((A.erase u) \ B) + σ ((A.erase u) ∩ B) := by
      rw [hσ]; simp only
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
    have h3 : σ B = σ (B \ (A.erase u)) + σ ((A.erase u) ∩ B) := by
      rw [hσ]; simp only
      rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter _ _),
        Finset.sdiff_union_inter]
    have hrel : 2 • h u + σ ((A.erase u) \ B) = σ (B \ (A.erase u)) := by
      have h4 : 2 • h u + σ ((A.erase u) \ B) + σ ((A.erase u) ∩ B)
          = σ (B \ (A.erase u)) + σ ((A.erase u) ∩ B) := by
        calc 2 • h u + σ ((A.erase u) \ B) + σ ((A.erase u) ∩ B)
            = h u + (h u + σ (A.erase u)) := by rw [two_nsmul, h2]; abel
          _ = σ A + h u := by rw [h1]; abel
          _ = σ B := heq
          _ = _ := h3
      exact add_right_cancel h4
    have hcardA : (A.erase u).card = 2 := by rw [Finset.card_erase_of_mem huA, hA]
    have hc : ((A.erase u) \ B).card + 1 ≤ (B \ (A.erase u)).card := by
      have e1 := Finset.card_sdiff_add_card_inter (A.erase u) B
      have e2 := Finset.card_sdiff_add_card_inter B (A.erase u)
      rw [Finset.inter_comm B] at e2
      omega
    refine hs.sh2 u ((A.erase u) \ B) (B \ (A.erase u)) ?_ ?_ disjoint_sdiff_sdiff
      hc ?_
    · intro hu; exact (Finset.notMem_erase u A) (Finset.mem_sdiff.mp hu).1
    · intro hu; exact huB (Finset.mem_sdiff.mp hu).1
    · rw [hσ] at hrel; exact hrel
  -- now the case analysis on the intersection sizes
  by_contra hlt
  have hI₁ : (M₁ ∩ P₂).card ≤ 1 := by omega
  have hI₂ : (M₂ ∩ P₁).card ≤ 1 := by omega
  rcases Nat.lt_or_ge (M₁ ∩ P₂).card 1 with h₁0 | h₁1
  · have hE₁ : M₁ ∩ P₂ = ∅ := Finset.card_eq_zero.mp (by omega)
    rcases Nat.lt_or_ge (M₂ ∩ P₁).card 1 with h₂0 | h₂1
    · -- both intersections empty: a cube collision forcing equal representations
      have hE₂ : M₂ ∩ P₁ = ∅ := Finset.card_eq_zero.mp (by omega)
      have hU : σ (M₁ ∪ P₂) = σ (M₂ ∪ P₁) := by
        have := hui
        rw [hE₁, hE₂] at this
        simpa [hσ] using this
      have hUeq : M₁ ∪ P₂ = M₂ ∪ P₁ := hs.dis hU
      have hM : M₁ = M₂ := by
        apply Finset.eq_of_subset_of_card_le _ (by rw [hM₁, hM₂])
        intro a ha
        have ha' : a ∈ M₂ ∪ P₁ := hUeq ▸ Finset.mem_union_left _ ha
        rcases Finset.mem_union.mp ha' with h | h
        · exact h
        · exact (Finset.disjoint_left.mp hd₁ ha h).elim
      have hP : P₁ = P₂ := by
        have e := hv₁.trans hv₂.symm
        rw [hM] at e
        exact hs.dis (sub_right_injective e)
      rcases hne with hne | hne
      · exact hne hM
      · exact hne hP
    · -- |M₂ ∩ P₁| = 1
      have h₂1' : (M₂ ∩ P₁).card = 1 := by omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h₂1'
      have huM₂ : u ∈ M₂ := (Finset.mem_inter.mp (hu ▸ Finset.mem_singleton_self u)).1
      have huP₁ : u ∈ P₁ := (Finset.mem_inter.mp (hu ▸ Finset.mem_singleton_self u)).2
      have heq : σ (M₂ ∪ P₁) + h u = σ (M₁ ∪ P₂) := by
        have e := hui
        rw [hE₁, hu] at e
        simp only [hσ, Finset.sum_empty, add_zero, Finset.sum_singleton] at e
        rw [hσ]; simp only
        exact e.symm
      refine kill (M₂ ∪ P₁) (M₁ ∪ P₂) u ?_ ?_ (Finset.mem_union_left _ huM₂) ?_ heq
      · have e := Finset.card_union_add_card_inter M₂ P₁
        omega
      · rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hE₁)]
        omega
      · intro hu'
        rcases Finset.mem_union.mp hu' with h | h
        · exact Finset.disjoint_left.mp hd₁ h huP₁
        · exact Finset.disjoint_left.mp hd₂ huM₂ h
  · -- |M₁ ∩ P₂| = 1, hence |M₂ ∩ P₁| = 0
    have h₁1' : (M₁ ∩ P₂).card = 1 := by omega
    have hE₂ : M₂ ∩ P₁ = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h₁1'
    have huM₁ : u ∈ M₁ := (Finset.mem_inter.mp (hu ▸ Finset.mem_singleton_self u)).1
    have huP₂ : u ∈ P₂ := (Finset.mem_inter.mp (hu ▸ Finset.mem_singleton_self u)).2
    have heq : σ (M₁ ∪ P₂) + h u = σ (M₂ ∪ P₁) := by
      have e := hui
      rw [hE₂, hu] at e
      simp only [hσ, Finset.sum_empty, add_zero, Finset.sum_singleton] at e
      rw [hσ]; simp only
      exact e
    refine kill (M₁ ∪ P₂) (M₂ ∪ P₁) u ?_ ?_ (Finset.mem_union_left _ huM₁) ?_ heq
    · have e := Finset.card_union_add_card_inter M₁ P₂
      omega
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hE₂)]
      omega
    · intro hu'
      rcases Finset.mem_union.mp hu' with h | h
      · exact Finset.disjoint_left.mp hd₂ h huP₂
      · exact Finset.disjoint_left.mp hd₁ huM₁ h

/-! ### The cluster lemma -/

/-- A representation family: disjoint `(2,2)`-pairs all representing `v`. -/
def RepFamily (h : Fin m → G) (v : G) (F : Finset (Finset (Fin m) × Finset (Fin m))) : Prop :=
  ∀ R ∈ F, R.1.card = 2 ∧ R.2.card = 2 ∧ Disjoint R.1 R.2 ∧
    (∑ j ∈ R.1, h j) - ∑ j ∈ R.2, h j = v

/-- Distinct members of a representation family satisfy the survival
inequality. -/
private lemma family_survival (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) {R R' : Finset (Fin m) × Finset (Fin m)}
    (hR : R ∈ F) (hR' : R' ∈ F) (hne : R ≠ R') :
    2 ≤ (R.1 ∩ R'.2).card + (R'.1 ∩ R.2).card := by
  obtain ⟨c1, c2, d, e⟩ := hF R hR
  obtain ⟨c1', c2', d', e'⟩ := hF R' hR'
  refine survival22 hs c1 c2 c1' c2' d d' e e' ?_
  by_contra hcon
  push Not at hcon
  exact hne (Prod.ext hcon.1 hcon.2)

/-- In a representation family, equal `M`-parts force equal members. -/
private lemma family_eq_of_fst (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) {R R' : Finset (Fin m) × Finset (Fin m)}
    (hR : R ∈ F) (hR' : R' ∈ F) (h1 : R.1 = R'.1) : R = R' := by
  obtain ⟨_, _, _, e⟩ := hF R hR
  obtain ⟨_, _, _, e'⟩ := hF R' hR'
  have e2 := e.trans e'.symm
  rw [h1] at e2
  exact Prod.ext h1 (hs.dis (sub_right_injective e2))

/-- In a representation family, equal `P`-parts force equal members. -/
private lemma family_eq_of_snd (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) {R R' : Finset (Fin m) × Finset (Fin m)}
    (hR : R ∈ F) (hR' : R' ∈ F) (h2 : R.2 = R'.2) : R = R' := by
  obtain ⟨_, _, _, e⟩ := hF R hR
  obtain ⟨_, _, _, e'⟩ := hF R' hR'
  have e2 := e.trans e'.symm
  rw [h2] at e2
  exact Prod.ext (hs.dis (sub_left_injective e2)) h2

/-- Members whose `M`-part contains a fixed `p`: at most three. -/
private lemma group_bound_fst (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) (p : Fin m) : (F.filter fun R => p ∈ R.1).card ≤ 3 := by
  classical
  set Gp := F.filter fun R => p ∈ R.1 with hGp
  rcases Gp.eq_empty_or_nonempty with he | ⟨R₀, hR₀⟩
  · rw [he]; simp
  · have hR₀F : R₀ ∈ F := (Finset.mem_filter.mp hR₀).1
    have hpR₀ : p ∈ R₀.1 := (Finset.mem_filter.mp hR₀).2
    obtain ⟨c1₀, c2₀, d₀, _⟩ := hF R₀ hR₀F
    -- the other element of `R.1` lies in `R₀.2`
    have hmap : ∀ R ∈ Gp.erase R₀, R.1.erase p ∈ R₀.2.image (fun a => ({a} : Finset (Fin m))) := by
      intro R hR
      have hRne : R ≠ R₀ := (Finset.mem_erase.mp hR).1
      have hRG : R ∈ Gp := (Finset.mem_erase.mp hR).2
      have hRF : R ∈ F := (Finset.mem_filter.mp hRG).1
      have hpR : p ∈ R.1 := (Finset.mem_filter.mp hRG).2
      obtain ⟨c1, c2, d, _⟩ := hF R hRF
      have hsurv := family_survival hs hF hRF hR₀F hRne
      have hpn₀ : p ∉ R₀.2 := Finset.disjoint_left.mp d₀ hpR₀
      have hpn : p ∉ R.2 := Finset.disjoint_left.mp d hpR
      have hsub1 : R.1 ∩ R₀.2 ⊆ R.1.erase p := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun hap => hpn₀ (hap ▸ (Finset.mem_inter.mp ha).2),
          (Finset.mem_inter.mp ha).1⟩
      have hsub2 : R₀.1 ∩ R.2 ⊆ R₀.1.erase p := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun hap => hpn (hap ▸ (Finset.mem_inter.mp ha).2),
          (Finset.mem_inter.mp ha).1⟩
      have hc1 : (R.1.erase p).card = 1 := by rw [Finset.card_erase_of_mem hpR, c1]
      have hc2 : (R₀.1.erase p).card = 1 := by rw [Finset.card_erase_of_mem hpR₀, c1₀]
      have hle1 := Finset.card_le_card hsub1
      have hle2 := Finset.card_le_card hsub2
      have hex : (R.1 ∩ R₀.2).card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hex
      have haR : a ∈ R.1 := (Finset.mem_inter.mp (ha ▸ Finset.mem_singleton_self a)).1
      have haR₀ : a ∈ R₀.2 := (Finset.mem_inter.mp (ha ▸ Finset.mem_singleton_self a)).2
      have hap : a ≠ p := fun hap => hpn₀ (hap ▸ haR₀)
      have herase : R.1.erase p = {a} := by
        apply Finset.eq_of_subset_of_card_le
        · intro b hb
          rw [Finset.mem_singleton]
          have hb' := Finset.mem_erase.mp hb
          have : ({b, a} : Finset (Fin m)) ⊆ R.1 := by
            intro c hc
            rcases Finset.mem_insert.mp hc with rfl | hc
            · exact hb'.2
            · exact (Finset.mem_singleton.mp hc) ▸ haR
          by_contra hba
          have h3 : ({p, b, a} : Finset (Fin m)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hba]
            simp [Ne.symm hb'.1, Ne.symm hap]
          have hsub : ({p, b, a} : Finset (Fin m)) ⊆ R.1 := by
            intro c hc
            rcases Finset.mem_insert.mp hc with rfl | hc
            · exact hpR
            · exact this hc
          have := Finset.card_le_card hsub
          omega
        · rw [Finset.card_singleton, hc1]
      rw [herase]
      exact Finset.mem_image_of_mem _ haR₀
    have hinj : Set.InjOn (fun R : Finset (Fin m) × Finset (Fin m) => R.1.erase p) (Gp.erase R₀) := by
      intro R hR R' hR' heq
      have hRF : R ∈ F := (Finset.mem_filter.mp (Finset.mem_erase.mp hR).2).1
      have hR'F : R' ∈ F := (Finset.mem_filter.mp (Finset.mem_erase.mp hR').2).1
      have hpR : p ∈ R.1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hR).2).2
      have hpR' : p ∈ R'.1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hR').2).2
      have h1 : R.1 = R'.1 := by
        rw [← Finset.insert_erase hpR, ← Finset.insert_erase hpR']
        simp only at heq
        rw [heq]
      exact family_eq_of_fst hs hF hRF hR'F h1
    have hcard := Finset.card_le_card_of_injOn _ hmap hinj
    rw [Finset.card_image_of_injective _ Finset.singleton_injective, c2₀] at hcard
    have := Finset.card_erase_add_one hR₀
    omega

/-- Members whose `P`-part contains a fixed `q`: at most three. -/
private lemma group_bound_snd (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) (q : Fin m) : (F.filter fun R => q ∈ R.2).card ≤ 3 := by
  classical
  -- swap the roles of M and P: the swapped family represents -v
  have hF' : RepFamily h (-v) (F.image Prod.swap) := by
    intro R hR
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨c1, c2, d, e⟩ := hF R' hR'
    exact ⟨c2, c1, d.symm, by simp [Prod.swap]; rw [← e]; abel⟩
  have hb := group_bound_fst hs hF' q
  have hswap : (F.image Prod.swap).filter (fun R => q ∈ R.1)
      = (F.filter fun R => q ∈ R.2).image Prod.swap := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨R', hR', rfl⟩, hq⟩
      exact ⟨R', ⟨hR', hq⟩, rfl⟩
    · rintro ⟨R', ⟨hR', hq⟩, rfl⟩
      exact ⟨⟨R', hR', rfl⟩, hq⟩
  rw [hswap, Finset.card_image_of_injective _ Prod.swap_injective] at hb
  exact hb

/-- **Cluster lemma.**  A representation family has at most `13` members. -/
theorem cluster22 (hs : SHC h) {v : G} {F : Finset (Finset (Fin m) × Finset (Fin m))}
    (hF : RepFamily h v F) : F.card ≤ 13 := by
  classical
  rcases F.eq_empty_or_nonempty with he | ⟨R₁, hR₁⟩
  · rw [he]; simp
  · obtain ⟨c1, c2, _, _⟩ := hF R₁ hR₁
    have hcover : F ⊆ insert R₁ ((R₁.2.biUnion fun p => F.filter fun R => p ∈ R.1)
        ∪ (R₁.1.biUnion fun q => F.filter fun R => q ∈ R.2)) := by
      intro R hR
      by_cases hRR : R = R₁
      · exact hRR ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hs2 := family_survival hs hF hR hR₁ hRR
        rcases Nat.lt_or_ge 0 (R.1 ∩ R₁.2).card with hpos | hzero
        · obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
          apply Finset.mem_union_left
          exact Finset.mem_biUnion.mpr ⟨p, (Finset.mem_inter.mp hp).2,
            Finset.mem_filter.mpr ⟨hR, (Finset.mem_inter.mp hp).1⟩⟩
        · have hpos' : 0 < (R₁.1 ∩ R.2).card := by omega
          obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos'
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨q, (Finset.mem_inter.mp hq).1,
            Finset.mem_filter.mpr ⟨hR, (Finset.mem_inter.mp hq).2⟩⟩
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_insert_le R₁ ((R₁.2.biUnion fun p => F.filter fun R => p ∈ R.1)
        ∪ (R₁.1.biUnion fun q => F.filter fun R => q ∈ R.2))
    have h3 := Finset.card_union_le (R₁.2.biUnion fun p => F.filter fun R => p ∈ R.1)
        (R₁.1.biUnion fun q => F.filter fun R => q ∈ R.2)
    have h4 : (R₁.2.biUnion fun p => F.filter fun R => p ∈ R.1).card ≤ 6 := by
      calc _ ≤ ∑ p ∈ R₁.2, (F.filter fun R => p ∈ R.1).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ R₁.2, 3 := Finset.sum_le_sum fun p _ => group_bound_fst hs hF p
        _ = 6 := by rw [Finset.sum_const, c2]; simp
    have h5 : (R₁.1.biUnion fun q => F.filter fun R => q ∈ R.2).card ≤ 6 := by
      calc _ ≤ ∑ q ∈ R₁.1, (F.filter fun R => q ∈ R.2).card := Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ R₁.1, 3 := Finset.sum_le_sum fun q _ => group_bound_snd hs hF q
        _ = 6 := by rw [Finset.sum_const, c1]; simp
    omega

/-! ### Target lemmas at level two -/

/-- `2 • h x + σ Y` (with `x ∉ Y`) is never a subset sum over `≥ |Y| + 1` indices. -/
private lemma head2_target (hs : SHC h) (x : Fin m) (Y T : Finset (Fin m)) (hxY : x ∉ Y)
    (hT : Y.card + 1 ≤ T.card) : 2 • h x + ∑ j ∈ Y, h j ≠ ∑ j ∈ T, h j := by
  classical
  intro heq
  -- cancel the common part Y ∩ T
  have hY : (∑ j ∈ Y, h j) = (∑ j ∈ Y \ T, h j) + ∑ j ∈ Y ∩ T, h j := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
  have hTd : (∑ j ∈ T, h j) = (∑ j ∈ T \ Y, h j) + ∑ j ∈ Y ∩ T, h j := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter _ _),
      Finset.sdiff_union_inter]
  have hrel : 2 • h x + ∑ j ∈ Y \ T, h j = ∑ j ∈ T \ Y, h j := by
    have h4 : 2 • h x + ∑ j ∈ Y \ T, h j + ∑ j ∈ Y ∩ T, h j
        = (∑ j ∈ T \ Y, h j) + ∑ j ∈ Y ∩ T, h j := by
      rw [← hTd, ← heq, hY]; abel
    exact add_right_cancel h4
  have e1 := Finset.card_sdiff_add_card_inter Y T
  have e2 := Finset.card_sdiff_add_card_inter T Y
  rw [Finset.inter_comm T] at e2
  by_cases hxT : x ∈ T
  · -- x ∈ T \ Y: a cube collision  σ({x} ∪ (Y \ T)) = σ((T \ Y).erase x)
    have hxTY : x ∈ T \ Y := Finset.mem_sdiff.mpr ⟨hxT, hxY⟩
    have hsplit : (∑ j ∈ T \ Y, h j) = h x + ∑ j ∈ (T \ Y).erase x, h j :=
      (Finset.add_sum_erase _ h hxTY).symm
    have hcol : (∑ j ∈ insert x (Y \ T), h j) = ∑ j ∈ (T \ Y).erase x, h j := by
      rw [Finset.sum_insert (fun hx' => hxY (Finset.mem_sdiff.mp hx').1)]
      have h5 : h x + (h x + ∑ j ∈ Y \ T, h j) = h x + ∑ j ∈ (T \ Y).erase x, h j := by
        rw [← hsplit, ← hrel, two_nsmul]; abel
      exact add_left_cancel h5
    have hsets := hs.dis hcol
    have : x ∈ (T \ Y).erase x := hsets ▸ Finset.mem_insert_self x _
    exact Finset.notMem_erase x _ this
  · exact hs.sh2 x (Y \ T) (T \ Y) (fun hx' => hxY (Finset.mem_sdiff.mp hx').1)
      (fun hx' => hxT (Finset.mem_sdiff.mp hx').1) disjoint_sdiff_sdiff (by omega) hrel

/-- `3 • h x + σ Y` (with `x ∉ Y`) is never a subset sum over `≥ |Y| + 2` indices. -/
private lemma head3_target (hs : SHC h) (x : Fin m) (Y T : Finset (Fin m)) (hxY : x ∉ Y)
    (hT : Y.card + 2 ≤ T.card) : 3 • h x + ∑ j ∈ Y, h j ≠ ∑ j ∈ T, h j := by
  classical
  intro heq
  have hY : (∑ j ∈ Y, h j) = (∑ j ∈ Y \ T, h j) + ∑ j ∈ Y ∩ T, h j := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
  have hTd : (∑ j ∈ T, h j) = (∑ j ∈ T \ Y, h j) + ∑ j ∈ Y ∩ T, h j := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter _ _),
      Finset.sdiff_union_inter]
  have hrel : 3 • h x + ∑ j ∈ Y \ T, h j = ∑ j ∈ T \ Y, h j := by
    have h4 : 3 • h x + ∑ j ∈ Y \ T, h j + ∑ j ∈ Y ∩ T, h j
        = (∑ j ∈ T \ Y, h j) + ∑ j ∈ Y ∩ T, h j := by
      rw [← hTd, ← heq, hY]; abel
    exact add_right_cancel h4
  have e1 := Finset.card_sdiff_add_card_inter Y T
  have e2 := Finset.card_sdiff_add_card_inter T Y
  rw [Finset.inter_comm T] at e2
  by_cases hxT : x ∈ T
  · have hxTY : x ∈ T \ Y := Finset.mem_sdiff.mpr ⟨hxT, hxY⟩
    have hsplit : (∑ j ∈ T \ Y, h j) = h x + ∑ j ∈ (T \ Y).erase x, h j :=
      (Finset.add_sum_erase _ h hxTY).symm
    have hrel2 : 2 • h x + ∑ j ∈ Y \ T, h j = ∑ j ∈ (T \ Y).erase x, h j := by
      have h5 : 2 • h x + ∑ j ∈ Y \ T, h j + h x = (∑ j ∈ (T \ Y).erase x, h j) + h x := by
        calc 2 • h x + ∑ j ∈ Y \ T, h j + h x = 3 • h x + ∑ j ∈ Y \ T, h j := by
              rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]; abel
          _ = ∑ j ∈ T \ Y, h j := hrel
          _ = _ := by rw [hsplit]; abel
      exact add_right_cancel h5
    refine hs.sh2 x (Y \ T) ((T \ Y).erase x) (fun hx' => hxY (Finset.mem_sdiff.mp hx').1)
      (Finset.notMem_erase x _) ?_ ?_ hrel2
    · exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) disjoint_sdiff_sdiff
    · rw [Finset.card_erase_of_mem hxTY]; omega
  · exact hs.sh3 x (Y \ T) (T \ Y) (fun hx' => hxY (Finset.mem_sdiff.mp hx').1)
      (fun hx' => hxT (Finset.mem_sdiff.mp hx').1) disjoint_sdiff_sdiff (by omega) hrel

/-- **All-level target lemma.**  Translation of a subset sum by `2 • h x`
cannot increase its level.  If `x ∉ Y`, this is the head-2 shell condition;
if `x ∈ Y`, splitting off `h x` turns it into the head-3 condition. -/
theorem shc_shift_target_card_gt (hs : SHC h) (x : Fin m)
    (Y T : Finset (Fin m)) (hcard : Y.card < T.card) :
    2 • h x + ∑ j ∈ Y, h j ≠ ∑ j ∈ T, h j := by
  classical
  by_cases hxY : x ∈ Y
  · intro heq
    have hsplit : (∑ j ∈ Y, h j) = h x + ∑ j ∈ Y.erase x, h j :=
      (Finset.add_sum_erase Y h hxY).symm
    refine head3_target hs x (Y.erase x) T (Finset.notMem_erase x Y) ?_ ?_
    · rw [Finset.card_erase_of_mem hxY]
      have hypos : 0 < Y.card := Finset.card_pos.mpr ⟨x, hxY⟩
      omega
    · calc
        3 • h x + ∑ j ∈ Y.erase x, h j
            = 2 • h x + ∑ j ∈ Y, h j := by
                rw [hsplit, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]
                abel
        _ = ∑ j ∈ T, h j := heq
  · exact head2_target hs x Y T hxY (by omega)

/-- Equality after a `2 • h x` shift forces the target subset to have no
larger cardinality than the source subset. -/
theorem card_le_of_two_smul_add_sum_eq (hs : SHC h) (x : Fin m)
    (Y T : Finset (Fin m))
    (heq : 2 • h x + ∑ j ∈ Y, h j = ∑ j ∈ T, h j) : T.card ≤ Y.card := by
  by_contra hnot
  exact shc_shift_target_card_gt hs x Y T (by omega) heq

/-- Consequences of dissociation and no 3-APs used in the charging argument. -/
private lemma shc_inj (hs : SHC h) : Function.Injective h := by
  intro a b hab
  have : (∑ j ∈ ({a} : Finset (Fin m)), h j) = ∑ j ∈ ({b} : Finset (Fin m)), h j := by
    simp [hab]
  exact Finset.singleton_injective (hs.dis this)

private lemma shc_ne (hs : SHC h) (a : Fin m) : h a ≠ 0 := by
  intro ha
  have : (∑ j ∈ ({a} : Finset (Fin m)), h j) = ∑ j ∈ (∅ : Finset (Fin m)), h j := by simp [ha]
  exact absurd (hs.dis this) (Finset.singleton_ne_empty a)

private lemma shc_no3AP (hs : SHC h) (a b c : Fin m) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    h a + h c ≠ 2 • h b := by
  intro heq
  refine hs.sh2 b ∅ {a, c} (Finset.notMem_empty b) (by simp [Ne.symm hab, hbc])
    (Finset.disjoint_empty_left _) (by rw [Finset.card_empty, Finset.card_pair hac]; omega) ?_
  rw [Finset.sum_empty, add_zero, Finset.sum_pair hac]
  exact heq.symm

/-- Two consecutive matching edges `h a' = h a + τ`, `h a'' = h a' + τ` form a 3-AP. -/
private lemma ap_kill (hs : SHC h) {τ : G} (hτ : τ ≠ 0) (h2τ : τ + τ ≠ 0)
    {a a' a'' : Fin m} (e1 : h a' = h a + τ) (e2 : h a'' = h a' + τ) : False := by
  have hab : a ≠ a' := by
    rintro rfl
    exact hτ (add_left_cancel (show h a + 0 = h a + τ by rw [add_zero]; exact e1)).symm
  have hbc : a' ≠ a'' := by
    rintro rfl
    exact hτ (add_left_cancel (show h a' + 0 = h a' + τ by rw [add_zero]; exact e2)).symm
  have hac : a ≠ a'' := by
    rintro rfl
    rw [e1, add_assoc] at e2
    exact h2τ (add_left_cancel (show h a + 0 = h a + (τ + τ) by rw [add_zero]; exact e2)).symm
  exact shc_no3AP hs a a' a'' hab hbc hac (by rw [e2, e1, two_nsmul]; abel)

/-- A foot-move `S₀ → S₁` (pairs with one common element and `σ S₁ = σ S₀ + τ`)
is a matching edge on the moving element. -/
private lemma foot_structure {τ : G} {S₀ S₁ : Finset (Fin m)}
    (h0 : S₀.card = 2) (h1 : S₁.card = 2) (hint : (S₀ ∩ S₁).card = 1)
    (hσ : (∑ j ∈ S₁, h j) = (∑ j ∈ S₀, h j) + τ) :
    ∃ b a a', a ≠ b ∧ a' ≠ b ∧ a ≠ a' ∧ S₀ = {b, a} ∧ S₁ = {b, a'} ∧ h a' = h a + τ := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hint
  have hbS₀ : b ∈ S₀ := (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b)).1
  have hbS₁ : b ∈ S₁ := (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b)).2
  obtain ⟨p, q, hpq, hS₀⟩ := Finset.card_eq_two.mp h0
  obtain ⟨p', q', hpq', hS₁⟩ := Finset.card_eq_two.mp h1
  -- the element of S₀ other than b
  have hS₀b : ∃ a, a ≠ b ∧ S₀ = {b, a} := by
    rw [hS₀] at hbS₀
    rcases Finset.mem_insert.mp hbS₀ with rfl | hq
    · exact ⟨q, Ne.symm hpq, hS₀⟩
    · rw [Finset.mem_singleton] at hq
      subst hq
      exact ⟨p, hpq, by rw [hS₀, Finset.pair_comm]⟩
  have hS₁b : ∃ a', a' ≠ b ∧ S₁ = {b, a'} := by
    rw [hS₁] at hbS₁
    rcases Finset.mem_insert.mp hbS₁ with rfl | hq
    · exact ⟨q', Ne.symm hpq', hS₁⟩
    · rw [Finset.mem_singleton] at hq
      subst hq
      exact ⟨p', hpq', by rw [hS₁, Finset.pair_comm]⟩
  obtain ⟨a, hab, hS₀'⟩ := hS₀b
  obtain ⟨a', hab', hS₁'⟩ := hS₁b
  have haa' : a ≠ a' := by
    rintro rfl
    have : a ∈ S₀ ∩ S₁ := Finset.mem_inter.mpr
      ⟨hS₀' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self a),
       hS₁' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self a)⟩
    rw [hb, Finset.mem_singleton] at this
    exact hab this
  refine ⟨b, a, a', hab, hab', haa', hS₀', hS₁', ?_⟩
  rw [hS₀', hS₁', Finset.sum_pair (Ne.symm hab), Finset.sum_pair (Ne.symm hab')] at hσ
  -- h b + h a' = h b + h a + τ
  have : h b + h a' = h b + (h a + τ) := by rw [hσ]; abel
  exact add_left_cancel this

/-- Membership of an element in a two-element set. -/
private lemma mem_pair_cases {c b a : Fin m} (hc : c ∈ ({b, a} : Finset (Fin m))) :
    c = b ∨ c = a := by
  rcases Finset.mem_insert.mp hc with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Finset.mem_singleton.mp h)

/-- **No three consecutive foot-moves.**  Pairs `S₀ → S₁ → S₂ → S₃` with
consecutive intersections of size one and `σ` increasing by `τ` at each
step force a 3-AP among the `h`'s. -/
private lemma no_three_feet (hs : SHC h) {τ : G} (hτ : τ ≠ 0) (h2τ : τ + τ ≠ 0)
    {S₀ S₁ S₂ S₃ : Finset (Fin m)}
    (c0 : S₀.card = 2) (c1 : S₁.card = 2) (c2 : S₂.card = 2) (c3 : S₃.card = 2)
    (i01 : (S₀ ∩ S₁).card = 1) (i12 : (S₁ ∩ S₂).card = 1) (i23 : (S₂ ∩ S₃).card = 1)
    (e1 : (∑ j ∈ S₁, h j) = (∑ j ∈ S₀, h j) + τ)
    (e2 : (∑ j ∈ S₂, h j) = (∑ j ∈ S₁, h j) + τ)
    (e3 : (∑ j ∈ S₃, h j) = (∑ j ∈ S₂, h j) + τ) : False := by
  obtain ⟨b, a, a', hab, hab', haa', hS₀, hS₁, ea⟩ := foot_structure c0 c1 i01 e1
  obtain ⟨c, e, e', hec, hec', hee', hS₁', hS₂, ee⟩ := foot_structure c1 c2 i12 e2
  -- {c, e} = {b, a'}
  have hcm : c ∈ ({b, a'} : Finset (Fin m)) := hS₁ ▸ hS₁' ▸ Finset.mem_insert_self c {e}
  have hem : e ∈ ({b, a'} : Finset (Fin m)) :=
    hS₁ ▸ hS₁' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self e)
  rcases mem_pair_cases hcm with rfl | rfl
  · -- c = b: the same foot moves twice
    rcases mem_pair_cases hem with rfl | rfl
    · exact absurd rfl hec
    · exact ap_kill hs hτ h2τ ea ee
  · -- c = a': feet switch, S₂ = {a', e'} with h e' = h b + τ (e = b)
    rcases mem_pair_cases hem with rfl | rfl
    · -- e = b
      obtain ⟨d, g, g', hgd, hgd', hgg', hS₂', hS₃, eg⟩ := foot_structure c2 c3 i23 e3
      have hdm : d ∈ ({c, e'} : Finset (Fin m)) := hS₂ ▸ hS₂' ▸ Finset.mem_insert_self d {g}
      have hgm : g ∈ ({c, e'} : Finset (Fin m)) :=
        hS₂ ▸ hS₂' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self g)
      rcases mem_pair_cases hdm with rfl | rfl
      · rcases mem_pair_cases hgm with rfl | rfl
        · exact absurd rfl hgd
        · exact ap_kill hs hτ h2τ ee eg
      · rcases mem_pair_cases hgm with rfl | rfl
        · exact ap_kill hs hτ h2τ ea eg
        · exact absurd rfl hgd
    · exact absurd rfl hec

/-! ### The theorem -/

/-- **Quadratic wedge.**  An SHC family `h : Fin m → G` in a finite abelian
group forces `C(m,2) ≤ 3·(m + (|G| - 2^m) + 14)`.  Writing `|G| = 2^m + r`:
`r ≥ m(m-1)/6 - m - 14`, so no SHC family exists in odd order
`2^m + r` with `r` below that bound. -/
theorem quadratic_wedge [Fintype G] (h : Fin m → G) (hs : SHC h) :
    m.choose 2 ≤ 3 * (m + (Fintype.card G - 2 ^ m) + 14) := by
  classical
  set σ : Finset (Fin m) → G := fun S => ∑ j ∈ S, h j with hσ
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : m.choose 2 = 0 := Nat.choose_eq_zero_of_lt hm
    omega
  set x₀ : Fin m := ⟨0, by omega⟩ with hx₀
  set τ : G := 2 • h x₀ with hτ
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply shc_ne hs x₀
    exact hs.inj2 (h x₀) 0 (by rw [← two_nsmul, ← hτ, h0, add_zero])
  have h2τ0 : τ + τ ≠ 0 := fun h0 => hτ0 (hs.inj2 τ 0 (by rw [h0, add_zero]))
  -- the cube and its complement
  set Cimg : Finset G := Finset.univ.image σ with hCimg
  have hCcard : Cimg.card = 2 ^ m := by
    rw [hCimg, Finset.card_image_of_injective _ hs.dis, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  have hcard2m : 2 ^ m ≤ Fintype.card G := by
    have := Finset.card_le_univ Cimg
    rwa [hCcard] at this
  -- the pair sums
  set P₂ : Finset (Finset (Fin m)) := Finset.univ.powersetCard 2 with hP₂
  have hP₂mem : ∀ S, S ∈ P₂ ↔ S.card = 2 := by
    intro S; rw [hP₂, Finset.mem_powersetCard]; simp
  set H₂ : Finset G := P₂.image σ with hH₂
  have hH₂card : H₂.card = m.choose 2 := by
    rw [hH₂, Finset.card_image_of_injective _ hs.dis, hP₂, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  set Hs : Finset G := Finset.univ.image h with hHs
  have hHscard : Hs.card = m := by
    rw [hHs, Finset.card_image_of_injective _ (shc_inj hs), Finset.card_univ, Fintype.card_fin]
  -- foot-moves, stated through the (unique) representing pairs
  set foot : G → Prop := fun u => u ∈ H₂ ∧ u + τ ∈ H₂ ∧
    ∀ S S', S ∈ P₂ → S' ∈ P₂ → σ S = u → σ S' = u + τ → (S ∩ S').card = 1 with hfoot
  have hno3 : ∀ u, foot u → foot (u + τ) → ¬ foot (u + τ + τ) := by
    intro u f0 f1 f2
    simp only [hfoot] at f0 f1 f2
    obtain ⟨hu, hu1, hf0⟩ := f0
    obtain ⟨_, hu2, hf1⟩ := f1
    obtain ⟨_, hu3, hf2⟩ := f2
    obtain ⟨S₀, hS₀, e0⟩ := Finset.mem_image.mp hu
    obtain ⟨S₁, hS₁, e1⟩ := Finset.mem_image.mp hu1
    obtain ⟨S₂, hS₂, e2⟩ := Finset.mem_image.mp hu2
    obtain ⟨S₃, hS₃, e3⟩ := Finset.mem_image.mp hu3
    refine no_three_feet hs hτ0 h2τ0 ((hP₂mem S₀).mp hS₀) ((hP₂mem S₁).mp hS₁)
      ((hP₂mem S₂).mp hS₂) ((hP₂mem S₃).mp hS₃)
      (hf0 S₀ S₁ hS₀ hS₁ e0 e1) (hf1 S₁ S₂ hS₁ hS₂ e1 e2) (hf2 S₂ S₃ hS₂ hS₃ e2 e3)
      ?_ ?_ ?_
    · show σ S₁ = σ S₀ + τ; rw [e1, e0]
    · show σ S₂ = σ S₁ + τ; rw [e2, e1]
    · show σ S₃ = σ S₂ + τ; rw [e3, e2]
  -- the three-fold cover of H₂ by the non-foot set
  set NF : Finset G := H₂.filter (fun u => ¬ foot u) with hNF
  have hcover : H₂ ⊆ NF ∪ NF.image (fun w => w - τ) ∪ NF.image (fun w => w - τ - τ) := by
    intro u hu
    by_cases f0 : foot u
    · by_cases f1 : foot (u + τ)
      · have hu2 : u + τ + τ ∈ H₂ := by
          have := f1; simp only [hfoot] at this; exact this.2.1
        have hnf : ¬ foot (u + τ + τ) := hno3 u f0 f1
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨u + τ + τ, Finset.mem_filter.mpr ⟨hu2, hnf⟩,
          by show u + τ + τ - τ - τ = u; abel⟩
      · have hu1 : u + τ ∈ H₂ := by
          have := f0; simp only [hfoot] at this; exact this.2.1
        apply Finset.mem_union_left; apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨u + τ, Finset.mem_filter.mpr ⟨hu1, f1⟩,
          by show u + τ - τ = u; abel⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hu, f0⟩
  have hH₂le : H₂.card ≤ 3 * NF.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (NF ∪ NF.image (fun w => w - τ))
      (NF.image (fun w => w - τ - τ))
    have h3 := Finset.card_union_le NF (NF.image (fun w => w - τ))
    have h4 := Finset.card_image_le (s := NF) (f := fun w => w - τ)
    have h5 := Finset.card_image_le (s := NF) (f := fun w => w - τ - τ)
    omega
  -- jump sources and escapees
  set J : Finset G := NF.filter (fun u => u + τ ∈ H₂) with hJ
  set E : Finset G := NF.filter (fun u => ¬ (u + τ ∈ H₂)) with hE
  have hNFsplit : J.card + E.card = NF.card := by
    rw [hJ, hE]; exact Finset.card_filter_add_card_filter_not _
  -- jump sources inject into the representation family of τ
  set F : Finset (Finset (Fin m) × Finset (Fin m)) :=
    (P₂ ×ˢ P₂).filter (fun R => Disjoint R.1 R.2 ∧ σ R.1 = σ R.2 + τ) with hF
  have hFfam : RepFamily h τ F := by
    intro R hR
    simp only [hF, Finset.mem_filter, Finset.mem_product] at hR
    obtain ⟨⟨h1, h2⟩, hd, hv⟩ := hR
    refine ⟨(hP₂mem _).mp h1, (hP₂mem _).mp h2, hd, ?_⟩
    show σ R.1 - σ R.2 = τ
    rw [hv]; abel
  have hJle : J.card ≤ 13 := by
    have hsub : J ⊆ F.image (fun R => σ R.2) := by
      intro u hu
      simp only [hJ, hNF, Finset.mem_filter] at hu
      obtain ⟨⟨hu2, hnf⟩, hu1⟩ := hu
      obtain ⟨S, hS, eS⟩ := Finset.mem_image.mp hu2
      obtain ⟨S', hS', eS'⟩ := Finset.mem_image.mp hu1
      have hint : (S ∩ S').card ≠ 1 := by
        intro h1
        apply hnf
        simp only [hfoot]
        refine ⟨hu2, hu1, ?_⟩
        intro T T' hT hT' eT eT'
        have hTS : T = S := hs.dis (eT.trans eS.symm)
        have hTS' : T' = S' := hs.dis (eT'.trans eS'.symm)
        rw [hTS, hTS']; exact h1
      have hcS : S.card = 2 := (hP₂mem S).mp hS
      have hcS' : S'.card = 2 := (hP₂mem S').mp hS'
      have hle : (S ∩ S').card ≤ 2 := by
        have := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := S')); omega
      have hdisj : Disjoint S S' := by
        rcases Nat.lt_or_ge (S ∩ S').card 2 with hlt | hge
        · have : (S ∩ S').card = 0 := by omega
          exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp this)
        · exfalso
          have hSS' : S ∩ S' = S :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          have hsub' : S ⊆ S' := by rw [← hSS']; exact Finset.inter_subset_right
          have hEq : S = S' := Finset.eq_of_subset_of_card_le hsub' (by omega)
          apply hτ0
          have h6 : σ S' = σ S + τ := by rw [eS', eS]
          rw [hEq] at h6
          exact (add_left_cancel (show σ S' + 0 = σ S' + τ by rw [add_zero]; exact h6)).symm
      refine Finset.mem_image.mpr ⟨(S', S), ?_, eS⟩
      simp only [hF, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hS', hS⟩, hdisj.symm, by rw [eS', eS]⟩
    calc J.card ≤ (F.image (fun R => σ R.2)).card := Finset.card_le_card hsub
      _ ≤ F.card := Finset.card_image_le
      _ ≤ 13 := cluster22 hs hFfam
  -- escapees land in {0} ∪ Hs ∪ (cube complement)
  have hEle : E.card ≤ 1 + m + (Fintype.card G - 2 ^ m) := by
    have hinj_tr : Function.Injective (fun u : G => u + τ) :=
      fun a b hab => add_right_cancel hab
    have himg : E.image (fun u => u + τ) ⊆ insert (0 : G) (Hs ∪ (Finset.univ \ Cimg)) := by
      intro v hv
      obtain ⟨u, huE, huv⟩ := Finset.mem_image.mp hv
      simp only [hE, hNF, Finset.mem_filter] at huE
      obtain ⟨⟨hu2, _⟩, hesc⟩ := huE
      obtain ⟨S, hS, eS⟩ := Finset.mem_image.mp hu2
      have hcS : S.card = 2 := (hP₂mem S).mp hS
      by_cases hvC : v ∈ Cimg
      · obtain ⟨T, _, eT⟩ := Finset.mem_image.mp hvC
        rcases Nat.lt_or_ge T.card 3 with hTc | hTc
        · have hTc' : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
          rcases hTc' with h0 | h1 | h2
          · have hTe : T = ∅ := Finset.card_eq_zero.mp h0
            have hv0 : v = 0 := by rw [← eT, hTe, hσ]; simp
            exact Finset.mem_insert.mpr (Or.inl hv0)
          · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
            have hvj : v = h j := by rw [← eT, hj, hσ]; simp
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _
              (hvj ▸ Finset.mem_image_of_mem h (Finset.mem_univ j)))
          · exfalso
            apply hesc
            rw [huv]
            exact Finset.mem_image.mpr ⟨T, (hP₂mem T).mpr h2, eT⟩
        · exfalso
          by_cases hx₀S : x₀ ∈ S
          · have hsplit : σ S = h x₀ + σ (S.erase x₀) := (Finset.add_sum_erase S h hx₀S).symm
            refine head3_target hs x₀ (S.erase x₀) T (Finset.notMem_erase x₀ S) ?_ ?_
            · rw [Finset.card_erase_of_mem hx₀S, hcS]; omega
            · show 3 • h x₀ + σ (S.erase x₀) = σ T
              rw [eT, ← huv, ← eS, hsplit, hτ, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]
              abel
          · refine head2_target hs x₀ S T hx₀S (by omega) ?_
            show 2 • h x₀ + σ S = σ T
            rw [eT, ← huv, ← eS, hτ]
            abel
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvC⟩))
    have h1 : E.card = (E.image (fun u => u + τ)).card :=
      (Finset.card_image_of_injective _ hinj_tr).symm
    have h2 := Finset.card_le_card himg
    have h3 := Finset.card_insert_le (0 : G) (Hs ∪ (Finset.univ \ Cimg))
    have h4 := Finset.card_union_le Hs (Finset.univ \ Cimg)
    have h5 : (Finset.univ \ Cimg).card = Fintype.card G - 2 ^ m := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hCcard]
    omega
  omega

/-- The quadratic wedge stated directly for a valid tuple. -/
theorem quadratic_wedge_of_valid [Fintype G] (g : Fin (m + 1) → G)
    (hg : ValidTuple g) (hinj2 : ∀ x y : G, x + x = y + y → x = y) :
    m.choose 2 ≤ 3 * (m + (Fintype.card G - 2 ^ m) + 14) :=
  quadratic_wedge (diff g) (shc_diff_of_valid g hg hinj2)

/-- The linear wedge for a valid tuple modulo an odd natural number. -/
theorem valid_odd_zmod_bottom_wedge {N : ℕ} (hN : Odd N)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g) :
    2 ^ (m + 1) + m ≤ 2 * N + 2 := by
  haveI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  simpa [ZMod.card] using bottom_wedge_of_valid g hg (add_self_injective_zmod hN)

/-- The quadratic wedge for a valid tuple modulo an odd natural number. -/
theorem valid_odd_zmod_quadratic_wedge {N : ℕ} (hN : Odd N)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g) :
    m.choose 2 ≤ 3 * (m + (N - 2 ^ m) + 14) := by
  haveI : NeZero N := ⟨by rcases hN with ⟨k, rfl⟩; omega⟩
  simpa [ZMod.card] using quadratic_wedge_of_valid g hg (add_self_injective_zmod hN)

end QuadraticWedge

end MinModulus
