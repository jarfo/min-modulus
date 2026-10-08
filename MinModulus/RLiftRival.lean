import MinModulus.RLiftBits
import MinModulus.RLiftSheetChain

/-!
# Generic rival engines for sheeted lifts

The master lemma `rival_vector_ne`: over any tuple of the form
`g i = (r i : ZMod N) + β i` with 2-torsion bits `β`, validity makes
every admissible integer coefficient vector (floor `-1`, zero sum,
somewhere nonzero) have nonzero value — integer part plus odd-support
bits.  On top of it, the seven fixed small-support shapes used by the
R-lift grid table, each generic in the integer representatives `r`.
-/

namespace MinModulus

open Finset

/-- Sum of a function supported on at most six points. -/
lemma sum_eq_of_six {n : ℕ} {A : Type*} [AddCommMonoid A] (f : Fin n → A)
    (p q s t u v : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (h : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → i ≠ u → i ≠ v → f i = 0) :
    ∑ i, f i = f p + f q + f s + f t + f u + f v := by
  classical
  rw [← Finset.sum_subset
    (Finset.subset_univ ({p, q, s, t, u, v} : Finset (Fin n)))]
  · rw [Finset.sum_insert (by simp [hpq, hps, hpt, hpu, hpv]),
        Finset.sum_insert (by simp [hqs, hqt, hqu, hqv]),
        Finset.sum_insert (by simp [hst, hsu, hsv]),
        Finset.sum_insert (by simp [htu, htv]),
        Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
    abel
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

section Engines

variable {n N : ℕ} {g β : Fin n → ZMod N} {r : Fin n → ℕ}

/-- **Master rival lemma.**  Any integer coefficient vector with floor
`-1`, zero sum, and a nonzero coordinate has nonzero value on a valid
sheeted tuple: exact integer part plus the odd-support bits. -/
lemma rival_vector_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (c : Fin n → ℤ)
    (hfloor : ∀ i, -1 ≤ c i) (hsum : ∑ i, c i = 0)
    {j : Fin n} (hj : c j ≠ 0) :
    (((∑ i, c i * (r i : ℤ)) : ℤ) : ZMod N)
      + ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i ≠ 0 := by
  classical
  set κ : Fin n → ℕ := fun i => (c i + 1).toNat with hκdef
  have hκc : ∀ i, (κ i : ℤ) = c i + 1 := by
    intro i
    simp only [hκdef]
    exact Int.toNat_of_nonneg (by linarith [hfloor i])
  have hκsum : ∑ i, κ i = n := by
    have hcast : ((∑ i, κ i : ℕ) : ℤ) = (n : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun i _ => hκc i, Finset.sum_add_distrib, hsum,
          zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    exact_mod_cast hcast
  have hj1 : κ j ≠ 1 := by
    intro h
    apply hj
    have hcj := hκc j
    rw [h] at hcj
    omega
  have hne := validTuple_no_shifted_rival hv κ hκsum hj1
  have hcc : ∀ i : Fin n, ((κ i : ℤ) - 1) • g i = c i • g i := by
    intro i
    rw [hκc i]
    ring_nf
  rw [Finset.sum_congr rfl fun i _ => hcc i] at hne
  rw [shifted_sum_eq c r β g hβ2 hg] at hne
  exact hne

/-- Shape `(+1, -1)`: the swap rival. -/
lemma rival_pm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q : Fin n) (hpq : p ≠ q) :
    ((((r p : ℤ) - r q) : ℤ) : ZMod N) + (β p + β q) ≠ 0 := by
  classical
  set c : Fin n → ℤ := fun i => if i = p then 1 else if i = q then -1 else 0
    with hc
  have hcp : c p = 1 := by simp [hc]
  have hcq : c q = -1 := by simp [hc, Ne.symm hpq]
  have hco : ∀ i, i ≠ p → i ≠ q → c i = 0 := by
    intro i h1 h2; simp [hc, h1, h2]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]
    · rw [hco i h1 h2]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_two c p q hpq hco, hcp, hcq]; ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ) = (r p : ℤ) - r q := by
    rw [sum_eq_of_two (fun i => c i * (r i : ℤ)) p q hpq
      (by intro i h1 h2; simp [hco i h1 h2]), hcp, hcq]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β p + β q := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_two (fun i => if Odd (c i) then β i else 0) p q hpq
      (by intro i h1 h2; rw [hco i h1 h2]; norm_num)]
    rw [hcp, hcq]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+2, -1, -1)`: the three-point rival. -/
lemma rival_2mm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q s : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    (((2 * (r p : ℤ) - r q - r s) : ℤ) : ZMod N) + (β q + β s) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 2 else if i = q then -1 else if i = s then -1
      else 0 with hc
  have hcp : c p = 2 := by simp [hc]
  have hcq : c q = -1 := by simp [hc, Ne.symm hpq]
  have hcs : c s = -1 := by simp [hc, Ne.symm hps, Ne.symm hqs]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ s → c i = 0 := by
    intro i h1 h2 h3; simp [hc, h1, h2, h3]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]
    by_cases h3 : i = s
    · subst h3; rw [hcs]
    · rw [hco i h1 h2 h3]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_three c p q s hpq hps hqs hco, hcp, hcq, hcs]; ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ) = 2 * (r p : ℤ) - r q - r s := by
    rw [sum_eq_of_three (fun i => c i * (r i : ℤ)) p q s hpq hps hqs
      (by intro i h1 h2 h3; simp [hco i h1 h2 h3]), hcp, hcq, hcs]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β q + β s := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_two (fun i => if Odd (c i) then β i else 0) q s hqs (by
      intro i h2 h3
      by_cases h1 : i = p
      · subst h1; rw [hcp]; norm_num
      · rw [hco i h1 h2 h3]; norm_num)]
    rw [hcq, hcs]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+3, -1, -1, -1)`. -/
lemma rival_3mmm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q s t : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) :
    (((3 * (r p : ℤ) - r q - r s - r t) : ℤ) : ZMod N)
      + (β p + β q + β s + β t) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 3 else if i = q then -1 else if i = s then -1
      else if i = t then -1 else 0 with hc
  have hcp : c p = 3 := by simp [hc]
  have hcq : c q = -1 := by simp [hc, Ne.symm hpq]
  have hcs : c s = -1 := by simp [hc, Ne.symm hps, Ne.symm hqs]
  have hct : c t = -1 := by simp [hc, Ne.symm hpt, Ne.symm hqt, Ne.symm hst]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → c i = 0 := by
    intro i h1 h2 h3 h4; simp [hc, h1, h2, h3, h4]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]
    by_cases h3 : i = s
    · subst h3; rw [hcs]
    by_cases h4 : i = t
    · subst h4; rw [hct]
    · rw [hco i h1 h2 h3 h4]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_four c p q s t hpq hps hpt hqs hqt hst hco,
        hcp, hcq, hcs, hct]
    ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ)
      = 3 * (r p : ℤ) - r q - r s - r t := by
    rw [sum_eq_of_four (fun i => c i * (r i : ℤ)) p q s t
      hpq hps hpt hqs hqt hst
      (by intro i h1 h2 h3 h4; simp [hco i h1 h2 h3 h4]),
      hcp, hcq, hcs, hct]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β p + β q + β s + β t := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_four (fun i => if Odd (c i) then β i else 0) p q s t
      hpq hps hpt hqs hqt hst
      (by intro i h1 h2 h3 h4; rw [hco i h1 h2 h3 h4]; norm_num)]
    rw [hcp, hcq, hcs, hct]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+1, +1, -1, -1)`. -/
lemma rival_ppmm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q s t : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) :
    ((((r p : ℤ) + r q - r s - r t) : ℤ) : ZMod N)
      + (β p + β q + β s + β t) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 1 else if i = q then 1 else if i = s then -1
      else if i = t then -1 else 0 with hc
  have hcp : c p = 1 := by simp [hc]
  have hcq : c q = 1 := by simp [hc, Ne.symm hpq]
  have hcs : c s = -1 := by simp [hc, Ne.symm hps, Ne.symm hqs]
  have hct : c t = -1 := by simp [hc, Ne.symm hpt, Ne.symm hqt, Ne.symm hst]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → c i = 0 := by
    intro i h1 h2 h3 h4; simp [hc, h1, h2, h3, h4]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]; norm_num
    by_cases h3 : i = s
    · subst h3; rw [hcs]
    by_cases h4 : i = t
    · subst h4; rw [hct]
    · rw [hco i h1 h2 h3 h4]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_four c p q s t hpq hps hpt hqs hqt hst hco,
        hcp, hcq, hcs, hct]
    ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ)
      = (r p : ℤ) + r q - r s - r t := by
    rw [sum_eq_of_four (fun i => c i * (r i : ℤ)) p q s t
      hpq hps hpt hqs hqt hst
      (by intro i h1 h2 h3 h4; simp [hco i h1 h2 h3 h4]),
      hcp, hcq, hcs, hct]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β p + β q + β s + β t := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_four (fun i => if Odd (c i) then β i else 0) p q s t
      hpq hps hpt hqs hqt hst
      (by intro i h1 h2 h3 h4; rw [hco i h1 h2 h3 h4]; norm_num)]
    rw [hcp, hcq, hcs, hct]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+2, +1, -1, -1, -1)`. -/
lemma rival_21mmm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q a b d : Fin n)
    (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b) (hpd : p ≠ d)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqd : q ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (((2 * (r p : ℤ) + r q - r a - r b - r d) : ℤ) : ZMod N)
      + (β q + β a + β b + β d) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 2 else if i = q then 1 else if i = a then -1
      else if i = b then -1 else if i = d then -1 else 0 with hc
  have hcp : c p = 2 := by simp [hc]
  have hcq : c q = 1 := by simp [hc, Ne.symm hpq]
  have hca : c a = -1 := by simp [hc, Ne.symm hpa, Ne.symm hqa]
  have hcb : c b = -1 := by simp [hc, Ne.symm hpb, Ne.symm hqb, Ne.symm hab]
  have hcd : c d = -1 := by
    simp [hc, Ne.symm hpd, Ne.symm hqd, Ne.symm had, Ne.symm hbd]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ a → i ≠ b → i ≠ d → c i = 0 := by
    intro i h1 h2 h3 h4 h5; simp [hc, h1, h2, h3, h4, h5]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]; norm_num
    by_cases h3 : i = a
    · subst h3; rw [hca]
    by_cases h4 : i = b
    · subst h4; rw [hcb]
    by_cases h5 : i = d
    · subst h5; rw [hcd]
    · rw [hco i h1 h2 h3 h4 h5]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_five c p q a b d hpq hpa hpb hpd hqa hqb hqd hab had hbd
      hco, hcp, hcq, hca, hcb, hcd]
    ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ)
      = 2 * (r p : ℤ) + r q - r a - r b - r d := by
    rw [sum_eq_of_five (fun i => c i * (r i : ℤ)) p q a b d
      hpq hpa hpb hpd hqa hqb hqd hab had hbd
      (by intro i h1 h2 h3 h4 h5; simp [hco i h1 h2 h3 h4 h5]),
      hcp, hcq, hca, hcb, hcd]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β q + β a + β b + β d := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_four (fun i => if Odd (c i) then β i else 0) q a b d
      hqa hqb hqd hab had hbd (by
        intro i h2 h3 h4 h5
        by_cases h1 : i = p
        · subst h1; rw [hcp]; norm_num
        · rw [hco i h1 h2 h3 h4 h5]; norm_num)]
    rw [hcq, hca, hcb, hcd]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+1, +1, +1, -1, -1, -1)`. -/
lemma rival_pppmmm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q s t u v : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    ((((r p : ℤ) + r q + r s - r t - r u - r v) : ℤ) : ZMod N)
      + (β p + β q + β s + β t + β u + β v) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 1 else if i = q then 1 else if i = s then 1
      else if i = t then -1 else if i = u then -1 else if i = v then -1
      else 0 with hc
  have hcp : c p = 1 := by simp [hc]
  have hcq : c q = 1 := by simp [hc, Ne.symm hpq]
  have hcs : c s = 1 := by simp [hc, Ne.symm hps, Ne.symm hqs]
  have hct : c t = -1 := by simp [hc, Ne.symm hpt, Ne.symm hqt, Ne.symm hst]
  have hcu : c u = -1 := by
    simp [hc, Ne.symm hpu, Ne.symm hqu, Ne.symm hsu, Ne.symm htu]
  have hcv : c v = -1 := by
    simp [hc, Ne.symm hpv, Ne.symm hqv, Ne.symm hsv, Ne.symm htv, Ne.symm huv]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → i ≠ u → i ≠ v →
      c i = 0 := by
    intro i h1 h2 h3 h4 h5 h6; simp [hc, h1, h2, h3, h4, h5, h6]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]; norm_num
    by_cases h3 : i = s
    · subst h3; rw [hcs]; norm_num
    by_cases h4 : i = t
    · subst h4; rw [hct]
    by_cases h5 : i = u
    · subst h5; rw [hcu]
    by_cases h6 : i = v
    · subst h6; rw [hcv]
    · rw [hco i h1 h2 h3 h4 h5 h6]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_six c p q s t u v hpq hps hpt hpu hpv hqs hqt hqu hqv
      hst hsu hsv htu htv huv hco, hcp, hcq, hcs, hct, hcu, hcv]
    ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ)
      = (r p : ℤ) + r q + r s - r t - r u - r v := by
    rw [sum_eq_of_six (fun i => c i * (r i : ℤ)) p q s t u v
      hpq hps hpt hpu hpv hqs hqt hqu hqv hst hsu hsv htu htv huv
      (by intro i h1 h2 h3 h4 h5 h6; simp [hco i h1 h2 h3 h4 h5 h6]),
      hcp, hcq, hcs, hct, hcu, hcv]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β p + β q + β s + β t + β u + β v := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_six (fun i => if Odd (c i) then β i else 0) p q s t u v
      hpq hps hpt hpu hpv hqs hqt hqu hqv hst hsu hsv htu htv huv
      (by intro i h1 h2 h3 h4 h5 h6; rw [hco i h1 h2 h3 h4 h5 h6]; norm_num)]
    rw [hcp, hcq, hcs, hct, hcu, hcv]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

/-- Shape `(+2, +2, -1, -1, -1, -1)`. -/
lemma rival_22mmmm_ne
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod N) + β i)
    (hv : ValidTuple g) (p q s t u v : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    (((2 * (r p : ℤ) + 2 * r q - r s - r t - r u - r v) : ℤ) : ZMod N)
      + (β s + β t + β u + β v) ≠ 0 := by
  classical
  set c : Fin n → ℤ :=
    fun i => if i = p then 2 else if i = q then 2 else if i = s then -1
      else if i = t then -1 else if i = u then -1 else if i = v then -1
      else 0 with hc
  have hcp : c p = 2 := by simp [hc]
  have hcq : c q = 2 := by simp [hc, Ne.symm hpq]
  have hcs : c s = -1 := by simp [hc, Ne.symm hps, Ne.symm hqs]
  have hct : c t = -1 := by simp [hc, Ne.symm hpt, Ne.symm hqt, Ne.symm hst]
  have hcu : c u = -1 := by
    simp [hc, Ne.symm hpu, Ne.symm hqu, Ne.symm hsu, Ne.symm htu]
  have hcv : c v = -1 := by
    simp [hc, Ne.symm hpv, Ne.symm hqv, Ne.symm hsv, Ne.symm htv, Ne.symm huv]
  have hco : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → i ≠ u → i ≠ v →
      c i = 0 := by
    intro i h1 h2 h3 h4 h5 h6; simp [hc, h1, h2, h3, h4, h5, h6]
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    by_cases h1 : i = p
    · subst h1; rw [hcp]; norm_num
    by_cases h2 : i = q
    · subst h2; rw [hcq]; norm_num
    by_cases h3 : i = s
    · subst h3; rw [hcs]
    by_cases h4 : i = t
    · subst h4; rw [hct]
    by_cases h5 : i = u
    · subst h5; rw [hcu]
    by_cases h6 : i = v
    · subst h6; rw [hcv]
    · rw [hco i h1 h2 h3 h4 h5 h6]; norm_num
  have hsum : ∑ i, c i = 0 := by
    rw [sum_eq_of_six c p q s t u v hpq hps hpt hpu hpv hqs hqt hqu hqv
      hst hsu hsv htu htv huv hco, hcp, hcq, hcs, hct, hcu, hcv]
    ring
  have h := rival_vector_ne hβ2 hg hv c hfloor hsum
    (j := p) (by rw [hcp]; norm_num)
  have hint : ∑ i, c i * (r i : ℤ)
      = 2 * (r p : ℤ) + 2 * r q - r s - r t - r u - r v := by
    rw [sum_eq_of_six (fun i => c i * (r i : ℤ)) p q s t u v
      hpq hps hpt hpu hpv hqs hqt hqu hqv hst hsu hsv htu htv huv
      (by intro i h1 h2 h3 h4 h5 h6; simp [hco i h1 h2 h3 h4 h5 h6]),
      hcp, hcq, hcs, hct, hcu, hcv]
    ring
  have hfil : ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i
      = β s + β t + β u + β v := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_four (fun i => if Odd (c i) then β i else 0) s t u v
      hst hsu hsv htu htv huv (by
        intro i h3 h4 h5 h6
        by_cases h1 : i = p
        · subst h1; rw [hcp]; norm_num
        by_cases h2 : i = q
        · subst h2; rw [hcq]; norm_num
        · rw [hco i h1 h2 h3 h4 h5 h6]; norm_num)]
    rw [hcs, hct, hcu, hcv]
    norm_num
  rw [hint, hfil] at h
  exact fun hh => h (by rw [← hh])

end Engines

end MinModulus
