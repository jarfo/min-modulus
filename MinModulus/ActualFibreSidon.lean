import MinModulus.ActualFibreMixedRivals

/-!
# Arbitrary-fibre Sidon counting or actual half-modulus descent

Validity makes every squarefree two-coordinate sum uniquely represented.
The only remaining unordered-pair collisions involve two repeated
coordinates. In a cyclic parent those collisions supply an antipodal
pair and hence an ACTUAL smaller valid tuple at half the modulus.

Consequently, without half descent every actual m-entry cyclic fibre
has exactly binom(m+1,2) two-coin sums. Two odd outsiders then require
at least binom(m+1,2) missing own-size sums. At odd fibre order the sharp
count and deficit hold outright. All subgroup indices and actual fibre
shapes are allowed; no SI, primitive, zero-entry, or criticality premise.
This sharpens the same general G1 residual, not a closure of G1/G2/G3.
-/

namespace MinModulus
open Finset

/-- A squarefree two-coordinate sum in a valid tuple has no different
two-coin representation, in any additive commutative group. -/
theorem pair_sum_eq_of_validTuple
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (u : Fin m → G) (hu : ValidTuple u)
    (a b c d : Fin m) (hab : a ≠ b) (heq : u a+u b=u c+u d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  classical
  have hc : c ∈ ({a,b} : Finset (Fin m)) := by
    by_contra hc
    exact not_validTuple_of_multiset_sum_eq_finset_with_outside u {a,b} {c,d}
      (by simp [hab]) (by simpa [hab] using heq.symm) c (by simp) hc hu
  rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hc : c=a ∨ c=b) with hca | hcb
  · subst c
    exact Or.inl ⟨rfl, validTuple_injective u hu (add_left_cancel heq)⟩
  · subst c
    have hda : d=a := validTuple_injective u hu (by simpa only [add_comm] using add_left_cancel (heq.symm.trans (add_comm _ _)))
    exact Or.inr ⟨hda.symm, rfl⟩

/-- Only two repeated-coordinate sums can collide in a valid tuple. -/
theorem pair_sum_eq_or_diagonal_of_validTuple
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (u : Fin m → G) (hu : ValidTuple u)
    (a b c d : Fin m) (heq : u a+u b=u c+u d) :
    ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) ∨ (a=b ∧ c=d) := by
  by_cases hab : a=b
  · by_cases hcd : c=d
    · exact Or.inr ⟨hab,hcd⟩
    · have h := pair_sum_eq_of_validTuple u hu c d a b hcd heq.symm
      exact Or.inl (by rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩; exact Or.inl ⟨h1.symm,h2.symm⟩; exact Or.inr ⟨h2.symm,h1.symm⟩)
  · exact Or.inl (pair_sum_eq_of_validTuple u hu a b c d hab heq)

/-- With injective doubling on the coordinates, validity makes every
unordered two-coin sum distinct. -/
theorem actual_fibre_pair_sum_injective_of_doubling_injective
    {m M : ℕ} [NeZero M] (u : Fin m → ZMod M) (hu : ValidTuple u)
    (hdouble : Function.Injective (fun i ↦ 2 • u i)) :
    Function.Injective (fun p : Sym2 (Fin m) ↦ (p.toMultiset.map u).sum) := by
  intro p q
  induction p, q using Sym2.inductionOn₂ with
  | hf a b c d =>
    intro heq
    have heq' : u a+u b=u c+u d := by simpa [Sym2.toMultiset] using heq
    apply Sym2.eq_iff.mpr
    rcases pair_sum_eq_or_diagonal_of_validTuple u hu a b c d heq' with h | ⟨hab,hcd⟩
    · exact h
    · subst b; subst d
      have hac : a=c := hdouble (by simpa only [two_nsmul] using heq')
      exact Or.inl ⟨hac,hac⟩

/-- Exact sharp two-coin cardinality when doubling is injective on a
valid fibre. This counts unordered pairs including repetitions. -/
theorem actual_fibre_two_coin_card_eq_of_doubling_injective
    {m M : ℕ} [NeZero M] (u : Fin m → ZMod M) (hu : ValidTuple u)
    (hdouble : Function.Injective (fun i ↦ 2 • u i)) :
    (actualFibreCoinCover u 2).card=(m+1).choose 2 := by
  classical
  let value : Sym2 (Fin m) → ZMod M := fun p ↦ (p.toMultiset.map u).sum
  have heq : actualFibreCoinCover u 2=Finset.univ.image value := by
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs, hsum⟩ := (Finset.mem_filter.mp hz).2
      obtain ⟨a,b,rfl⟩ := Multiset.card_eq_two.mp hs
      exact Finset.mem_image.mpr ⟨s(a,b), Finset.mem_univ _, by simpa [value, Sym2.toMultiset] using hsum⟩
    · intro hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.toMultiset, Sym2.card_toMultiset p, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (actual_fibre_pair_sum_injective_of_doubling_injective u hu hdouble)]
  rw [← Finset.sym2_univ, Finset.card_sym2]
  simp

/-- At odd order, every valid tuple is Sidon: all unordered two-coin
sums are distinct, without a primitive or SI assumption. -/
theorem actual_fibre_two_coin_card_eq_of_odd
    {m M : ℕ} [NeZero M] (hM : Odd M) (u : Fin m → ZMod M) (hu : ValidTuple u) :
    (actualFibreCoinCover u 2).card=(m+1).choose 2 := by
  apply actual_fibre_two_coin_card_eq_of_doubling_injective u hu
  intro a b h
  apply validTuple_injective u hu
  apply ((ZMod.isUnit_iff_coprime 2 M).mpr hM.coprime_two_left).mul_left_cancel
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h

/-- A collision between doubled parent coordinates gives ACTUAL
one-coordinate half-modulus descent, using the unique cyclic involution. -/
theorem admitsValidTuple_half_of_doubled_coordinate_collision
    {n M : ℕ} [NeZero M] (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (a b : Fin (n+1)) (hab : a ≠ b) (heq : 2 • g a=2 • g b) :
    AdmitsValidTuple n M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  have hzero : (g a-g b)+(g a-g b)=0 := by
    simp only [two_nsmul] at heq
    calc
      (g a-g b)+(g a-g b)=(g a+g a)-(g b+g b) := by abel
      _=0 := sub_eq_zero.mpr heq
  rcases zmod_eq_zero_or_half_of_add_self_eq_zero rfl (g a-g b) hzero with hz | hh
  · exact (hab (validTuple_injective g hg (sub_eq_zero.mp hz))).elim
  · exact exists_validTuple_half_of_pair rfl hMpos hg hh

/-- Without actual half deletion, every embedded actual cyclic fibre
has injective coordinate doubling, at ANY subgroup index. -/
theorem actual_fibre_doubling_injective_of_no_half_descent
    {n m M L : ℕ} [NeZero M] [NeZero L]
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod L) (f : Fin m ↪ Fin (n+1))
    (τ : ZMod L →+ ZMod (2*M)) (hpref : ∀ i, g (f i)=τ (u i))
    (hno : ¬AdmitsValidTuple n M) : Function.Injective (fun i ↦ 2 • u i) := by
  intro a b hab
  by_contra hne
  apply hno
  apply admitsValidTuple_half_of_doubled_coordinate_collision g hg (f a) (f b)
    (fun h ↦ hne (f.injective h))
  rw [hpref, hpref, ← map_nsmul, ← map_nsmul]
  exact congrArg τ hab

/-- General G1 dichotomy: either the required smaller valid tuple
already exists, or every actual cyclic fibre has the sharp Sidon count.
No criticality, fibre shape, zero entry, or quotient-validity premise. -/
theorem admitsValidTuple_half_or_actual_fibre_two_coin_card_eq
    {n m M L : ℕ} [NeZero M] [NeZero L]
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod L) (f : Fin m ↪ Fin (n+1))
    (τ : ZMod L →+ ZMod (2*M)) (hpref : ∀ i, g (f i)=τ (u i)) :
    AdmitsValidTuple n M ∨ (actualFibreCoinCover u 2).card=(m+1).choose 2 := by
  by_cases h : AdmitsValidTuple n M
  · exact Or.inl h
  · apply Or.inr
    have hu : ValidTuple u := by
      apply validTuple_of_comp τ
      simpa only [hpref] using validTuple_embedding f g hg
    exact actual_fibre_two_coin_card_eq_of_doubling_injective u hu
      (actual_fibre_doubling_injective_of_no_half_descent g hg u f τ hpref h)

/-- Direct arbitrary-fibre G1 restriction: either actual half deletion
holds, or two odd outsiders force binom(m+1,2) missing own-size sums. -/
theorem admitsValidTuple_half_or_actual_even_fibre_sharp_deficit
    {m k M : ℕ} [NeZero M]
    (g : Fin (m+(k+1)) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=zmodScaleHom 2 M (u i))
    (j l : Fin (k+1)) (hjl : j ≠ l)
    (hj : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m j))=1)
    (hl : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m l))=1) :
    AdmitsValidTuple (m+k) M ∨ (actualFibreOwnSizeCover u).card+(m+1).choose 2 ≤ M := by
  rcases admitsValidTuple_half_or_actual_fibre_two_coin_card_eq g hg u
    ⟨Fin.castAdd (k+1), Fin.castAdd_injective m (k+1)⟩ (zmodScaleHom 2 M) hpref with h | h
  · exact Or.inl h
  · right
    have hpack := actual_even_fibre_own_cover_card_add_two_coin_card_le g hg u hpref j l hjl hj hl
    rwa [h] at hpack

/-- In the first-even stratum the sharp deficit holds outright:
odd fibre order precludes repeated-coordinate sum collisions. -/
theorem actual_first_even_fibre_sharp_deficit
    {m k M : ℕ} [NeZero M] (hM : Odd M)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom 2 M (u i))
    (j l : Fin k) (hjl : j ≠ l)
    (hj : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m j))=1)
    (hl : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.natAdd m l))=1) :
    (actualFibreOwnSizeCover u).card+(m+1).choose 2 ≤ M := by
  have hu : ValidTuple u := by
    apply validTuple_of_comp (zmodScaleHom 2 M)
    have hv := validTuple_embedding ⟨Fin.castAdd k, Fin.castAdd_injective m k⟩ g hg
    change ValidTuple (fun i : Fin m ↦ g (Fin.castAdd k i)) at hv
    simpa only [hpref] using hv
  have hpack := actual_even_fibre_own_cover_card_add_two_coin_card_le g hg u hpref j l hjl hj hl
  rwa [actual_fibre_two_coin_card_eq_of_odd hM u hu] at hpack

end MinModulus
