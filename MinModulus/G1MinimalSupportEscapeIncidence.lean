/-
# Coefficient-floor escapes from minimal support deletion

Every coordinate deleted by a minimal protected support transversal owns a
private half witness.  Subtracting that witness from twice the protected
quarter witness would give a zero relation.  Original validity therefore
forces the coefficient floor to fail somewhere.  This file records those
failures as finite incidences covering the deletion set.
-/
import MinModulus.G1MinimalSupportTransversal

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- If `q` is a quarter witness and `c` a half witness, with `q` zero but `c`
nonzero at some coordinate, then validity forces a coefficient-floor escape
for `2q-c`. -/
theorem exists_twice_quarter_coefficientEscape
    (g : Fin m → G) (hg : ValidTuple g)
    {t : G} {q c : Fin m → ℤ}
    (hq : Witness g t q) (hc : Witness g (t + t) c)
    {b : Fin m} (hqb : q b = 0) (hcb : c b ≠ 0) :
    ∃ i : Fin m, 2 * q i + 2 ≤ c i := by
  have hne : q + q - c ≠ 0 := by
    intro heq
    have hb := congrFun heq b
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, hqb] at hb
    omega
  by_contra hescape
  simp only [not_exists, not_le] at hescape
  have hfloor : ∀ i, -1 ≤ (q + q - c) i := by
    intro i
    have hi := hescape i
    simp only [Pi.sub_apply, Pi.add_apply]
    omega
  exact (validTuple_iff_no_zero_witness g).mp hg (q + q - c)
    (witness_twice_sub_at_zero g hq hc hne hfloor)

/-- All coefficient-floor escape incidences of the canonically selected
private witnesses.  The first coordinate is a member of the minimal deletion
set, and the second is a coordinate where `2q-c_b` violates its floor. -/
noncomputable def minimalSupportPrivateEscapePairs
    (g : Fin m → G) (h : G) (q : Fin m → ℤ)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ({b : Fin m // b ∈ B} × Fin m) := by
  classical
  exact (B.attach ×ˢ Finset.univ).filter (fun p ↦
    2 * q p.2 + 2 ≤ minimalSupportPrivateWitness g h hmin p.1 p.2)

@[simp] theorem mem_minimalSupportPrivateEscapePairs_iff
    (g : Fin m → G) (h : G) (q : Fin m → ℤ)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {b : Fin m // b ∈ B}) (i : Fin m) :
    (b, i) ∈ minimalSupportPrivateEscapePairs g h q hmin ↔
      2 * q i + 2 ≤ minimalSupportPrivateWitness g h hmin b i := by
  classical
  simp [minimalSupportPrivateEscapePairs]

/-- Every deleted coordinate has at least one coefficient-floor escape. -/
theorem exists_minimalSupportPrivateEscape
    (g : Fin m → G) (hg : ValidTuple g) {h t : G}
    {q : Fin m → ℤ} (ht : t + t = h) (hq : Witness g t q)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (b : {b : Fin m // b ∈ B}) :
    ∃ i : Fin m,
      (b, i) ∈ minimalSupportPrivateEscapePairs g h q hmin := by
  have hc : Witness g h (minimalSupportPrivateWitness g h hmin b) :=
    minimalSupportPrivateWitness_isWitness g h hmin b
  have hc' : Witness g (t + t)
      (minimalSupportPrivateWitness g h hmin b) := by
    rwa [ht]
  obtain ⟨i, hi⟩ := exists_twice_quarter_coefficientEscape
    g hg hq hc' (hqzero b b.property)
      (minimalSupportPrivateWitness_ne_zero g h hmin b)
  exact ⟨i, (mem_minimalSupportPrivateEscapePairs_iff
    g h q hmin b i).2 hi⟩

/-- Escape incidences project onto the whole deletion set. -/
theorem image_fst_minimalSupportPrivateEscapePairs_eq
    (g : Fin m → G) (hg : ValidTuple g) {h t : G}
    {q : Fin m → ℤ} (ht : t + t = h) (hq : Witness g t q)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0) :
    (minimalSupportPrivateEscapePairs g h q hmin).image Prod.fst =
      B.attach := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hb
    subst b
    simp
  · intro hb
    obtain ⟨i, hi⟩ := exists_minimalSupportPrivateEscape
      g hg ht hq hmin hqzero b
    exact Finset.mem_image.mpr ⟨(b, i), hi, rfl⟩

/-- Counted consequence: there is at least one distinct ordered escape
incidence for every coordinate deleted. -/
theorem card_le_card_minimalSupportPrivateEscapePairs
    (g : Fin m → G) (hg : ValidTuple g) {h t : G}
    {q : Fin m → ℤ} (ht : t + t = h) (hq : Witness g t q)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0) :
    B.card ≤ (minimalSupportPrivateEscapePairs g h q hmin).card := by
  have hproj := image_fst_minimalSupportPrivateEscapePairs_eq
    g hg ht hq hmin hqzero
  calc
    B.card = B.attach.card := by simp
    _ = ((minimalSupportPrivateEscapePairs g h q hmin).image
        Prod.fst).card := (congrArg Finset.card hproj).symm
    _ ≤ (minimalSupportPrivateEscapePairs g h q hmin).card :=
      Finset.card_image_le

/-- An escape of the private witness at `b` cannot occur at another deleted
coordinate. -/
theorem minimalSupportPrivateEscape_eq_self_or_external
    (g : Fin m → G) (h : G) (q : Fin m → ℤ)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ b ∈ B, q b = 0)
    (b : {b : Fin m // b ∈ B}) (i : Fin m)
    (hi : (b, i) ∈ minimalSupportPrivateEscapePairs g h q hmin) :
    i = b ∨ i ∉ B := by
  by_cases hiB : i ∈ B
  · left
    by_contra hib
    have hci := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b hiB hib
    have hqi := hqzero i hiB
    have hescape := (mem_minimalSupportPrivateEscapePairs_iff
      g h q hmin b i).1 hi
    omega
  · exact Or.inr hiB

/-- The enhanced quantitative package: protected descent loses exactly
`B.card` coordinates, while a finite escape-incidence family of cardinality
at least `B.card` records where validity forces the corresponding private
witnesses to carry excess coefficient mass. -/
theorem quarterWitness_minimalExternalSupportEscapeIncidences
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    {t : ZMod N} {q : Fin m → ℤ}
    (ht : t + t = (M : ZMod N)) (hq : Witness g t q)
    (hkernel : ∀ c : Fin m → ℤ, Witness g (M : ZMod N) c →
      (∀ i : Fin m, q i = 0 → c i = 0) → False) :
    ∃ B : Finset (Fin m),
      ∃ hmin : MinimalWitnessSupportTransversal
        g (M : ZMod N) B,
      B ⊆ Finset.univ \ coefficientSupport q ∧
      AdmitsValidTupleWithWitness (m - B.card) M (K : ZMod M) ∧
      B.card ≤
        (minimalSupportPrivateEscapePairs
          g (M : ZMod N) q hmin).card ∧
      ∀ p ∈ minimalSupportPrivateEscapePairs
          g (M : ZMod N) q hmin,
        p.2 = p.1 ∨ p.2 ∉ B := by
  obtain ⟨B, hBsub, hmin, hrec, _hprivate⟩ :=
    quarterWitness_minimalExternalSupportDescent
      hN hM hK g hg ht hq hkernel
  have hqzero : ∀ b ∈ B, q b = 0 := by
    intro b hb
    have hbfull := hBsub hb
    have hbnot := (Finset.mem_sdiff.mp hbfull).2
    by_contra hqb
    exact hbnot (by simpa using hqb)
  refine ⟨B, hmin, hBsub, hrec, ?_, ?_⟩
  · exact card_le_card_minimalSupportPrivateEscapePairs
      g hg ht hq hmin hqzero
  · intro p hp
    exact minimalSupportPrivateEscape_eq_self_or_external
      g (M : ZMod N) q hmin hqzero p.1 p.2 hp

end MinModulus
