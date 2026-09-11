import MinModulus.PrefixCertificateClosed

namespace MinModulus.PrefixCertificate

def NoUnitPairs (N : ℕ) (p : List ℕ) : Prop :=
  ∀ a ∈ p, ∀ b ∈ p, ¬ IsUnit ((b : ZMod N) - (a : ZMod N))

theorem noUnitPairs_of_prefix {N : ℕ} {p q : List ℕ}
    (hprefix : p <+: q) (hq : NoUnitPairs N q) : NoUnitPairs N p := by
  obtain ⟨s, rfl⟩ := hprefix
  intro a ha b hb
  exact hq a (List.mem_append_left s ha) b (List.mem_append_left s hb)

def unitPairHit (N : ℕ) (p : List ℕ) (i j : ℕ) : Bool :=
  decide (i < p.length ∧ j < p.length ∧ p.getD i 0 ≤ p.getD j 0 ∧
    Nat.Coprime (p.getD j 0 - p.getD i 0) N)

theorem not_noUnitPairs_of_unitPairHit (N : ℕ) (p : List ℕ) (i j : ℕ)
    (hh : unitPairHit N p i j = true) : ¬ NoUnitPairs N p := by
  simp only [unitPairHit, decide_eq_true_eq] at hh
  obtain ⟨hi, hj, hle, hcoprime⟩ := hh
  simp only [List.getD_eq_getElem, hi, hj] at hle hcoprime
  have hu : IsUnit ((p[j] - p[i] : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcoprime
  rw [Nat.cast_sub hle] at hu
  intro hnu
  exact hnu p[i] (List.getElem_mem hi) p[j] (List.getElem_mem hj) hu

inductive UnitCertificate where
  | stop : ℕ → UnitCertificate
  | unitPair : ℕ → ℕ → UnitCertificate
  | branch : List UnitCertificate → UnitCertificate

def verifyNoUnits (N : ℕ) : ℕ → List ℕ → ℕ → UnitCertificate → Bool
  | _, p, _, .stop code => hitsPacked N p code
  | _, p, _, .unitPair i j => unitPairHit N p i j
  | 0, _, _, .branch _ => false
  | k + 1, p, next, .branch children =>
      decide (children.length = N - next) &&
        (children.zipIdx next).all fun (child, x) ↦
          verifyNoUnits N k (p ++ [x]) (x + 1) child

def ClosedNoUnitPrefix (N k : ℕ) (p : List ℕ) (next : ℕ) : Prop :=
  ∀ s : List ℕ, s.length = k → s.Pairwise (· < ·) →
    (∀ x ∈ s, next ≤ x) → (∀ x ∈ s, x < N) →
    ¬ (ListValid N (p ++ s) ∧ NoUnitPairs N (p ++ s))

theorem closedNoUnitPrefix_of_verify (N k : ℕ) (p : List ℕ) (next : ℕ)
    (cert : UnitCertificate) (hc : verifyNoUnits N k p next cert = true) :
    ClosedNoUnitPrefix N k p next := by
  induction k generalizing p next cert with
  | zero =>
    intro s hlen _ _ _ hgood
    have hs : s = [] := List.length_eq_zero_iff.mp hlen
    subst s
    simp only [List.append_nil] at hgood
    cases cert with
    | stop code =>
      have hh : hits N p (decode code p.length) = true := by
        simpa only [hits_eq_hitsPacked, verifyNoUnits] using hc
      exact not_listValid_of_hits N p _ hh hgood.1
    | unitPair i j => exact not_noUnitPairs_of_unitPairHit N p i j hc hgood.2
    | branch children => simp [verifyNoUnits] at hc
  | succ k ih =>
    intro s hlen hmono hlo hhi hgood
    cases cert with
    | stop code =>
      have hh : hits N p (decode code p.length) = true := by
        simpa only [hits_eq_hitsPacked, verifyNoUnits] using hc
      exact not_listValid_of_hits N p _ hh (listValid_of_prefix ⟨s, rfl⟩ hgood.1)
    | unitPair i j =>
      exact not_noUnitPairs_of_unitPairHit N p i j hc
        (noUnitPairs_of_prefix ⟨s, rfl⟩ hgood.2)
    | branch children =>
      cases s with
      | nil => simp at hlen
      | cons x s =>
        have hxlo := hlo x (by simp)
        have hxhi := hhi x (by simp)
        have hm := List.pairwise_cons.mp hmono
        simp only [verifyNoUnits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
        have hjlt : x - next < children.length := by omega
        have hmem : (children[x - next], next + (x - next)) ∈ children.zipIdx next := by
          apply List.mk_add_mem_zipIdx_iff_getElem?.mpr
          exact List.getElem?_eq_getElem hjlt
        have hh := hc.2 _ hmem
        rw [show next + (x - next) = x by omega] at hh
        have hclosed := ih (p ++ [x]) (x + 1) children[x - next] hh s
          (by simpa using hlen) hm.2
          (by intro y hy; have := hm.1 y hy; omega)
          (by intro y hy; exact hhi y (by simp [hy]))
        exact hclosed (by simpa [List.append_assoc] using hgood)

theorem closedNoUnitPrefix_of_children (N k : ℕ) (p : List ℕ) (next : ℕ)
    (hchildren : ∀ x : ℕ, next ≤ x → x < N → ClosedNoUnitPrefix N k (p ++ [x]) (x + 1)) :
    ClosedNoUnitPrefix N (k + 1) p next := by
  intro s hlen hmono hlo hhi
  cases s with
  | nil => simp at hlen
  | cons x s =>
    have hxlo := hlo x (by simp)
    have hxhi := hhi x (by simp)
    have hm := List.pairwise_cons.mp hmono
    have hclosed := hchildren x hxlo hxhi s (by simpa using hlen) hm.2
      (by intro y hy; have := hm.1 y hy; omega)
      (by intro y hy; exact hhi y (by simp [hy]))
    simpa [List.append_assoc] using hclosed

end MinModulus.PrefixCertificate
