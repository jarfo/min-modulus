import MinModulus.SortedValidTuples

namespace MinModulus.PrefixCertificate

open Finset

def dot : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: r, b :: p => a * b + dot r p

def ListValid (N : ℕ) (p : List ℕ) : Prop :=
  ValidTuple (fun i : Fin p.length ↦ (p[i] : ZMod N))

def hits (N : ℕ) (p r : List ℕ) : Bool :=
  decide (r.length = p.length ∧ r.sum = p.length ∧
    ¬ r = List.replicate p.length 1 ∧ dot r p % N = p.sum % N)

def covered (N : ℕ) (p : List ℕ) (rs : List (List ℕ)) : Bool :=
  rs.any fun r ↦ decide (dot r p % N = p.sum % N)

def legalRivals (k : ℕ) (rs : List (List ℕ)) : Bool :=
  rs.all fun r ↦ decide (r.length = k ∧ r.sum = k ∧ ¬ r = List.replicate k 1)

theorem sum_entries (p : List ℕ) : (∑ i : Fin p.length, p[i]) = p.sum := by
  induction p with
  | nil => simp
  | cons a p ih => simpa [Fin.sum_univ_succ] using congrArg (a + ·) ih

theorem dot_entries (p r : List ℕ) (hlen : r.length = p.length) :
    (∑ i : Fin p.length, r[i]'(by omega) * p[i]) = dot r p := by
  induction p generalizing r with
  | nil => cases r <;> simp [dot]
  | cons a p ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      have hlen' : r.length = p.length := by simpa using hlen
      simpa [dot, Fin.sum_univ_succ] using congrArg (b * a + ·) (ih r hlen')

theorem not_listValid_of_hits (N : ℕ) (p r : List ℕ)
    (hh : hits N p r = true) : ¬ ListValid N p := by
  intro hp
  simp only [hits, decide_eq_true_eq] at hh
  obtain ⟨hlen, hsum, hne, hmod⟩ := hh
  let k : Fin p.length → ℕ := fun i ↦ r[i]'(by omega)
  have hk : ∑ i, k i = p.length := by
    calc
      ∑ i, k i = ∑ i : Fin r.length, r[i] :=
        Fintype.sum_equiv (finCongr hlen.symm) _ _ (by intro i; rfl)
      _ = p.length := (sum_entries r).trans hsum
  have heq : (∑ i : Fin p.length, k i • (p[i] : ZMod N)) =
      ∑ i : Fin p.length, (p[i] : ZMod N) := by
    have hd := dot_entries p r hlen
    have hs := sum_entries p
    have he : (dot r p : ZMod N) = (p.sum : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [← hd, ← hs] at he
    simpa [k, Nat.cast_sum, Nat.cast_mul, nsmul_eq_mul] using he
  have hone := hp k hk heq
  apply hne
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have h := hone ⟨i, by omega⟩
    simpa [k] using h

theorem not_listValid_of_covered (N : ℕ) (p : List ℕ) (rs : List (List ℕ))
    (hlegal : legalRivals p.length rs = true)
    (hh : covered N p rs = true) : ¬ ListValid N p := by
  simp only [covered, List.any_eq_true, decide_eq_true_eq] at hh
  obtain ⟨r, hrmem, hr⟩ := hh
  simp only [legalRivals, List.all_eq_true, decide_eq_true_eq] at hlegal
  obtain ⟨hlen, hsum, hne⟩ := hlegal r hrmem
  apply not_listValid_of_hits N p r
  simpa only [hits, decide_eq_true_eq] using And.intro hlen ⟨hsum, hne, hr⟩

theorem listValid_of_prefix {N : ℕ} {p q : List ℕ}
    (hprefix : p <+: q) (hq : ListValid N q) : ListValid N p := by
  obtain ⟨s, rfl⟩ := hprefix
  let e : Fin p.length ↪ Fin (p ++ s).length :=
    ⟨fun i ↦ ⟨i.val, by simp; omega⟩, by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin (p ++ s).length ↦ x.val) h)⟩
  have hh := validTuple_embedding e (fun i : Fin (p ++ s).length ↦
    ((p ++ s)[i] : ZMod N)) hq
  have heq : (fun i : Fin p.length ↦ ((p ++ s)[e i] : ZMod N)) =
      (fun i : Fin p.length ↦ (p[i] : ZMod N)) := by
    funext i
    simp only [Fin.getElem_fin]
    change ((p ++ s)[i.val]'(by simp; omega) : ZMod N) = (p[i.val] : ZMod N)
    rw [List.getElem_append_left i.isLt]
  change ValidTuple (fun i : Fin p.length ↦ ((p ++ s)[e i] : ZMod N)) at hh
  rw [heq] at hh
  exact hh

def check (N : ℕ) (rs : ℕ → List (List ℕ)) : ℕ → List ℕ → ℕ → Bool
  | 0, p, _ => covered N p (rs p.length)
  | k + 1, p, next => covered N p (rs p.length) ||
      (List.range (N - next)).all fun j ↦
        check N rs k (p ++ [next + j]) (next + j + 1)

theorem not_listValid_append_of_check (N : ℕ) (rs : ℕ → List (List ℕ))
    (hlegal : ∀ k, legalRivals k (rs k) = true)
    (k : ℕ) (p : List ℕ) (next : ℕ) (hc : check N rs k p next = true)
    (s : List ℕ) (hlen : s.length = k) (hmono : s.Pairwise (· < ·))
    (hlo : ∀ x ∈ s, next ≤ x) (hhi : ∀ x ∈ s, x < N) :
    ¬ ListValid N (p ++ s) := by
  induction k generalizing p next s with
  | zero =>
    have hs : s = [] := List.length_eq_zero_iff.mp hlen
    subst s
    simpa using not_listValid_of_covered N p (rs p.length) (hlegal _) hc
  | succ k ih =>
    simp only [check, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · intro hv
      exact not_listValid_of_covered N p (rs p.length) (hlegal _) hc
        (listValid_of_prefix ⟨s, rfl⟩ hv)
    · cases s with
      | nil => simp at hlen
      | cons x s =>
        have hxlo := hlo x (by simp)
        have hxhi := hhi x (by simp)
        simp only [List.all_eq_true] at hc
        have hbranch := hc (x-next) (List.mem_range.mpr (by omega))
        rw [show next + (x-next) = x by omega] at hbranch
        have hm := List.pairwise_cons.mp hmono
        have hh := ih (p ++ [x]) (x+1) hbranch s (by simpa using hlen) hm.2
          (by intro y hy; have := hm.1 y hy; omega)
          (by intro y hy; exact hhi y (by simp [hy]))
        simpa [List.append_assoc] using hh

theorem listValid_ofFn {n N : ℕ} (v : Fin n → ℕ)
    (hv : ValidTuple (fun i ↦ (v i : ZMod N))) : ListValid N (List.ofFn v) := by
  let e : Fin (List.ofFn v).length ↪ Fin n :=
    (finCongr (List.length_ofFn)).toEmbedding
  have hh := validTuple_embedding e (fun i ↦ (v i : ZMod N)) hv
  have heq : (fun i : Fin (List.ofFn v).length ↦ (v (e i) : ZMod N)) =
      (fun i : Fin (List.ofFn v).length ↦ ((List.ofFn v)[i] : ZMod N)) := by
    funext i
    simp only [Fin.getElem_fin, List.getElem_ofFn]
    congr 2
  change ValidTuple (fun i : Fin (List.ofFn v).length ↦ ((List.ofFn v)[i] : ZMod N))
  rw [← heq]
  exact hh

theorem not_validTuple_of_check {n N : ℕ} [NeZero N]
    (rs : ℕ → List (List ℕ)) (hlegal : ∀ k, legalRivals k (rs k) = true)
    (hc : check N rs n [0] 1 = true)
    (g : Fin (n+1) → ZMod N) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨v, hv, h0, hlt, hw, _, _⟩ := exists_sorted_valid_nat_tuple g hg
  let s := List.ofFn (fun i : Fin n ↦ v i.succ)
  have hs : s.length = n := by simp [s]
  have hm : s.Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hv (by simpa using hij)
  have hlo : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hi := hv (Fin.succ_pos i)
    omega
  have hhi : ∀ x ∈ s, x < N := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hlt i.succ
  have hno := not_listValid_append_of_check N rs hlegal n [0] 1 hc s hs hm hlo hhi
  have heq : [0] ++ s = List.ofFn v := by
    rw [List.ofFn_succ, h0]
    rfl
  rw [heq] at hno
  exact hno (listValid_ofFn v hw)

theorem check_of_children (N : ℕ) (rs : ℕ → List (List ℕ))
    (k : ℕ) (p : List ℕ) (next : ℕ)
    (hchildren : ∀ a : ℕ, next ≤ a → a < N →
      check N rs k (p ++ [a]) (a+1) = true) :
    check N rs (k+1) p next = true := by
  simp only [check, Bool.or_eq_true]
  right
  apply List.all_eq_true.mpr
  intro j hj
  exact hchildren (next+j) (by omega) (by have := List.mem_range.mp hj; omega)

def decode (code : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => code % 8 :: decode (code / 8) k

inductive Certificate where
  | stop : ℕ → Certificate
  | branch : List Certificate → Certificate

def verify (N : ℕ) : ℕ → List ℕ → ℕ → Certificate → Bool
  | _, p, _, .stop code => hits N p (decode code p.length)
  | 0, _, _, .branch _ => false
  | k+1, p, next, .branch children =>
      (List.range (N-next)).all fun j ↦
        verify N k (p ++ [next+j]) (next+j+1) (children.getD j (.stop 0))

theorem not_listValid_append_of_verify (N : ℕ)
    (k : ℕ) (p : List ℕ) (next : ℕ) (cert : Certificate)
    (hc : verify N k p next cert = true)
    (s : List ℕ) (hlen : s.length = k) (hmono : s.Pairwise (· < ·))
    (hlo : ∀ x ∈ s, next ≤ x) (hhi : ∀ x ∈ s, x < N) :
    ¬ ListValid N (p ++ s) := by
  induction k generalizing p next cert s with
  | zero =>
    have hs : s = [] := List.length_eq_zero_iff.mp hlen
    subst s
    cases cert with
    | stop code => simpa using not_listValid_of_hits N p (decode code p.length) hc
    | branch children => simp [verify] at hc
  | succ k ih =>
    cases cert with
    | stop code =>
      intro hv
      exact not_listValid_of_hits N p (decode code p.length) hc
        (listValid_of_prefix ⟨s,rfl⟩ hv)
    | branch children =>
      cases s with
      | nil => simp at hlen
      | cons x s =>
        have hxlo := hlo x (by simp)
        have hxhi := hhi x (by simp)
        simp only [verify, List.all_eq_true] at hc
        have hbranch := hc (x-next) (List.mem_range.mpr (by omega))
        rw [show next + (x-next) = x by omega] at hbranch
        have hm := List.pairwise_cons.mp hmono
        have hh := ih (p ++ [x]) (x+1) _ hbranch s (by simpa using hlen) hm.2
          (by intro y hy; have := hm.1 y hy; omega)
          (by intro y hy; exact hhi y (by simp [hy]))
        simpa [List.append_assoc] using hh

theorem not_validTuple_of_verify {n N : ℕ} [NeZero N]
    (cert : Certificate) (hc : verify N n [0] 1 cert = true)
    (g : Fin (n+1) → ZMod N) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨v, hv, h0, hlt, hw, _, _⟩ := exists_sorted_valid_nat_tuple g hg
  let s := List.ofFn (fun i : Fin n ↦ v i.succ)
  have hs : s.length = n := by simp [s]
  have hm : s.Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hv (by simpa using hij)
  have hlo : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hi := hv (Fin.succ_pos i)
    omega
  have hhi : ∀ x ∈ s, x < N := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hlt i.succ
  have hno := not_listValid_append_of_verify N n [0] 1 cert hc s hs hm hlo hhi
  have heq : [0] ++ s = List.ofFn v := by
    rw [List.ofFn_succ, h0]
    rfl
  rw [heq] at hno
  exact hno (listValid_ofFn v hw)

end MinModulus.PrefixCertificate
