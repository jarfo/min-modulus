import MinModulus.PrefixCertificatePacked

namespace MinModulus.PrefixCertificate

def ClosedPrefix (N k : ℕ) (p : List ℕ) (next : ℕ) : Prop :=
  ∀ s : List ℕ, s.length = k → s.Pairwise (· < ·) →
    (∀ x ∈ s, next ≤ x) → (∀ x ∈ s, x < N) → ¬ ListValid N (p ++ s)

theorem closedPrefix_of_verifyPacked (N k : ℕ) (p : List ℕ) (next : ℕ)
    (cert : Certificate) (hc : verifyPacked N k p next cert = true) :
    ClosedPrefix N k p next := by
  have hlinear : verifyLinear N k p next cert = true := by
    simpa only [verifyLinear_eq_verifyPacked] using hc
  exact not_listValid_append_of_verify N k p next cert
    (verify_of_verifyLinear N k p next cert hlinear)

theorem closedPrefix_of_children (N k : ℕ) (p : List ℕ) (next : ℕ)
    (hchildren : ∀ x : ℕ, next ≤ x → x < N → ClosedPrefix N k (p ++ [x]) (x + 1)) :
    ClosedPrefix N (k + 1) p next := by
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

theorem not_validTuple_of_closedPrefix {n N : ℕ} [NeZero N]
    (hc : ClosedPrefix N n [0] 1)
    (g : Fin (n + 1) → ZMod N) : ¬ ValidTuple g := by
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
  have hno := hc s hs hm hlo hhi
  have heq : [0] ++ s = List.ofFn v := by
    rw [List.ofFn_succ, h0]
    rfl
  rw [heq] at hno
  exact hno (listValid_ofFn v hw)

end MinModulus.PrefixCertificate
