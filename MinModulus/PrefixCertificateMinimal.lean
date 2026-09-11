import MinModulus.PrefixCertificateCanonical

namespace MinModulus.PrefixCertificate

theorem pairMinimal_of_prefix {N a : ℕ} {p q : List ℕ}
    (hp : p <+: q) (hq : PairMinimal N a q) : PairMinimal N a p := by
  obtain ⟨s, rfl⟩ := hp
  intro x hx y hy u v huv hn
  exact hq x (List.mem_append_left s hx) y (List.mem_append_left s hy) u v huv hn

theorem thirdMinimal_of_prefix {N a : ℕ} {p q : List ℕ}
    (hp : p <+: q) (hq : ThirdMinimal N a q) : ThirdMinimal N a p := by
  obtain ⟨s, rfl⟩ := hp
  intro x hx y hy z hz u hu hn
  exact hq x (List.mem_append_left s hx) y (List.mem_append_left s hy)
    z (List.mem_append_left s hz) u hu hn

def pairImproveHit (N a : ℕ) (p : List ℕ) (i j u v : ℕ) : Bool :=
  decide (i < p.length ∧ j < p.length ∧ (u : ZMod N) * (v : ZMod N) = 1 ∧
    ((u : ZMod N) * ((p.getD j 0 : ZMod N) - (p.getD i 0 : ZMod N))).val ≠ 0 ∧
    ((u : ZMod N) * ((p.getD j 0 : ZMod N) - (p.getD i 0 : ZMod N))).val < a)

def thirdImproveHit (N a : ℕ) (p : List ℕ) (i j k u : ℕ) : Bool :=
  decide (i < p.length ∧ j < p.length ∧ k < p.length ∧
    (u : ZMod N) * ((p.getD j 0 : ZMod N) - (p.getD i 0 : ZMod N)) = 1 ∧
    1 < ((u : ZMod N) * ((p.getD k 0 : ZMod N) - (p.getD i 0 : ZMod N))).val ∧
    ((u : ZMod N) * ((p.getD k 0 : ZMod N) - (p.getD i 0 : ZMod N))).val < a)

theorem not_pairMinimal_of_hit (N a : ℕ) (p : List ℕ) (i j u v : ℕ)
    (hh : pairImproveHit N a p i j u v = true) : ¬ PairMinimal N a p := by
  simp only [pairImproveHit, decide_eq_true_eq] at hh
  obtain ⟨hi, hj, huv, hn, hlt⟩ := hh
  have hmi : p.getD i 0 ∈ p := by simpa only [List.getD_eq_getElem, hi] using List.getElem_mem hi
  have hmj : p.getD j 0 ∈ p := by simpa only [List.getD_eq_getElem, hj] using List.getElem_mem hj
  intro hmin
  exact (Nat.not_lt_of_ge (hmin _ hmi _ hmj u v huv hn)) hlt

theorem not_thirdMinimal_of_hit (N a : ℕ) (p : List ℕ) (i j k u : ℕ)
    (hh : thirdImproveHit N a p i j k u = true) : ¬ ThirdMinimal N a p := by
  simp only [thirdImproveHit, decide_eq_true_eq] at hh
  obtain ⟨hi, hj, hk, hu, hn, hlt⟩ := hh
  have hmi : p.getD i 0 ∈ p := by simpa only [List.getD_eq_getElem, hi] using List.getElem_mem hi
  have hmj : p.getD j 0 ∈ p := by simpa only [List.getD_eq_getElem, hj] using List.getElem_mem hj
  have hmk : p.getD k 0 ∈ p := by simpa only [List.getD_eq_getElem, hk] using List.getElem_mem hk
  intro hmin
  exact (Nat.not_lt_of_ge (hmin _ hmi _ hmj _ hmk u hu hn)) hlt

def MinimalConstraint (third : Bool) (N a : ℕ) (p : List ℕ) : Prop :=
  if third then ThirdMinimal N a p else NoUnitPairs N p ∧ PairMinimal N a p

theorem minimalConstraint_of_prefix {third : Bool} {N a : ℕ} {p q : List ℕ}
    (hp : p <+: q) (hq : MinimalConstraint third N a q) : MinimalConstraint third N a p := by
  cases third
  · exact ⟨noUnitPairs_of_prefix hp hq.1, pairMinimal_of_prefix hp hq.2⟩
  · exact thirdMinimal_of_prefix hp hq

inductive MinimalWitness where
  | collision : ℕ → MinimalWitness
  | unitPair : ℕ → ℕ → MinimalWitness
  | pair : ℕ → ℕ → ℕ → ℕ → MinimalWitness
  | third : ℕ → ℕ → ℕ → ℕ → MinimalWitness

def minimalWitnessHit (third : Bool) (N a : ℕ) (p : List ℕ) : MinimalWitness → Bool
  | .collision code => hitsPacked N p code
  | .unitPair i j => if third then false else unitPairHit N p i j
  | .pair i j u v => if third then false else pairImproveHit N a p i j u v
  | .third i j k u => if third then thirdImproveHit N a p i j k u else false

theorem not_valid_minimal_of_hit (third : Bool) (N a : ℕ) (p : List ℕ)
    (w : MinimalWitness) (hc : minimalWitnessHit third N a p w = true) :
    ¬ (ListValid N p ∧ MinimalConstraint third N a p) := by
  intro hg
  cases w with
  | collision code =>
    have hh : hits N p (decode code p.length) = true := by
      simpa only [hits_eq_hitsPacked, minimalWitnessHit] using hc
    exact not_listValid_of_hits N p _ hh hg.1
  | unitPair i j =>
    cases third
    · exact not_noUnitPairs_of_unitPairHit N p i j hc hg.2.1
    · simp [minimalWitnessHit] at hc
  | pair i j u v =>
    cases third
    · exact not_pairMinimal_of_hit N a p i j u v hc hg.2.2
    · simp [minimalWitnessHit] at hc
  | third i j k u =>
    cases third
    · simp [minimalWitnessHit] at hc
    · exact not_thirdMinimal_of_hit N a p i j k u hc hg.2

inductive MinimalCertificate where
  | stop : MinimalWitness → MinimalCertificate
  | branch : List MinimalCertificate → MinimalCertificate

def verifyMinimal (third : Bool) (N a : ℕ) : ℕ → List ℕ → ℕ → MinimalCertificate → Bool
  | _, p, _, .stop w => minimalWitnessHit third N a p w
  | 0, _, _, .branch _ => false
  | k + 1, p, next, .branch children =>
    decide (children.length = N - next) &&
      (children.zipIdx next).all fun (child, x) ↦ verifyMinimal third N a k (p ++ [x]) (x + 1) child

def ClosedMinimalPrefix (third : Bool) (N a k : ℕ) (p : List ℕ) (next : ℕ) : Prop :=
  ∀ s : List ℕ, s.length = k → s.Pairwise (· < ·) →
    (∀ x ∈ s, next ≤ x) → (∀ x ∈ s, x < N) →
    ¬ (ListValid N (p ++ s) ∧ MinimalConstraint third N a (p ++ s))

theorem closedMinimalPrefix_of_verify (third : Bool) (N a k : ℕ) (p : List ℕ) (next : ℕ)
    (cert : MinimalCertificate) (hc : verifyMinimal third N a k p next cert = true) :
    ClosedMinimalPrefix third N a k p next := by
  induction k generalizing p next cert with
  | zero =>
    intro s hlen _ _ _ hgood
    have hs : s = [] := List.length_eq_zero_iff.mp hlen
    subst s
    simp only [List.append_nil] at hgood
    cases cert with
    | stop w => exact not_valid_minimal_of_hit third N a p w hc hgood
    | branch children => simp [verifyMinimal] at hc
  | succ k ih =>
    intro s hlen hmono hlo hhi hgood
    cases cert with
    | stop w =>
      exact not_valid_minimal_of_hit third N a p w hc
        ⟨listValid_of_prefix ⟨s, rfl⟩ hgood.1, minimalConstraint_of_prefix ⟨s, rfl⟩ hgood.2⟩
    | branch children =>
      cases s with
      | nil => simp at hlen
      | cons x s =>
        have hxlo := hlo x (by simp)
        have hxhi := hhi x (by simp)
        have hm := List.pairwise_cons.mp hmono
        simp only [verifyMinimal, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
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

theorem closedMinimalPrefix_of_children (third : Bool) (N a k : ℕ) (p : List ℕ) (next : ℕ)
    (hchildren : ∀ x : ℕ, next ≤ x → x < N →
      ClosedMinimalPrefix third N a k (p ++ [x]) (x + 1)) :
    ClosedMinimalPrefix third N a (k + 1) p next := by
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
