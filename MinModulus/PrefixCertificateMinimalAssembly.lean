import MinModulus.PrefixCertificateMinimal

namespace MinModulus.PrefixCertificate

theorem not_validTuple_of_minimal_prefixes {n N : ℕ}
    [NeZero N] [Nontrivial (ZMod N)] (hN : 1 < N)
    (hunit : ∀ a : ℕ, 2 ≤ a → a < N →
      ClosedMinimalPrefix true N a n [0, 1, a] (a + 1))
    (hnonunit : ∀ a : ℕ, 1 ≤ a → a < N →
      ClosedMinimalPrefix false N a (n + 1) [0, a] (a + 1))
    (g : Fin (n + 3) → ZMod N) : ¬ ValidTuple g := by
  classical
  intro hg
  by_cases he : ∃ w : Fin (n + 3) → ZMod N, ValidTuple w ∧
      ∃ i j, IsUnit (w j - w i)
  · obtain ⟨w, hw, i, j, hij⟩ := he
    obtain ⟨z, hz, h0, h1⟩ := exists_normalized_valid_of_unit_difference w hw i j hij
    obtain ⟨w, hw, hw0, hlt, hvalid, hpre, _⟩ := exists_sorted_valid_nat_tuple z hz
    have hw1 : w 1 = 1 := by
      apply sorted_second_eq_one hw hw0
      obtain ⟨j, hj⟩ := hpre 1
      exact ⟨j, by simpa only [h0, h1, sub_zero, ZMod.val_one'' (by omega : N ≠ 1)] using hj⟩
    obtain ⟨v, hv, hv1, hmin⟩ := exists_minimal_third ⟨w, ⟨hw, hw0, hlt, hvalid⟩, hw1⟩
    have ha : 2 ≤ v 2 := by
      have := hv.1 (show (1 : Fin (n + 3)) < 2 by
        change 1 % (n + 3) < 2 % (n + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        decide)
      omega
    let s := List.ofFn (fun i : Fin n ↦ v i.succ.succ.succ)
    have hs : s.length = n := by simp [s]
    have hm : s.Pairwise (· < ·) := by
      apply List.pairwise_ofFn.mpr
      intro i j hij
      exact hv.1 (by simpa using hij)
    have hlo : ∀ x ∈ s, v 2 + 1 ≤ x := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      have hi := hv.1 (show (2 : Fin (n + 3)) < i.succ.succ.succ by
        change 2 < i.val + 1 + 1 + 1
        omega)
      omega
    have hhi : ∀ x ∈ s, x < N := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hv.2.2.1 i.succ.succ.succ
    have hno := hunit (v 2) ha (hv.2.2.1 2) s hs hm hlo hhi
    have heq : [0, 1, v 2] ++ s = List.ofFn v := by
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp [s, hv.2.1, hv1]
    rw [heq] at hno
    exact hno ⟨listValid_ofFn v hv.2.2.2, hmin⟩
  · obtain ⟨v, hv, hmin⟩ := exists_minimal_pair g hg
    have hnu : NoUnitPairs N (List.ofFn v) := by
      intro x hx y hy hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact he ⟨(fun k ↦ (v k : ZMod N)), hv.2.2.2, i, j, hu⟩
    have ha : 1 ≤ v 1 := by
      have := hv.1 (show (0 : Fin (n + 3)) < 1 by simp)
      have := hv.2.1
      omega
    let s := List.ofFn (fun i : Fin (n + 1) ↦ v i.succ.succ)
    have hs : s.length = n + 1 := by simp [s]
    have hm : s.Pairwise (· < ·) := by
      apply List.pairwise_ofFn.mpr
      intro i j hij
      exact hv.1 (by simpa using hij)
    have hlo : ∀ x ∈ s, v 1 + 1 ≤ x := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      have hi := hv.1 (show (1 : Fin (n + 3)) < i.succ.succ by
        change 1 < i.val + 1 + 1
        omega)
      omega
    have hhi : ∀ x ∈ s, x < N := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hv.2.2.1 i.succ.succ
    have hno := hnonunit (v 1) ha (hv.2.2.1 1) s hs hm hlo hhi
    have heq : [0, v 1] ++ s = List.ofFn v := by
      rw [List.ofFn_succ, List.ofFn_succ]
      simp [s, hv.2.1]
    rw [heq] at hno
    exact hno ⟨listValid_ofFn v hv.2.2.2, hnu, hmin⟩

end MinModulus.PrefixCertificate
