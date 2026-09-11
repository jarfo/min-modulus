import MinModulus.PrefixCertificateNoUnits

namespace MinModulus.PrefixCertificate

theorem not_validTuple_normalized_of_closedPrefix {n N : ℕ} [NeZero N]
    (hN : 1 < N) (hc : ClosedPrefix N n [0, 1] 2)
    (g : Fin (n + 2) → ZMod N) (hg0 : g 0 = 0) (hg1 : g 1 = 1) :
    ¬ ValidTuple g := by
  intro hg
  obtain ⟨v, hv, h0, hlt, hw, hpre, _⟩ := exists_sorted_valid_nat_tuple g hg
  obtain ⟨j, hj⟩ := hpre 1
  have hj1 : v j = 1 := by
    simpa [hg0, hg1, ZMod.val_one'' (show N ≠ 1 by omega)] using hj
  have hj0 : j ≠ 0 := by
    intro heq
    rw [heq, h0] at hj1
    omega
  have hjle : (1 : Fin (n + 2)) ≤ j := by
    have : j.val ≠ 0 := by simpa using hj0
    change 1 ≤ j.val
    omega
  have hvle := hv.monotone hjle
  have hv01 := hv (show (0 : Fin (n + 2)) < 1 by simp)
  have h1 : v 1 = 1 := by omega
  let s := List.ofFn (fun i : Fin n ↦ v i.succ.succ)
  have hs : s.length = n := by simp [s]
  have hm : s.Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hv (by simpa using hij)
  have hlo : ∀ x ∈ s, 2 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hi := hv (show (1 : Fin (n + 2)) < i.succ.succ by
      change 1 < i.val + 1 + 1
      omega)
    omega
  have hhi : ∀ x ∈ s, x < N := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hlt i.succ.succ
  have hno := hc s hs hm hlo hhi
  have heq : [0, 1] ++ s = List.ofFn v := by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp [s, h0, h1]
  rw [heq] at hno
  exact hno (listValid_ofFn v hw)

theorem not_validTuple_of_unit_and_noUnit_prefixes {n N : ℕ}
    [NeZero N] [Nontrivial (ZMod N)] (hN : 1 < N)
    (hunit : ClosedPrefix N n [0, 1] 2)
    (hnonunit : ClosedNoUnitPrefix N (n + 1) [0] 1)
    (g : Fin (n + 2) → ZMod N) : ¬ ValidTuple g := by
  classical
  intro hg
  by_cases hu : ∃ i j, IsUnit (g j - g i)
  · obtain ⟨i, j, hij⟩ := hu
    obtain ⟨w, hw, h0, h1⟩ := exists_normalized_valid_of_unit_difference g hg i j hij
    exact not_validTuple_normalized_of_closedPrefix hN hunit w h0 h1 hw
  · push Not at hu
    obtain ⟨v, hv, h0, hlt, hw, _, hback⟩ := exists_sorted_valid_nat_tuple g hg
    have hnu : NoUnitPairs N (List.ofFn v) := by
      intro a ha b hb hunit
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      obtain ⟨ii, hi⟩ := hback i
      obtain ⟨jj, hj⟩ := hback j
      apply hu ii jj
      simpa only [hi, hj, ZMod.natCast_zmod_val, sub_sub_sub_cancel_right] using hunit
    let s := List.ofFn (fun i : Fin (n + 1) ↦ v i.succ)
    have hs : s.length = n + 1 := by simp [s]
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
    have hno := hnonunit s hs hm hlo hhi
    have heq : [0] ++ s = List.ofFn v := by
      rw [List.ofFn_succ, h0]
      rfl
    rw [heq] at hno
    exact hno ⟨listValid_ofFn v hw, hnu⟩

end MinModulus.PrefixCertificate
