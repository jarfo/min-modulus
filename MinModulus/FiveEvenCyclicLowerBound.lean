import MinModulus.CyclicUnitNormalization
import MinModulus.FiveSmallEvenCertificate
import MinModulus.G3FiveModTwentyFour

namespace MinModulus

/-- A normalized exclusion and two quotient tests suffice to exclude every
five-tuple at a modulus below 32. -/
theorem not_validTuple_five_of_normalized_exclusion
    {N p : ℕ} [NeZero N] [NeZero p] [Nontrivial (ZMod N)]
    (hd2 : 2 ∣ N) (hdp : p ∣ N) (hN : N < 32) (hp : (1 : ZMod p) ≠ 0)
    (hunit : ∀ x y : ZMod N,
      ZMod.castHom hd2 (ZMod 2) x ≠ 0 →
      ZMod.castHom hdp (ZMod p) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y))
    (hnorm : ∀ a b c : ZMod N, ¬ ValidTuple (![0,1,a,b,c]))
    (g : Fin 5 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨a,ha⟩ := exists_nonzero_cast_difference_of_valid_subbinary hd2 g hg hN (by decide)
  obtain ⟨b,hb⟩ := exists_nonzero_cast_difference_of_valid_subbinary hdp g hg hN hp
  have hdiff : ∃ i j, IsUnit (g j-g i) := by
    rcases hunit (g a-g 0) (g b-g 0) ha hb with h | h | h
    · exact ⟨0,a,h⟩
    · exact ⟨0,b,h⟩
    · exact ⟨b,a,by simpa only [sub_sub_sub_cancel_right] using h⟩
  obtain ⟨i,j,hu⟩ := hdiff
  obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_of_unit_difference g hg i j hu
  have heq : w = ![0,1,w 2,w 3,w 4] := by
    funext k
    fin_cases k <;> simp [h0,h1]
  rw [heq] at hw
  exact hnorm _ _ _ hw

/-- The equality case of the abelian bound excludes length five modulo 16. -/
theorem not_validTuple_five_mod_sixteen (g : Fin 5 → ZMod 16) : ¬ ValidTuple g := by
  intro hg
  have hh := equality_order_two g hg (by norm_num [ZMod.card]) (1 : ZMod 16)
  exact (by decide : (2 : ZMod 16) ≠ 0) (by simpa using hh)

/-- The complete five-coordinate exclusion modulo 18. -/
theorem not_validTuple_five_mod_eighteen (g : Fin 5 → ZMod 18) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 18) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_five_of_normalized_exclusion (N := 18) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (FiveSmallEvenCertificate.not_validTuple_normalized (N := 18)
      FiveSmallEvenCertificate.rivals18 FiveSmallEvenCertificate.all_covered18) g

/-- The complete five-coordinate exclusion modulo 20. -/
theorem not_validTuple_five_mod_twenty (g : Fin 5 → ZMod 20) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 20) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_five_of_normalized_exclusion (N := 20) (p := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (FiveSmallEvenCertificate.not_validTuple_normalized (N := 20)
      FiveSmallEvenCertificate.rivals20 FiveSmallEvenCertificate.all_covered20) g

/-- The complete five-coordinate exclusion modulo 22. -/
theorem not_validTuple_five_mod_twenty_two (g : Fin 5 → ZMod 22) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 22) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_five_of_normalized_exclusion (N := 22) (p := 11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (FiveSmallEvenCertificate.not_validTuple_normalized (N := 22)
      FiveSmallEvenCertificate.rivals22 FiveSmallEvenCertificate.all_covered22) g

/-- The complete five-coordinate exclusion modulo 26. -/
theorem not_validTuple_five_mod_twenty_six (g : Fin 5 → ZMod 26) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 26) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_five_of_normalized_exclusion (N := 26) (p := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (FiveSmallEvenCertificate.not_validTuple_normalized (N := 26)
      FiveSmallEvenCertificate.rivals26 FiveSmallEvenCertificate.all_covered26) g

/-- Every valid five-tuple at a positive even cyclic modulus has modulus at least 28. -/
theorem cyclic_even_lower_bound_five {N : ℕ} (hN : 0 < N) (hEven : Even N)
    (g : Fin 5 → ZMod N) (hg : ValidTuple g) : 28 ≤ N := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hb : 16 ≤ N := by simpa only [ZMod.card,Nat.reducePow] using card_ge g hg
  by_contra hn
  have hcases : N=16 ∨ N=18 ∨ N=20 ∨ N=22 ∨ N=24 ∨ N=26 := by
    rcases hEven with ⟨k,hk⟩
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_validTuple_five_mod_sixteen g hg
  · exact not_validTuple_five_mod_eighteen g hg
  · exact not_validTuple_five_mod_twenty g hg
  · exact not_validTuple_five_mod_twenty_two g hg
  · exact not_validTuple_five_mod_twenty_four g hg
  · exact not_validTuple_five_mod_twenty_six g hg

/-- The conjectured five-coordinate bound in every positive two-adic stratum. -/
theorem even_stratum_lower_bound_five {s q : ℕ} (hq : Odd q)
    (g : Fin 5 → ZMod (2^(s+1)*q)) (hg : ValidTuple g) :
    stratumBound 5 (s+1) ≤ 2^(s+1)*q := by
  have hpos : 0 < 2^(s+1)*q := mul_pos (by positivity) hq.pos
  have heven : Even (2^(s+1)*q) := ⟨2^s*q, by rw [pow_succ']; ring⟩
  have hb := cyclic_even_lower_bound_five hpos heven g hg
  rcases s with _ | s
  · rcases hq with ⟨k,hk⟩
    norm_num [stratumBound,show Nat.log 2 5=2 by decide] at hb ⊢
    omega
  · have hs : min (s+1+1) (Nat.log 2 5)=2 := by norm_num [show Nat.log 2 5=2 by decide]
    simpa only [stratumBound,hs,Nat.reducePow,Nat.reduceSub] using hb

end MinModulus
