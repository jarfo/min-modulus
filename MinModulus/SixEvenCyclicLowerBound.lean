import MinModulus.SixEvenExclusion34
import MinModulus.SixEvenExclusion36
import MinModulus.SixEvenExclusion38
import MinModulus.SixEvenExclusion40
import MinModulus.SixEvenExclusion44
import MinModulus.SixEvenExclusion46
import MinModulus.SixEvenExclusion48
import MinModulus.SixEvenExclusion50
import MinModulus.SixEvenExclusion52
import MinModulus.SixEvenExclusion54
import MinModulus.SixEvenExclusion58
import MinModulus.SixModFortyTwo
import MinModulus.G3SixModFiftySix
import MinModulus.G1FiveCoordinateBase

namespace MinModulus

theorem not_validTuple_six_mod_thirty_two (g : Fin 6 → ZMod 32) : ¬ ValidTuple g := by
  intro hg
  have hh := equality_order_two g hg (by norm_num [ZMod.card]) (1 : ZMod 32)
  exact (by decide : (2 : ZMod 32) ≠ 0) (by simpa using hh)

theorem cyclic_even_lower_bound_six {N : ℕ} (hN : 0<N) (hEven : Even N)
    (g : Fin 6 → ZMod N) (hg : ValidTuple g) : 60≤N := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hb : 32≤N := by simpa only [ZMod.card,Nat.reducePow] using card_ge g hg
  by_contra hn
  have hcases : N=32 ∨ N=34 ∨ N=36 ∨ N=38 ∨ N=40 ∨ N=42 ∨ N=44 ∨ N=46 ∨ N=48 ∨ N=50 ∨ N=52 ∨ N=54 ∨ N=56 ∨ N=58 := by
    rcases hEven with ⟨k,hk⟩
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_validTuple_six_mod_thirty_two g hg
  · exact not_validTuple_six_mod_34 g hg
  · exact not_validTuple_six_mod_36 g hg
  · exact not_validTuple_six_mod_38 g hg
  · exact not_validTuple_six_mod_40 g hg
  · exact not_validTuple_six_mod_forty_two g hg
  · exact not_validTuple_six_mod_44 g hg
  · exact not_validTuple_six_mod_46 g hg
  · exact not_validTuple_six_mod_48 g hg
  · exact not_validTuple_six_mod_50 g hg
  · exact not_validTuple_six_mod_52 g hg
  · exact not_validTuple_six_mod_54 g hg
  · exact not_validTuple_six_mod_fifty_six g hg
  · exact not_validTuple_six_mod_58 g hg

theorem even_stratum_lower_bound_six {s q : ℕ} (hq : Odd q)
    (g : Fin 6 → ZMod (2^(s+1)*q)) (hg : ValidTuple g) :
    stratumBound 6 (s+1) ≤ 2^(s+1)*q := by
  have hpos : 0 < 2^(s+1)*q := mul_pos (by positivity) hq.pos
  have heven : Even (2^(s+1)*q) := ⟨2^s*q, by rw [pow_succ']; ring⟩
  have hb := cyclic_even_lower_bound_six hpos heven g hg
  rcases s with _ | s
  · rcases hq with ⟨k,hk⟩
    norm_num [stratumBound,show Nat.log 2 6=2 by decide] at hb ⊢
    omega
  · have hs : min (s+1+1) (Nat.log 2 6)=2 := by norm_num [show Nat.log 2 6=2 by decide]
    simpa only [stratumBound,hs,Nat.reducePow,Nat.reduceSub] using hb

theorem primitiveThreeOmissionDeleteStepFrom_five_iff_six :
    PrimitiveThreeOmissionDeleteStepFrom 5 ↔ PrimitiveThreeOmissionDeleteStepFrom 6 := by
  constructor
  · intro h n s q hn hq g hg hc hw hp
    exact h (by omega) hq g hg hc hw hp
  · intro h n s q hn hq g hg hc hw hp
    by_cases hn6 : 6≤n
    · exact h hn6 hq g hg hc hw hp
    · have hn5 : n=5 := by omega
      subst n
      have hb := even_stratum_lower_bound_six hq g hg
      exact (Nat.not_lt_of_ge hb hc).elim





end MinModulus
