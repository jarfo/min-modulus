import MinModulus.Generated.SHCSixN105A27B15

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a27_b17_c00 (q : Σ d : Fin (9 - 0 - 2), Fin (9 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c01 (q : Σ d : Fin (9 - 1 - 2), Fin (9 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c02 (q : Σ d : Fin (9 - 2 - 2), Fin (9 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c03 (q : Σ d : Fin (9 - 3 - 2), Fin (9 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c04 (q : Σ d : Fin (9 - 4 - 2), Fin (9 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c05 (q : Σ d : Fin (9 - 5 - 2), Fin (9 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a27_b17_c06 (q : Σ d : Fin (9 - 6 - 2), Fin (9 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨4481, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a27_b17 (q : IncreasingThree 9) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨27, by norm_num⟩ : Fin 55) (⟨45, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a27_b17_c00 q
  · exact certificate105_a27_b17_c01 q
  · exact certificate105_a27_b17_c02 q
  · exact certificate105_a27_b17_c03 q
  · exact certificate105_a27_b17_c04 q
  · exact certificate105_a27_b17_c05 q
  · exact certificate105_a27_b17_c06 q

end MinModulus.SHCSixExceptionalCertificate.Generated
