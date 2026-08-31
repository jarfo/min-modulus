import MinModulus.Generated.SHCSixNormalizedN69A04B44

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate69_a04_b46_c00 (q : Σ d : Fin (15 - 0 - 2), Fin (15 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨0, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c01 (q : Σ d : Fin (15 - 1 - 2), Fin (15 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨1, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c02 (q : Σ d : Fin (15 - 2 - 2), Fin (15 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨2, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c03 (q : Σ d : Fin (15 - 3 - 2), Fin (15 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨3, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c04 (q : Σ d : Fin (15 - 4 - 2), Fin (15 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨4, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c05 (q : Σ d : Fin (15 - 5 - 2), Fin (15 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨5, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c06 (q : Σ d : Fin (15 - 6 - 2), Fin (15 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨6, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c07 (q : Σ d : Fin (15 - 7 - 2), Fin (15 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨7, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c08 (q : Σ d : Fin (15 - 8 - 2), Fin (15 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨8, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c09 (q : Σ d : Fin (15 - 9 - 2), Fin (15 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨9, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c10 (q : Σ d : Fin (15 - 10 - 2), Fin (15 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨10, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c11 (q : Σ d : Fin (15 - 11 - 2), Fin (15 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨11, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a04_b46_c12 (q : Σ d : Fin (15 - 12 - 2), Fin (15 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 ⟨(⟨12, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate69_a04_b46 (q : IncreasingThree 15) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 6 53 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate69_a04_b46_c00 q
  · exact certificate69_a04_b46_c01 q
  · exact certificate69_a04_b46_c02 q
  · exact certificate69_a04_b46_c03 q
  · exact certificate69_a04_b46_c04 q
  · exact certificate69_a04_b46_c05 q
  · exact certificate69_a04_b46_c06 q
  · exact certificate69_a04_b46_c07 q
  · exact certificate69_a04_b46_c08 q
  · exact certificate69_a04_b46_c09 q
  · exact certificate69_a04_b46_c10 q
  · exact certificate69_a04_b46_c11 q
  · exact certificate69_a04_b46_c12 q

end MinModulus.SHCSixCertificate.Generated
