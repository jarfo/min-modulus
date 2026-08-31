import MinModulus.Generated.SHCSixN105A35B00

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a35_b02_c00 (q : Σ d : Fin (16 - 0 - 2), Fin (16 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c01 (q : Σ d : Fin (16 - 1 - 2), Fin (16 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c02 (q : Σ d : Fin (16 - 2 - 2), Fin (16 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · fin_cases e
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c03 (q : Σ d : Fin (16 - 3 - 2), Fin (16 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c04 (q : Σ d : Fin (16 - 4 - 2), Fin (16 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c05 (q : Σ d : Fin (16 - 5 - 2), Fin (16 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a35_b02_c06 (q : Σ d : Fin (16 - 6 - 2), Fin (16 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c07 (q : Σ d : Fin (16 - 7 - 2), Fin (16 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c08 (q : Σ d : Fin (16 - 8 - 2), Fin (16 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c09 (q : Σ d : Fin (16 - 9 - 2), Fin (16 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2189, by decide, by decide⟩

private theorem certificate105_a35_b02_c10 (q : Σ d : Fin (16 - 10 - 2), Fin (16 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c11 (q : Σ d : Fin (16 - 11 - 2), Fin (16 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c12 (q : Σ d : Fin (16 - 12 - 2), Fin (16 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b02_c13 (q : Σ d : Fin (16 - 13 - 2), Fin (16 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (16 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a35_b02 (q : IncreasingThree 16) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨38, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a35_b02_c00 q
  · exact certificate105_a35_b02_c01 q
  · exact certificate105_a35_b02_c02 q
  · exact certificate105_a35_b02_c03 q
  · exact certificate105_a35_b02_c04 q
  · exact certificate105_a35_b02_c05 q
  · exact certificate105_a35_b02_c06 q
  · exact certificate105_a35_b02_c07 q
  · exact certificate105_a35_b02_c08 q
  · exact certificate105_a35_b02_c09 q
  · exact certificate105_a35_b02_c10 q
  · exact certificate105_a35_b02_c11 q
  · exact certificate105_a35_b02_c12 q
  · exact certificate105_a35_b02_c13 q

end MinModulus.SHCSixExceptionalCertificate.Generated
