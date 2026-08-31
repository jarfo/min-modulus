import MinModulus.Generated.SHCSixN105A08B24

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a08_b26_c00 (q : Σ d : Fin (19 - 0 - 2), Fin (19 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨9860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c01 (q : Σ d : Fin (19 - 1 - 2), Fin (19 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c02 (q : Σ d : Fin (19 - 2 - 2), Fin (19 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨8711, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c03 (q : Σ d : Fin (19 - 3 - 2), Fin (19 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c04 (q : Σ d : Fin (19 - 4 - 2), Fin (19 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a08_b26_c05 (q : Σ d : Fin (19 - 5 - 2), Fin (19 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c06 (q : Σ d : Fin (19 - 6 - 2), Fin (19 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c07 (q : Σ d : Fin (19 - 7 - 2), Fin (19 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c08 (q : Σ d : Fin (19 - 8 - 2), Fin (19 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨18832, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c09 (q : Σ d : Fin (19 - 9 - 2), Fin (19 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c10 (q : Σ d : Fin (19 - 10 - 2), Fin (19 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c11 (q : Σ d : Fin (19 - 11 - 2), Fin (19 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c12 (q : Σ d : Fin (19 - 12 - 2), Fin (19 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c13 (q : Σ d : Fin (19 - 13 - 2), Fin (19 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c14 (q : Σ d : Fin (19 - 14 - 2), Fin (19 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  exact ⟨6403, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c15 (q : Σ d : Fin (19 - 15 - 2), Fin (19 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a08_b26_c16 (q : Σ d : Fin (19 - 16 - 2), Fin (19 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (19 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

theorem certificate105_a08_b26 (q : IncreasingThree 19) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨8, by norm_num⟩ : Fin 55) (⟨35, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a08_b26_c00 q
  · exact certificate105_a08_b26_c01 q
  · exact certificate105_a08_b26_c02 q
  · exact certificate105_a08_b26_c03 q
  · exact certificate105_a08_b26_c04 q
  · exact certificate105_a08_b26_c05 q
  · exact certificate105_a08_b26_c06 q
  · exact certificate105_a08_b26_c07 q
  · exact certificate105_a08_b26_c08 q
  · exact certificate105_a08_b26_c09 q
  · exact certificate105_a08_b26_c10 q
  · exact certificate105_a08_b26_c11 q
  · exact certificate105_a08_b26_c12 q
  · exact certificate105_a08_b26_c13 q
  · exact certificate105_a08_b26_c14 q
  · exact certificate105_a08_b26_c15 q
  · exact certificate105_a08_b26_c16 q

end MinModulus.SHCSixExceptionalCertificate.Generated
