import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_16 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4265, 278, 279, 589, 403, 153, 773, 4884, 2624, 4227, 209, 2626, 642, 2468, 2308, 643, 2631, 2786, 321, 4232, 85, 4387, 2064, 2305, 518, 4234, 10, 1984, 519, 1527, 193, 1665, 1187, 262, 11, 18, 201, 263, 13, 6, 385, 522, 19, 5504, 4870, 12, 5184, 4876, 833, 523, 2546, 705, 577, 2024, 3904, 4106, 1667, 524, 26, 337, 387, 1827, 3907, 20, 898, 449, 89, 771, 4865]

private theorem valid51_16 : ∀ code ∈ codes51_16, validRelationCode code := by
  decide

private theorem cover51_16 : ∀ q : IncreasingFourTail 49 (⟨16, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_16 (increasingFourValues (N := 51) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a16
    (q : IncreasingFourTail 49 (⟨16, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_16 _ valid51_16 (cover51_16 q)

end MinModulus.SHCFiveCertificate.Generated
