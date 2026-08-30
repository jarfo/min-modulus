import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_14 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 153, 773, 589, 403, 279, 4884, 193, 2545, 7, 6, 1984, 1868, 2626, 2308, 85, 642, 10, 4227, 1187, 2305, 4387, 209, 321, 1905, 1827, 643, 4232, 518, 387, 2944, 2465, 89, 385]

private theorem valid41_14 : ∀ code ∈ codes41_14, validRelationCode code := by
  decide

private theorem cover41_14 : ∀ q : IncreasingFourTail 39 (⟨14, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_14 (increasingFourValues (N := 41) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a14
    (q : IncreasingFourTail 39 (⟨14, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_14 _ valid41_14 (cover41_14 q)

end MinModulus.SHCFiveCertificate.Generated
