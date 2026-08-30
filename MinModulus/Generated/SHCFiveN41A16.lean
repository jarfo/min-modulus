import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_16 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 772, 3745, 773, 1865, 153, 642, 4227, 2308, 2626, 4884, 1868, 4885, 402, 526, 85, 589, 2631, 3344, 465, 209, 321, 705, 713, 5184, 770, 4544, 5036, 1828]

private theorem valid41_16 : ∀ code ∈ codes41_16, validRelationCode code := by
  decide

private theorem cover41_16 : ∀ q : IncreasingFourTail 39 (⟨16, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_16 (increasingFourValues (N := 41) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a16
    (q : IncreasingFourTail 39 (⟨16, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_16 _ valid41_16 (cover41_16 q)

end MinModulus.SHCFiveCertificate.Generated
