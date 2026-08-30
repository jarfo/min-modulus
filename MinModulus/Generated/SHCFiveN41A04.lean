import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 3785, 2485, 643, 3765, 403, 2786, 773, 2468, 209, 85, 589, 2631, 153, 4234, 524, 2306, 20, 321, 4237, 4547, 525, 3185, 775, 401, 2305, 217, 837, 2788, 2628, 770, 4265, 774, 4884, 769, 3024, 4224, 1907, 386]

private theorem valid41_04 : ∀ code ∈ codes41_04, validRelationCode code := by
  decide

private theorem cover41_04 : ∀ q : IncreasingFourTail 39 (⟨4, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_04 (increasingFourValues (N := 41) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a04
    (q : IncreasingFourTail 39 (⟨4, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_04 _ valid41_04 (cover41_04 q)

end MinModulus.SHCFiveCertificate.Generated
