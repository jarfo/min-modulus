import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2308, 2306, 524, 772, 20, 4884, 153, 773, 774, 5204, 775, 154, 217, 401, 155, 3024, 589, 402, 403, 3344, 526, 525, 465, 527, 89, 13]

private theorem valid39_02 : ∀ code ∈ codes39_02, validRelationCode code := by
  decide

private theorem cover39_02 : ∀ q : IncreasingFourTail 37 (⟨2, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_02 (increasingFourValues (N := 39) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a02
    (q : IncreasingFourTail 37 (⟨2, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_02 _ valid39_02 (cover39_02 q)

end MinModulus.SHCFiveCertificate.Generated
