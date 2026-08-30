import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 524, 2306, 772, 2308, 20, 85, 217, 4884, 153, 5025, 589, 2633, 465, 89, 4234, 526, 401, 21, 2476, 705, 837, 403, 154, 30]

private theorem valid37_02 : ∀ code ∈ codes37_02, validRelationCode code := by
  decide

private theorem cover37_02 : ∀ q : IncreasingFourTail 35 (⟨2, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_02 (increasingFourValues (N := 37) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a02
    (q : IncreasingFourTail 35 (⟨2, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_02 _ valid37_02 (cover37_02 q)

end MinModulus.SHCFiveCertificate.Generated
