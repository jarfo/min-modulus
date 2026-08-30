import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 1187, 4397, 449, 385]

private theorem valid37_01 : ∀ code ∈ codes37_01, validRelationCode code := by
  decide

private theorem cover37_01 : ∀ q : IncreasingFourTail 35 (⟨1, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_01 (increasingFourValues (N := 37) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a01
    (q : IncreasingFourTail 35 (⟨1, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_01 _ valid37_01 (cover37_01 q)

end MinModulus.SHCFiveCertificate.Generated
