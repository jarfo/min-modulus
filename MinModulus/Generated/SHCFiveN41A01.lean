import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 1187, 4397, 2628, 774, 643, 402, 2626, 4552, 22, 13, 4237, 12, 386, 154, 30, 769]

private theorem valid41_01 : ∀ code ∈ codes41_01, validRelationCode code := by
  decide

private theorem cover41_01 : ∀ q : IncreasingFourTail 39 (⟨1, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_01 (increasingFourValues (N := 41) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a01
    (q : IncreasingFourTail 39 (⟨1, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_01 _ valid41_01 (cover41_01 q)

end MinModulus.SHCFiveCertificate.Generated
