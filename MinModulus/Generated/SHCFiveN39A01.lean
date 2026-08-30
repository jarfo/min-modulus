import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2626, 402, 13, 643, 386, 77, 22, 89]

private theorem valid39_01 : ∀ code ∈ codes39_01, validRelationCode code := by
  decide

private theorem cover39_01 : ∀ q : IncreasingFourTail 37 (⟨1, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_01 (increasingFourValues (N := 39) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a01
    (q : IncreasingFourTail 37 (⟨1, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_01 _ valid39_01 (cover39_01 q)

end MinModulus.SHCFiveCertificate.Generated
