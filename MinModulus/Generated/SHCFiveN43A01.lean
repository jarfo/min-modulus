import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2626, 402, 643, 2628, 774, 4552, 4237, 837, 465, 2788, 775, 4234, 2786, 12, 403, 3786, 154, 961, 385, 25]

private theorem valid43_01 : ∀ code ∈ codes43_01, validRelationCode code := by
  decide

private theorem cover43_01 : ∀ q : IncreasingFourTail 41 (⟨1, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_01 (increasingFourValues (N := 43) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a01
    (q : IncreasingFourTail 41 (⟨1, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_01 _ valid43_01 (cover43_01 q)

end MinModulus.SHCFiveCertificate.Generated
