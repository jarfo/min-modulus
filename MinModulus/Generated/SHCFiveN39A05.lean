import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 772, 4227, 2308, 1665, 3765, 642, 4387, 4232, 402, 2626, 403, 2786, 589, 2631, 643, 85, 209, 773, 2624, 153, 713, 321, 1905, 4425, 2465, 10, 2305, 4234, 1528, 4265, 1546, 154, 89, 385, 641, 1667, 2478, 401, 13]

private theorem valid39_05 : ∀ code ∈ codes39_05, validRelationCode code := by
  decide

private theorem cover39_05 : ∀ q : IncreasingFourTail 37 (⟨5, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_05 (increasingFourValues (N := 39) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a05
    (q : IncreasingFourTail 37 (⟨5, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_05 _ valid39_05 (cover39_05 q)

end MinModulus.SHCFiveCertificate.Generated
