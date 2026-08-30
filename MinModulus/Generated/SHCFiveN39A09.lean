import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_09 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 153, 773, 4884, 4232, 4387, 2468, 4234, 1347, 10, 518, 4265, 278, 519, 2305, 321, 1905, 4425, 209, 713, 2465, 1186, 2624, 523, 4584, 522, 2148, 263, 1348, 18, 19, 387, 11, 3904, 1187, 28, 898, 386]

private theorem valid39_09 : ∀ code ∈ codes39_09, validRelationCode code := by
  decide

private theorem cover39_09 : ∀ q : IncreasingFourTail 37 (⟨9, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_09 (increasingFourValues (N := 39) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a09
    (q : IncreasingFourTail 37 (⟨9, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_09 _ valid39_09 (cover39_09 q)

end MinModulus.SHCFiveCertificate.Generated
