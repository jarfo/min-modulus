import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 4227, 577, 772, 2308, 18, 522, 262, 153, 773, 4387, 4232, 2468, 402, 642, 2626, 1825, 1665, 2786, 643, 403, 523, 263, 19, 2631, 589, 85, 4234, 4884, 833, 209, 385, 321, 3746, 3906, 524, 770, 2624, 20, 713, 27, 10, 30, 21, 4865, 12, 154]

private theorem valid39_07 : ∀ code ∈ codes39_07, validRelationCode code := by
  decide

private theorem cover39_07 : ∀ q : IncreasingFourTail 37 (⟨7, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_07 (increasingFourValues (N := 39) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a07
    (q : IncreasingFourTail 37 (⟨7, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_07 _ valid39_07 (cover39_07 q)

end MinModulus.SHCFiveCertificate.Generated
