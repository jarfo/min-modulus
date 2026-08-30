import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 4227, 642, 772, 402, 2626, 2308, 3904, 201, 337, 577, 1825, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 4884, 5184, 522, 2064, 262, 1665, 209, 321, 3765, 3746, 518, 1905, 18, 713, 4265, 4425, 2465, 10, 278, 2305, 386, 11, 20, 12]

private theorem valid39_08 : ∀ code ∈ codes39_08, validRelationCode code := by
  decide

private theorem cover39_08 : ∀ q : IncreasingFourTail 37 (⟨8, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_08 (increasingFourValues (N := 39) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a08
    (q : IncreasingFourTail 37 (⟨8, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_08 _ valid39_08 (cover39_08 q)

end MinModulus.SHCFiveCertificate.Generated
