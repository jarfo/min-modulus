import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 153, 773, 4387, 4232, 321, 85, 589, 2631, 4234, 2546, 385, 2305, 20, 21, 2306, 641, 4224, 2944, 524, 4265, 2866, 401, 387, 3765, 30, 525, 770]

private theorem valid39_04 : ∀ code ∈ codes39_04, validRelationCode code := by
  decide

private theorem cover39_04 : ∀ q : IncreasingFourTail 37 (⟨4, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_04 (increasingFourValues (N := 39) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a04
    (q : IncreasingFourTail 37 (⟨4, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_04 _ valid39_04 (cover39_04 q)

end MinModulus.SHCFiveCertificate.Generated
