import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 4227, 3904, 772, 2308, 403, 643, 2786, 1825, 402, 642, 2626, 201, 337, 577, 153, 773, 4387, 4232, 2468, 2631, 589, 85, 4234, 4884, 833, 522, 209, 770, 3746, 385, 5036, 1528, 1868, 2648, 18, 775, 1668, 641]

private theorem valid35_07 : ∀ code ∈ codes35_07, validRelationCode code := by
  decide

private theorem cover35_07 : ∀ q : IncreasingFourTail 33 (⟨7, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_07 (increasingFourValues (N := 35) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a07
    (q : IncreasingFourTail 33 (⟨7, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_07 _ valid35_07 (cover35_07 q)

end MinModulus.SHCFiveCertificate.Generated
