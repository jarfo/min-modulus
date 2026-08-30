import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 772, 4227, 2308, 1665, 402, 642, 2626, 209, 713, 321, 403, 643, 2786, 85, 589, 2631, 4234, 4265, 2305, 12, 3586, 4067, 4387, 21, 28, 15]

private theorem valid35_04 : ∀ code ∈ codes35_04, validRelationCode code := by
  decide

private theorem cover35_04 : ∀ q : IncreasingFourTail 33 (⟨4, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_04 (increasingFourValues (N := 35) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a04
    (q : IncreasingFourTail 33 (⟨4, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_04 _ valid35_04 (cover35_04 q)

end MinModulus.SHCFiveCertificate.Generated
