import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 772, 4227, 2308, 19, 523, 263, 3765, 4387, 4232, 773, 2468, 153, 209, 27, 713, 642, 20, 1993, 641, 321, 524, 10, 401, 2466, 2306, 1837, 3024, 525, 1825, 24, 402, 89]

private theorem valid35_05 : ∀ code ∈ codes35_05, validRelationCode code := by
  decide

private theorem cover35_05 : ∀ q : IncreasingFourTail 33 (⟨5, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_05 (increasingFourValues (N := 35) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a05
    (q : IncreasingFourTail 33 (⟨5, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_05 _ valid35_05 (cover35_05 q)

end MinModulus.SHCFiveCertificate.Generated
