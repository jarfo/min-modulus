import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3785, 2485, 3765, 642, 402, 403, 2786, 2626, 643, 21, 2148, 774, 525, 465, 524, 401, 3586, 3185, 2788, 2628, 3025, 3118, 4234, 3907, 773]

private theorem valid35_03 : ∀ code ∈ codes35_03, validRelationCode code := by
  decide

private theorem cover35_03 : ∀ q : IncreasingFourTail 33 (⟨3, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_03 (increasingFourValues (N := 35) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a03
    (q : IncreasingFourTail 33 (⟨3, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_03 _ valid35_03 (cover35_03 q)

end MinModulus.SHCFiveCertificate.Generated
