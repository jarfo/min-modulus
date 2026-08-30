import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 772, 4227, 2308, 18, 522, 262, 209, 713, 321, 19, 523, 263, 402, 642, 1825, 1665, 2626, 403, 643, 2786, 3765, 85, 4387, 4232, 153, 26, 589, 773, 2468, 2631, 2064, 4584, 2624, 2808, 641]

private theorem valid35_06 : ∀ code ∈ codes35_06, validRelationCode code := by
  decide

private theorem cover35_06 : ∀ q : IncreasingFourTail 33 (⟨6, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_06 (increasingFourValues (N := 35) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a06
    (q : IncreasingFourTail 33 (⟨6, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_06 _ valid35_06 (cover35_06 q)

end MinModulus.SHCFiveCertificate.Generated
