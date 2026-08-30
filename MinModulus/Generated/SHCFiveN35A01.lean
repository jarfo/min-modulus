import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 837, 2633, 2631, 4232, 775, 641, 2306, 4387, 2308]

private theorem valid35_01 : ∀ code ∈ codes35_01, validRelationCode code := by
  decide

private theorem cover35_01 : ∀ q : IncreasingFourTail 33 (⟨1, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_01 (increasingFourValues (N := 35) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a01
    (q : IncreasingFourTail 33 (⟨1, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_01 _ valid35_01 (cover35_01 q)

end MinModulus.SHCFiveCertificate.Generated
