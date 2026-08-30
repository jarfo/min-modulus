import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 524, 2306, 772, 2308, 20, 4884, 153, 773, 217, 589, 21, 5204, 89, 85, 4552, 154]

private theorem valid35_02 : ∀ code ∈ codes35_02, validRelationCode code := by
  decide

private theorem cover35_02 : ∀ q : IncreasingFourTail 33 (⟨2, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_02 (increasingFourValues (N := 35) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a02
    (q : IncreasingFourTail 33 (⟨2, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_02 _ valid35_02 (cover35_02 q)

end MinModulus.SHCFiveCertificate.Generated
