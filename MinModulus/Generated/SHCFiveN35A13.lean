import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_13 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 153, 773, 4884, 833, 385, 402, 2468, 4232, 642, 278, 10, 4387, 1865, 518, 321, 898, 27]

private theorem valid35_13 : ∀ code ∈ codes35_13, validRelationCode code := by
  decide

private theorem cover35_13 : ∀ q : IncreasingFourTail 33 (⟨13, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_13 (increasingFourValues (N := 35) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a13
    (q : IncreasingFourTail 33 (⟨13, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_13 _ valid35_13 (cover35_13 q)

end MinModulus.SHCFiveCertificate.Generated
