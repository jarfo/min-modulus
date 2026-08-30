import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_09 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 402, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 642, 2064, 4227, 2308, 643, 2786, 2626, 2624, 1186, 209, 4232, 10, 85, 4387, 4234, 3746, 2631, 321, 2465, 2468, 18, 201, 217]

private theorem valid35_09 : ∀ code ∈ codes35_09, validRelationCode code := by
  decide

private theorem cover35_09 : ∀ q : IncreasingFourTail 33 (⟨9, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_09 (increasingFourValues (N := 35) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a09
    (q : IncreasingFourTail 33 (⟨9, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_09 _ valid35_09 (cover35_09 q)

end MinModulus.SHCFiveCertificate.Generated
