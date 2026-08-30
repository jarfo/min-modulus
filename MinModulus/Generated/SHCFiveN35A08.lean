import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_08 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 642, 2626, 4227, 2308, 4884, 85, 2631, 4387, 643, 2305, 518, 2468, 10, 519, 321, 1905, 4232, 209, 385, 2786, 1186, 3904, 4234, 2624, 3586, 18, 522, 899]

private theorem valid35_08 : ∀ code ∈ codes35_08, validRelationCode code := by
  decide

private theorem cover35_08 : ∀ q : IncreasingFourTail 33 (⟨8, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_08 (increasingFourValues (N := 35) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a08
    (q : IncreasingFourTail 33 (⟨8, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_08 _ valid35_08 (cover35_08 q)

end MinModulus.SHCFiveCertificate.Generated
