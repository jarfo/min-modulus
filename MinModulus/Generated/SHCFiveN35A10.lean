import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_10 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 4584, 279, 589, 403, 153, 773, 4884, 2546, 4227, 2308, 642, 321, 85, 2626, 4232, 4387, 2631, 643, 518, 2468, 10, 209, 519, 2624, 577, 2786, 193, 28, 6, 337]

private theorem valid35_10 : ∀ code ∈ codes35_10, validRelationCode code := by
  decide

private theorem cover35_10 : ∀ q : IncreasingFourTail 33 (⟨10, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_10 (increasingFourValues (N := 35) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a10
    (q : IncreasingFourTail 33 (⟨10, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_10 _ valid35_10 (cover35_10 q)

end MinModulus.SHCFiveCertificate.Generated
