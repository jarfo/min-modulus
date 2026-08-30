import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_12 : List ℕ := [17, 521, 261, 131, 1186, 7, 772, 4227, 2308, 402, 642, 2626, 153, 773, 4884, 589, 4584, 4232, 2468, 643, 2786, 2546, 2631, 4387, 85, 1984, 1828, 209, 26, 22, 193]

private theorem valid35_12 : ∀ code ∈ codes35_12, validRelationCode code := by
  decide

private theorem cover35_12 : ∀ q : IncreasingFourTail 33 (⟨12, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_12 (increasingFourValues (N := 35) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a12
    (q : IncreasingFourTail 33 (⟨12, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_12 _ valid35_12 (cover35_12 q)

end MinModulus.SHCFiveCertificate.Generated
