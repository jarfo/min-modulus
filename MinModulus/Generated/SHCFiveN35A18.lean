import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_18 : List ℕ := [17, 521, 261, 131, 3785, 772, 402, 642, 2626, 4227, 2308, 2485, 4234, 14, 771, 5346]

private theorem valid35_18 : ∀ code ∈ codes35_18, validRelationCode code := by
  decide

private theorem cover35_18 : ∀ q : IncreasingFourTail 33 (⟨18, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_18 (increasingFourValues (N := 35) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a18
    (q : IncreasingFourTail 33 (⟨18, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_18 _ valid35_18 (cover35_18 q)

end MinModulus.SHCFiveCertificate.Generated
