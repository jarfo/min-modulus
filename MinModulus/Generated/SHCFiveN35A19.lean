import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_19 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid35_19 : ∀ code ∈ codes35_19, validRelationCode code := by
  decide

private theorem cover35_19 : ∀ q : IncreasingFourTail 33 (⟨19, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_19 (increasingFourValues (N := 35) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a19
    (q : IncreasingFourTail 33 (⟨19, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_19 _ valid35_19 (cover35_19 q)

end MinModulus.SHCFiveCertificate.Generated
