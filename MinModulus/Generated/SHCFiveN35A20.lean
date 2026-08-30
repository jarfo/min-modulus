import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_20 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid35_20 : ∀ code ∈ codes35_20, validRelationCode code := by
  decide

private theorem cover35_20 : ∀ q : IncreasingFourTail 33 (⟨20, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_20 (increasingFourValues (N := 35) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a20
    (q : IncreasingFourTail 33 (⟨20, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_20 _ valid35_20 (cover35_20 q)

end MinModulus.SHCFiveCertificate.Generated
