import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_25 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid35_25 : ∀ code ∈ codes35_25, validRelationCode code := by
  decide

private theorem cover35_25 : ∀ q : IncreasingFourTail 33 (⟨25, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_25 (increasingFourValues (N := 35) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a25
    (q : IncreasingFourTail 33 (⟨25, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_25 _ valid35_25 (cover35_25 q)

end MinModulus.SHCFiveCertificate.Generated
