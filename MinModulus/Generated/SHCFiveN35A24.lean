import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_24 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid35_24 : ∀ code ∈ codes35_24, validRelationCode code := by
  decide

private theorem cover35_24 : ∀ q : IncreasingFourTail 33 (⟨24, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_24 (increasingFourValues (N := 35) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a24
    (q : IncreasingFourTail 33 (⟨24, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_24 _ valid35_24 (cover35_24 q)

end MinModulus.SHCFiveCertificate.Generated
