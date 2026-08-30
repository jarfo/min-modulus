import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_16 : List ℕ := [1185]

private theorem valid35_16 : ∀ code ∈ codes35_16, validRelationCode code := by
  decide

private theorem cover35_16 : ∀ q : IncreasingFourTail 33 (⟨16, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_16 (increasingFourValues (N := 35) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a16
    (q : IncreasingFourTail 33 (⟨16, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_16 _ valid35_16 (cover35_16 q)

end MinModulus.SHCFiveCertificate.Generated
