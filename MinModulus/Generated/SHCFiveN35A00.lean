import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_00 : List ℕ := [1344]

private theorem valid35_00 : ∀ code ∈ codes35_00, validRelationCode code := by
  decide

private theorem cover35_00 : ∀ q : IncreasingFourTail 33 (⟨0, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_00 (increasingFourValues (N := 35) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a00
    (q : IncreasingFourTail 33 (⟨0, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_00 _ valid35_00 (cover35_00 q)

end MinModulus.SHCFiveCertificate.Generated
