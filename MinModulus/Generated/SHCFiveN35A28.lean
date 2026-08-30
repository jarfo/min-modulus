import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_28 : List ℕ := [17, 402]

private theorem valid35_28 : ∀ code ∈ codes35_28, validRelationCode code := by
  decide

private theorem cover35_28 : ∀ q : IncreasingFourTail 33 (⟨28, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_28 (increasingFourValues (N := 35) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a28
    (q : IncreasingFourTail 33 (⟨28, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_28 _ valid35_28 (cover35_28 q)

end MinModulus.SHCFiveCertificate.Generated
