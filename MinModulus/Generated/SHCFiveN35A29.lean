import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_29 : List ℕ := [772]

private theorem valid35_29 : ∀ code ∈ codes35_29, validRelationCode code := by
  decide

private theorem cover35_29 : ∀ q : IncreasingFourTail 33 (⟨29, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_29 (increasingFourValues (N := 35) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a29
    (q : IncreasingFourTail 33 (⟨29, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_29 _ valid35_29 (cover35_29 q)

end MinModulus.SHCFiveCertificate.Generated
