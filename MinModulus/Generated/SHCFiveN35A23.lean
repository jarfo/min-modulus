import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_23 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid35_23 : ∀ code ∈ codes35_23, validRelationCode code := by
  decide

private theorem cover35_23 : ∀ q : IncreasingFourTail 33 (⟨23, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_23 (increasingFourValues (N := 35) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a23
    (q : IncreasingFourTail 33 (⟨23, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_23 _ valid35_23 (cover35_23 q)

end MinModulus.SHCFiveCertificate.Generated
