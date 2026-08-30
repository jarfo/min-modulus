import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_21 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid35_21 : ∀ code ∈ codes35_21, validRelationCode code := by
  decide

private theorem cover35_21 : ∀ q : IncreasingFourTail 33 (⟨21, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_21 (increasingFourValues (N := 35) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a21
    (q : IncreasingFourTail 33 (⟨21, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_21 _ valid35_21 (cover35_21 q)

end MinModulus.SHCFiveCertificate.Generated
