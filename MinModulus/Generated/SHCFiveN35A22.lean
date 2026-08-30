import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_22 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid35_22 : ∀ code ∈ codes35_22, validRelationCode code := by
  decide

private theorem cover35_22 : ∀ q : IncreasingFourTail 33 (⟨22, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_22 (increasingFourValues (N := 35) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a22
    (q : IncreasingFourTail 33 (⟨22, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_22 _ valid35_22 (cover35_22 q)

end MinModulus.SHCFiveCertificate.Generated
