import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_26 : List ℕ := [17, 521, 261, 772]

private theorem valid35_26 : ∀ code ∈ codes35_26, validRelationCode code := by
  decide

private theorem cover35_26 : ∀ q : IncreasingFourTail 33 (⟨26, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_26 (increasingFourValues (N := 35) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a26
    (q : IncreasingFourTail 33 (⟨26, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_26 _ valid35_26 (cover35_26 q)

end MinModulus.SHCFiveCertificate.Generated
