import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_27 : List ℕ := [17, 521, 770]

private theorem valid35_27 : ∀ code ∈ codes35_27, validRelationCode code := by
  decide

private theorem cover35_27 : ∀ q : IncreasingFourTail 33 (⟨27, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_27 (increasingFourValues (N := 35) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a27
    (q : IncreasingFourTail 33 (⟨27, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_27 _ valid35_27 (cover35_27 q)

end MinModulus.SHCFiveCertificate.Generated
