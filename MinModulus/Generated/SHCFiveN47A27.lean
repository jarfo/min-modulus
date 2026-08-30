import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_27 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 403, 4387, 402, 589, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 386, 1667]

private theorem valid47_27 : ∀ code ∈ codes47_27, validRelationCode code := by
  decide

private theorem cover47_27 : ∀ q : IncreasingFourTail 45 (⟨27, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_27 (increasingFourValues (N := 47) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a27
    (q : IncreasingFourTail 45 (⟨27, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_27 _ valid47_27 (cover47_27 q)

end MinModulus.SHCFiveCertificate.Generated
