import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_27 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid45_27 : ∀ code ∈ codes45_27, validRelationCode code := by
  decide

private theorem cover45_27 : ∀ q : IncreasingFourTail 43 (⟨27, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_27 (increasingFourValues (N := 45) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a27
    (q : IncreasingFourTail 43 (⟨27, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_27 _ valid45_27 (cover45_27 q)

end MinModulus.SHCFiveCertificate.Generated
