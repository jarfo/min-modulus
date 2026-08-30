import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_27 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid39_27 : ∀ code ∈ codes39_27, validRelationCode code := by
  decide

private theorem cover39_27 : ∀ q : IncreasingFourTail 37 (⟨27, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_27 (increasingFourValues (N := 39) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a27
    (q : IncreasingFourTail 37 (⟨27, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_27 _ valid39_27 (cover39_27 q)

end MinModulus.SHCFiveCertificate.Generated
