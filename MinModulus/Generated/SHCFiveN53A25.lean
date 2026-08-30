import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_25 : List ℕ := [1185]

private theorem valid53_25 : ∀ code ∈ codes53_25, validRelationCode code := by
  decide

private theorem cover53_25 : ∀ q : IncreasingFourTail 51 (⟨25, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_25 (increasingFourValues (N := 53) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a25
    (q : IncreasingFourTail 51 (⟨25, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_25 _ valid53_25 (cover53_25 q)

end MinModulus.SHCFiveCertificate.Generated
