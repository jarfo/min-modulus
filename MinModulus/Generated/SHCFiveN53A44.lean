import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_44 : List ℕ := [17, 521, 261, 772]

private theorem valid53_44 : ∀ code ∈ codes53_44, validRelationCode code := by
  decide

private theorem cover53_44 : ∀ q : IncreasingFourTail 51 (⟨44, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_44 (increasingFourValues (N := 53) ⟨⟨44, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a44
    (q : IncreasingFourTail 51 (⟨44, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨44, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_44 _ valid53_44 (cover53_44 q)

end MinModulus.SHCFiveCertificate.Generated
