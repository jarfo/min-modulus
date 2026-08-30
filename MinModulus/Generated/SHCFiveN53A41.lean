import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_41 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid53_41 : ∀ code ∈ codes53_41, validRelationCode code := by
  decide

private theorem cover53_41 : ∀ q : IncreasingFourTail 51 (⟨41, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_41 (increasingFourValues (N := 53) ⟨⟨41, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a41
    (q : IncreasingFourTail 51 (⟨41, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨41, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_41 _ valid53_41 (cover53_41 q)

end MinModulus.SHCFiveCertificate.Generated
