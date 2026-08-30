import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_46 : List ℕ := [17, 402]

private theorem valid53_46 : ∀ code ∈ codes53_46, validRelationCode code := by
  decide

private theorem cover53_46 : ∀ q : IncreasingFourTail 51 (⟨46, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_46 (increasingFourValues (N := 53) ⟨⟨46, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a46
    (q : IncreasingFourTail 51 (⟨46, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨46, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_46 _ valid53_46 (cover53_46 q)

end MinModulus.SHCFiveCertificate.Generated
