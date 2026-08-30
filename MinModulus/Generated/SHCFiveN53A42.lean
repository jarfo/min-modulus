import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_42 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid53_42 : ∀ code ∈ codes53_42, validRelationCode code := by
  decide

private theorem cover53_42 : ∀ q : IncreasingFourTail 51 (⟨42, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_42 (increasingFourValues (N := 53) ⟨⟨42, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a42
    (q : IncreasingFourTail 51 (⟨42, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨42, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_42 _ valid53_42 (cover53_42 q)

end MinModulus.SHCFiveCertificate.Generated
