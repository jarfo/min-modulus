import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_00 : List ℕ := [1344]

private theorem valid53_00 : ∀ code ∈ codes53_00, validRelationCode code := by
  decide

private theorem cover53_00 : ∀ q : IncreasingFourTail 51 (⟨0, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_00 (increasingFourValues (N := 53) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a00
    (q : IncreasingFourTail 51 (⟨0, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_00 _ valid53_00 (cover53_00 q)

end MinModulus.SHCFiveCertificate.Generated
