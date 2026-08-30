import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_45 : List ℕ := [17, 521, 770]

private theorem valid53_45 : ∀ code ∈ codes53_45, validRelationCode code := by
  decide

private theorem cover53_45 : ∀ q : IncreasingFourTail 51 (⟨45, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_45 (increasingFourValues (N := 53) ⟨⟨45, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a45
    (q : IncreasingFourTail 51 (⟨45, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨45, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_45 _ valid53_45 (cover53_45 q)

end MinModulus.SHCFiveCertificate.Generated
