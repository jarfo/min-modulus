import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_00 : List ℕ := [1344]

private theorem valid45_00 : ∀ code ∈ codes45_00, validRelationCode code := by
  decide

private theorem cover45_00 : ∀ q : IncreasingFourTail 43 (⟨0, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_00 (increasingFourValues (N := 45) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a00
    (q : IncreasingFourTail 43 (⟨0, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_00 _ valid45_00 (cover45_00 q)

end MinModulus.SHCFiveCertificate.Generated
