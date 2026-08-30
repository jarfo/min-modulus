import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_35 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid45_35 : ∀ code ∈ codes45_35, validRelationCode code := by
  decide

private theorem cover45_35 : ∀ q : IncreasingFourTail 43 (⟨35, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_35 (increasingFourValues (N := 45) ⟨⟨35, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a35
    (q : IncreasingFourTail 43 (⟨35, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨35, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_35 _ valid45_35 (cover45_35 q)

end MinModulus.SHCFiveCertificate.Generated
