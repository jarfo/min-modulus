import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_15 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 465, 2476, 4227, 772, 526, 3344, 705, 4387, 4232, 2465, 3757, 2468]

private theorem valid37_15 : ∀ code ∈ codes37_15, validRelationCode code := by
  decide

private theorem cover37_15 : ∀ q : IncreasingFourTail 35 (⟨15, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_15 (increasingFourValues (N := 37) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a15
    (q : IncreasingFourTail 35 (⟨15, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_15 _ valid37_15 (cover37_15 q)

end MinModulus.SHCFiveCertificate.Generated
