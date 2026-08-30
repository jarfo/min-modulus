import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_42 : List ℕ := [17, 521, 261, 772]

private theorem valid51_42 : ∀ code ∈ codes51_42, validRelationCode code := by
  decide

private theorem cover51_42 : ∀ q : IncreasingFourTail 49 (⟨42, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_42 (increasingFourValues (N := 51) ⟨⟨42, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a42
    (q : IncreasingFourTail 49 (⟨42, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨42, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_42 _ valid51_42 (cover51_42 q)

end MinModulus.SHCFiveCertificate.Generated
