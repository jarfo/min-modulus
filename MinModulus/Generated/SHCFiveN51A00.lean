import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_00 : List ℕ := [1344]

private theorem valid51_00 : ∀ code ∈ codes51_00, validRelationCode code := by
  decide

private theorem cover51_00 : ∀ q : IncreasingFourTail 49 (⟨0, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_00 (increasingFourValues (N := 51) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a00
    (q : IncreasingFourTail 49 (⟨0, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_00 _ valid51_00 (cover51_00 q)

end MinModulus.SHCFiveCertificate.Generated
