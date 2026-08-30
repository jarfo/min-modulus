import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_40 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid51_40 : ∀ code ∈ codes51_40, validRelationCode code := by
  decide

private theorem cover51_40 : ∀ q : IncreasingFourTail 49 (⟨40, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_40 (increasingFourValues (N := 51) ⟨⟨40, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a40
    (q : IncreasingFourTail 49 (⟨40, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨40, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_40 _ valid51_40 (cover51_40 q)

end MinModulus.SHCFiveCertificate.Generated
