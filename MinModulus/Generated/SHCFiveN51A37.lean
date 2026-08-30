import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_37 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid51_37 : ∀ code ∈ codes51_37, validRelationCode code := by
  decide

private theorem cover51_37 : ∀ q : IncreasingFourTail 49 (⟨37, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_37 (increasingFourValues (N := 51) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a37
    (q : IncreasingFourTail 49 (⟨37, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_37 _ valid51_37 (cover51_37 q)

end MinModulus.SHCFiveCertificate.Generated
