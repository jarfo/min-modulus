import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_35 : List ℕ := [17, 521, 770]

private theorem valid43_35 : ∀ code ∈ codes43_35, validRelationCode code := by
  decide

private theorem cover43_35 : ∀ q : IncreasingFourTail 41 (⟨35, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_35 (increasingFourValues (N := 43) ⟨⟨35, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a35
    (q : IncreasingFourTail 41 (⟨35, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨35, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_35 _ valid43_35 (cover43_35 q)

end MinModulus.SHCFiveCertificate.Generated
