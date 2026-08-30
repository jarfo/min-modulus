import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_37 : List ℕ := [17, 521, 770]

private theorem valid45_37 : ∀ code ∈ codes45_37, validRelationCode code := by
  decide

private theorem cover45_37 : ∀ q : IncreasingFourTail 43 (⟨37, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_37 (increasingFourValues (N := 45) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a37
    (q : IncreasingFourTail 43 (⟨37, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_37 _ valid45_37 (cover45_37 q)

end MinModulus.SHCFiveCertificate.Generated
