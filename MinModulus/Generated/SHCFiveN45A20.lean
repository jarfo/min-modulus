import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_20 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 22, 2786, 465, 4387, 402, 526, 4227, 4232, 2476, 2626, 2308, 642, 705, 153, 773, 1507, 386, 3264]

private theorem valid45_20 : ∀ code ∈ codes45_20, validRelationCode code := by
  decide

private theorem cover45_20 : ∀ q : IncreasingFourTail 43 (⟨20, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_20 (increasingFourValues (N := 45) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a20
    (q : IncreasingFourTail 43 (⟨20, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_20 _ valid45_20 (cover45_20 q)

end MinModulus.SHCFiveCertificate.Generated
