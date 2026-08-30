import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_19 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 2308, 3344, 465, 526, 2476, 705, 2468, 4544, 773, 4387, 4232, 402, 833, 3757, 386, 22, 642, 770, 26, 589]

private theorem valid45_19 : ∀ code ∈ codes45_19, validRelationCode code := by
  decide

private theorem cover45_19 : ∀ q : IncreasingFourTail 43 (⟨19, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_19 (increasingFourValues (N := 45) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a19
    (q : IncreasingFourTail 43 (⟨19, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_19 _ valid45_19 (cover45_19 q)

end MinModulus.SHCFiveCertificate.Generated
