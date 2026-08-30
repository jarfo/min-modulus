import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_18 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 4227, 772, 2308, 1865, 2545, 1507, 2468, 773, 642, 402, 2626, 4387, 2631, 705, 2476, 465, 85, 589, 387, 386, 321, 2866, 4066, 209, 713, 2624, 526, 4584, 30, 2305, 153]

private theorem valid45_18 : ∀ code ∈ codes45_18, validRelationCode code := by
  decide

private theorem cover45_18 : ∀ q : IncreasingFourTail 43 (⟨18, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_18 (increasingFourValues (N := 45) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a18
    (q : IncreasingFourTail 43 (⟨18, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_18 _ valid45_18 (cover45_18 q)

end MinModulus.SHCFiveCertificate.Generated
