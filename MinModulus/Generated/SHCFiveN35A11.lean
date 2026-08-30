import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_11 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 278, 402, 713, 4425, 2546, 403, 153, 773, 4884, 279, 589, 1868, 519, 4227, 2308, 11, 4232, 2468, 770, 85, 3907, 6, 193, 2227, 642, 10, 898, 18, 27]

private theorem valid35_11 : ∀ code ∈ codes35_11, validRelationCode code := by
  decide

private theorem cover35_11 : ∀ q : IncreasingFourTail 33 (⟨11, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_11 (increasingFourValues (N := 35) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a11
    (q : IncreasingFourTail 33 (⟨11, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_11 _ valid35_11 (cover35_11 q)

end MinModulus.SHCFiveCertificate.Generated
