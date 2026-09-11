import MinModulus.SixEvenData58

open MinModulus MinModulus.SixEvenCertificate MinModulus.SixEvenCertificate.N58
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem MinModulus.SixEvenCertificate.N58.checked_row_3_part_6_7 :
    (List.range (7 - 6)).all (fun x ↦
    let b := 6 + x
    (List.range (58 - 1 - b)).all (fun z ↦
      let c := b + 1 + z
      (List.range (58 - 1 - c)).all (fun t ↦ covered 58 rivals 3 b c (c + 1 + t)))) = true := by decide +kernel
