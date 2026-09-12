import MinModulus.SixEvenData58
import MinModulus.SixEvenCertificate

open MinModulus MinModulus.SixEvenCertificate MinModulus.SixEvenCertificate.N58
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem MinModulus.SixEvenCertificate.N58.checked_row_8_part_18_20 :
    (List.range (20 - 18)).all (fun x ↦
    let b := 18 + x
    (List.range (58 - 1 - b)).all (fun z ↦
      let c := b + 1 + z
      (List.range (58 - 1 - c)).all (fun t ↦ covered 58 rivals 8 b c (c + 1 + t)))) = true := by decide +kernel
