import MinModulus.SixEvenData58
import MinModulus.SixEvenCertificate

open MinModulus MinModulus.SixEvenCertificate MinModulus.SixEvenCertificate.N58
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem MinModulus.SixEvenCertificate.N58.checked_row_5_part_26_30 :
    (List.range (30 - 26)).all (fun x ↦
    let b := 26 + x
    (List.range (58 - 1 - b)).all (fun z ↦
      let c := b + 1 + z
      (List.range (58 - 1 - c)).all (fun t ↦ covered 58 rivals 5 b c (c + 1 + t)))) = true := by decide +kernel
