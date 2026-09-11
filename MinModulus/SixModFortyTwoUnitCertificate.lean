import MinModulus.SixModFortyTwoData

namespace MinModulus.SixFortyTwoCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

theorem all_unit_covered_row_2 : unitRow 2=true := by decide +kernel

theorem all_unit_covered_row_3 : unitRow 3=true := by decide +kernel

theorem all_unit_covered_row_4 : unitRow 4=true := by decide +kernel

theorem all_unit_covered_row_5 : unitRow 5=true := by decide +kernel

theorem all_unit_covered_row_6 : unitRow 6=true := by decide +kernel

theorem all_unit_covered_row_7 : unitRow 7=true := by decide +kernel

theorem all_unit_covered_row_8 : unitRow 8=true := by decide +kernel

theorem all_unit_covered_row_9 : unitRow 9=true := by decide +kernel

theorem all_unit_covered_row_10 : unitRow 10=true := by decide +kernel

theorem all_unit_covered_row_11 : unitRow 11=true := by decide +kernel

theorem all_unit_covered_row_12 : unitRow 12=true := by decide +kernel

theorem all_unit_covered_row_13 : unitRow 13=true := by decide +kernel

theorem all_unit_covered_row_14 : unitRow 14=true := by decide +kernel

theorem all_unit_covered_row_15 : unitRow 15=true := by decide +kernel

theorem all_unit_covered_row_16 : unitRow 16=true := by decide +kernel

theorem all_unit_covered_row_17 : unitRow 17=true := by decide +kernel

theorem all_unit_covered_row_18 : unitRow 18=true := by decide +kernel

theorem all_unit_covered_row_19 : unitRow 19=true := by decide +kernel

theorem all_unit_covered_row_20 : unitRow 20=true := by decide +kernel

theorem all_unit_covered_row_21 : unitRow 21=true := by decide +kernel

theorem all_unit_covered_row_22 : unitRow 22=true := by decide +kernel

theorem all_unit_covered_row_23 : unitRow 23=true := by decide +kernel

theorem all_unit_covered_row_24 : unitRow 24=true := by decide +kernel

theorem all_unit_covered_row_25 : unitRow 25=true := by decide +kernel

theorem all_unit_covered_row_26 : unitRow 26=true := by decide +kernel

theorem all_unit_covered_row_27 : unitRow 27=true := by decide +kernel

theorem all_unit_covered_row_28 : unitRow 28=true := by decide +kernel

theorem all_unit_covered_row_29 : unitRow 29=true := by decide +kernel

theorem all_unit_covered_row_30 : unitRow 30=true := by decide +kernel

theorem all_unit_covered_row_31 : unitRow 31=true := by decide +kernel

theorem all_unit_covered_row_32 : unitRow 32=true := by decide +kernel

theorem all_unit_covered_row_33 : unitRow 33=true := by decide +kernel

theorem all_unit_covered_row_34 : unitRow 34=true := by decide +kernel

theorem all_unit_covered_row_35 : unitRow 35=true := by decide +kernel

theorem all_unit_covered_row_36 : unitRow 36=true := by decide +kernel

theorem all_unit_covered_row_37 : unitRow 37=true := by decide +kernel

theorem all_unit_covered_row_38 : unitRow 38=true := by decide +kernel

theorem all_unit_covered_row_39 : unitRow 39=true := by decide +kernel

theorem all_unit_covered_row_40 : unitRow 40=true := by decide +kernel

theorem all_unit_covered_row_41 : unitRow 41=true := by decide +kernel

theorem all_unit_covered : unitBlock 2 42=true :=
  (combine_rows (unitRow 2) (unitRow 3 && (unitRow 4 && (unitRow 5 && (unitRow 6 && (unitRow 7 && (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))))))))))))) all_unit_covered_row_2 (combine_rows (unitRow 3) (unitRow 4 && (unitRow 5 && (unitRow 6 && (unitRow 7 && (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))))))))))))) all_unit_covered_row_3 (combine_rows (unitRow 4) (unitRow 5 && (unitRow 6 && (unitRow 7 && (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))))))))))) all_unit_covered_row_4 (combine_rows (unitRow 5) (unitRow 6 && (unitRow 7 && (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))))))))))) all_unit_covered_row_5 (combine_rows (unitRow 6) (unitRow 7 && (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))))))))) all_unit_covered_row_6 (combine_rows (unitRow 7) (unitRow 8 && (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))))))))) all_unit_covered_row_7 (combine_rows (unitRow 8) (unitRow 9 && (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))))))) all_unit_covered_row_8 (combine_rows (unitRow 9) (unitRow 10 && (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))))))) all_unit_covered_row_9 (combine_rows (unitRow 10) (unitRow 11 && (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))))) all_unit_covered_row_10 (combine_rows (unitRow 11) (unitRow 12 && (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))))) all_unit_covered_row_11 (combine_rows (unitRow 12) (unitRow 13 && (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))))) all_unit_covered_row_12 (combine_rows (unitRow 13) (unitRow 14 && (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))))) all_unit_covered_row_13 (combine_rows (unitRow 14) (unitRow 15 && (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))))) all_unit_covered_row_14 (combine_rows (unitRow 15) (unitRow 16 && (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))))) all_unit_covered_row_15 (combine_rows (unitRow 16) (unitRow 17 && (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))))) all_unit_covered_row_16 (combine_rows (unitRow 17) (unitRow 18 && (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))))) all_unit_covered_row_17 (combine_rows (unitRow 18) (unitRow 19 && (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))))) all_unit_covered_row_18 (combine_rows (unitRow 19) (unitRow 20 && (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))))) all_unit_covered_row_19 (combine_rows (unitRow 20) (unitRow 21 && (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))))) all_unit_covered_row_20 (combine_rows (unitRow 21) (unitRow 22 && (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))))) all_unit_covered_row_21 (combine_rows (unitRow 22) (unitRow 23 && (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))))) all_unit_covered_row_22 (combine_rows (unitRow 23) (unitRow 24 && (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))))) all_unit_covered_row_23 (combine_rows (unitRow 24) (unitRow 25 && (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))))) all_unit_covered_row_24 (combine_rows (unitRow 25) (unitRow 26 && (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))))) all_unit_covered_row_25 (combine_rows (unitRow 26) (unitRow 27 && (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))))) all_unit_covered_row_26 (combine_rows (unitRow 27) (unitRow 28 && (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))))) all_unit_covered_row_27 (combine_rows (unitRow 28) (unitRow 29 && (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))))) all_unit_covered_row_28 (combine_rows (unitRow 29) (unitRow 30 && (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))))) all_unit_covered_row_29 (combine_rows (unitRow 30) (unitRow 31 && (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))))) all_unit_covered_row_30 (combine_rows (unitRow 31) (unitRow 32 && (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))))) all_unit_covered_row_31 (combine_rows (unitRow 32) (unitRow 33 && (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))))) all_unit_covered_row_32 (combine_rows (unitRow 33) (unitRow 34 && (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))))) all_unit_covered_row_33 (combine_rows (unitRow 34) (unitRow 35 && (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))))) all_unit_covered_row_34 (combine_rows (unitRow 35) (unitRow 36 && (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))))) all_unit_covered_row_35 (combine_rows (unitRow 36) (unitRow 37 && (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))))) all_unit_covered_row_36 (combine_rows (unitRow 37) (unitRow 38 && (unitRow 39 && (unitRow 40 && (unitRow 41 && (true))))) all_unit_covered_row_37 (combine_rows (unitRow 38) (unitRow 39 && (unitRow 40 && (unitRow 41 && (true)))) all_unit_covered_row_38 (combine_rows (unitRow 39) (unitRow 40 && (unitRow 41 && (true))) all_unit_covered_row_39 (combine_rows (unitRow 40) (unitRow 41 && (true)) all_unit_covered_row_40 (combine_rows (unitRow 41) (true) all_unit_covered_row_41 (rfl : true=true)))))))))))))))))))))))))))))))))))))))))


end MinModulus.SixFortyTwoCertificate
