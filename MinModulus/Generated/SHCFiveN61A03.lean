import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000
set_option linter.unusedSimpArgs false

private def codes61_03_00 : List ℕ := [131]

private theorem valid61_03_00 : ∀ code ∈ codes61_03_00, validRelationCode code := by
  decide

private theorem cover61_03_00 : ∀ q : IncreasingTwo 54,
    coveredNat 61 codes61_03_00 (blockValues 5 6 q) = true := by
  decide

private def codes61_03_01 : List ℕ := [17, 642, 85, 577, 18, 641, 20, 521, 402, 589, 337, 522, 401, 524, 261, 21, 525, 2465, 2024, 201, 262, 263, 3785, 3344, 465, 526, 527, 2306, 4544, 705, 22, 23, 2485, 2476, 2308, 2648, 2958, 2788, 2478, 2633, 2808, 3108, 2468, 2488, 3118, 2628, 837, 153, 3907, 4237, 3268, 4067, 3747, 3912, 24, 770, 4087, 4397, 3927, 4227, 3587, 154, 93, 769, 25, 773, 775, 4865, 3757, 772, 774, 217, 89, 31, 4884, 4866, 1527, 1837, 1347, 1667, 1992]

private theorem valid61_03_01 : ∀ code ∈ codes61_03_01, validRelationCode code := by
  decide

private theorem cover61_03_01 : ∀ q : IncreasingTwo 53,
    coveredNat 61 codes61_03_01 (blockValues 5 7 q) = true := by
  decide

private def codes61_03_02 : List ℕ := [17, 521, 261, 403, 402, 337, 522, 643, 642, 577, 18, 19, 641, 20, 21, 523, 401, 524, 525, 2305, 2024, 201, 262, 263, 1586, 4544, 705, 22, 23, 4106, 3344, 465, 526, 527, 2466, 3786, 2306, 2485, 2476, 154, 2308, 770, 155, 771, 2958, 24, 772, 769, 25, 773, 898, 89, 153, 4870, 26, 217, 833, 897, 27, 4397, 28, 29, 775, 5026]

private theorem valid61_03_02 : ∀ code ∈ codes61_03_02, validRelationCode code := by
  decide

private theorem cover61_03_02 : ∀ q : IncreasingTwo 52,
    coveredNat 61 codes61_03_02 (blockValues 5 8 q) = true := by
  decide

private def codes61_03_03 : List ℕ := [1825]

private theorem valid61_03_03 : ∀ code ∈ codes61_03_03, validRelationCode code := by
  decide

private theorem cover61_03_03 : ∀ q : IncreasingTwo 51,
    coveredNat 61 codes61_03_03 (blockValues 5 9 q) = true := by
  decide

private def codes61_03_04 : List ℕ := [1665]

private theorem valid61_03_04 : ∀ code ∈ codes61_03_04, validRelationCode code := by
  decide

private theorem cover61_03_04 : ∀ q : IncreasingTwo 50,
    coveredNat 61 codes61_03_04 (blockValues 5 10 q) = true := by
  decide

private def codes61_03_05 : List ℕ := [17, 521, 261, 3185, 2704, 337, 522, 402, 589, 4385, 3904, 577, 18, 642, 85, 2024, 201, 262, 263, 3024, 401, 524, 525, 4224, 641, 20, 21, 2631, 3344, 465, 526, 527, 4544, 705, 22, 23, 2485, 2466, 2306, 2308, 770, 2476, 1527, 3907, 1993, 24, 772, 26, 775, 3786, 4707, 4087, 2148, 154, 961, 217, 93, 153, 1347, 4232, 2953, 30, 897, 769, 25, 29, 5036, 3756, 4866, 4876, 4871, 3747, 2788, 2478, 2628]

private theorem valid61_03_05 : ∀ code ∈ codes61_03_05, validRelationCode code := by
  decide

private theorem cover61_03_05 : ∀ q : IncreasingTwo 49,
    coveredNat 61 codes61_03_05 (blockValues 5 11 q) = true := by
  decide

private def codes61_03_06 : List ℕ := [17, 521, 261, 3025, 2704, 337, 522, 403, 402, 589, 3785, 3024, 401, 524, 525, 4225, 3904, 577, 18, 643, 642, 85, 3344, 465, 526, 527, 2024, 201, 262, 263, 4224, 641, 20, 21, 2626, 3946, 2631, 2485, 4544, 705, 22, 23, 2466, 3786, 770, 773, 2476, 2306, 1587, 4397, 3587, 2468, 2958, 2953, 24, 28, 898, 154, 26, 217, 897, 153, 29, 775, 4885, 5186, 4232]

private theorem valid61_03_06 : ∀ code ∈ codes61_03_06, validRelationCode code := by
  decide

private theorem cover61_03_06 : ∀ q : IncreasingTwo 48,
    coveredNat 61 codes61_03_06 (blockValues 5 12 q) = true := by
  decide

private def codes61_03_07 : List ℕ := [17, 521, 261, 4230, 3904, 577, 18, 19, 643, 642, 85, 2024, 201, 262, 263, 2704, 337, 522, 523, 403, 402, 589, 4224, 641, 20, 21, 2786, 2626, 2485, 4544, 705, 22, 23, 3024, 401, 524, 525, 1586, 2148, 1993, 2466, 2306, 1527, 772, 770, 465, 3344, 1187, 4227, 2648, 28, 837, 5184, 5504, 2476, 3907, 1347, 3587, 1668, 2308, 24, 449, 25, 773, 775, 5186, 3946, 4866]

private theorem valid61_03_07 : ∀ code ∈ codes61_03_07, validRelationCode code := by
  decide

private theorem cover61_03_07 : ∀ q : IncreasingTwo 47,
    coveredNat 61 codes61_03_07 (blockValues 5 13 q) = true := by
  decide

private def codes61_03_08 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 4234, 643, 642, 85, 403, 402, 589, 4224, 641, 20, 21, 2786, 2485, 2631, 4544, 705, 22, 23, 3024, 401, 524, 525, 2466, 2306, 526, 465, 527, 3344, 3756, 1988, 770, 449, 1586, 1187, 3907, 4227, 2308, 772, 217, 385, 5514, 5045, 3765, 4387, 1827, 1347, 2953, 898, 386, 154, 774, 89, 837, 153, 25, 899, 771, 5204, 4885, 5026, 5036, 3946, 4866, 4876, 4547]

private theorem valid61_03_08 : ∀ code ∈ codes61_03_08, validRelationCode code := by
  decide

private theorem cover61_03_08 : ∀ q : IncreasingTwo 46,
    coveredNat 61 codes61_03_08 (blockValues 5 14 q) = true := by
  decide

private def codes61_03_09 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 4234, 643, 642, 85, 403, 402, 589, 4224, 641, 20, 21, 2485, 2626, 2631, 4544, 705, 22, 23, 524, 401, 525, 3024, 2466, 2306, 1187, 4227, 772, 527, 2308, 449, 3756, 1837, 154, 774, 526, 465, 3586, 4547, 3907, 770, 14, 837, 385, 387, 775, 4885, 2476, 3906, 4397, 1347, 24, 12, 386, 26, 30, 769, 773, 899, 4864, 5191]

private theorem valid61_03_09 : ∀ code ∈ codes61_03_09, validRelationCode code := by
  decide

private theorem cover61_03_09 : ∀ q : IncreasingTwo 45,
    coveredNat 61 codes61_03_09 (blockValues 5 15 q) = true := by
  decide

private def codes61_03_10 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 3185, 4385, 4234, 643, 642, 85, 3785, 403, 402, 589, 3024, 401, 524, 525, 4224, 641, 20, 21, 2485, 3344, 2786, 2626, 2631, 770, 1546, 705, 4544, 2466, 22, 526, 465, 3746, 3756, 24, 772, 774, 14, 449, 385, 153, 387, 155, 775, 4874, 4066, 2476, 3586, 2308, 154, 209, 837, 773, 527, 3765, 4106, 2546, 3946, 4866, 5191]

private theorem valid61_03_10 : ∀ code ∈ codes61_03_10, validRelationCode code := by
  decide

private theorem cover61_03_10 : ∀ q : IncreasingTwo 44,
    coveredNat 61 codes61_03_10 (blockValues 5 16 q) = true := by
  decide

private def codes61_03_11 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 3025, 3185, 3785, 4225, 4385, 403, 402, 589, 4234, 643, 642, 85, 1527, 2485, 3024, 401, 524, 525, 4224, 2786, 20, 641, 21, 527, 3344, 4544, 1546, 2631, 465, 23, 4106, 2626, 1837, 772, 449, 385, 1586, 5026, 3906, 2306, 3586, 4547, 4227, 386, 774, 321, 773, 387, 155, 15, 4865, 2706, 5191]

private theorem valid61_03_11 : ∀ code ∈ codes61_03_11, validRelationCode code := by
  decide

private theorem cover61_03_11 : ∀ q : IncreasingTwo 43,
    coveredNat 61 codes61_03_11 (blockValues 5 17 q) = true := by
  decide

private def codes61_03_12 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 4230, 4225, 4385, 4234, 643, 642, 85, 3025, 3185, 4224, 641, 20, 21, 2485, 403, 402, 4544, 705, 2786, 1546, 3586, 2648, 524, 401, 2466, 3746, 2306, 2631, 449, 3344, 2546, 772, 465, 589, 93, 385, 3264, 3024, 5514, 2866, 1586, 4227, 2308, 386, 774, 961, 771, 775, 5184, 5665, 5045, 5510, 4870, 5191, 2227, 3747]

private theorem valid61_03_12 : ∀ code ∈ codes61_03_12, validRelationCode code := by
  decide

private theorem cover61_03_12 : ∀ q : IncreasingTwo 42,
    coveredNat 61 codes61_03_12 (blockValues 5 18 q) = true := by
  decide

private def codes61_03_13 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 4230, 4225, 4385, 4234, 643, 642, 85, 3785, 3185, 2485, 1546, 4224, 641, 20, 402, 403, 2626, 705, 589, 2786, 2631, 524, 449, 4227, 772, 22, 526, 14, 385, 401, 1187, 2308, 12, 465, 387, 5514, 2945, 2866, 4066, 1586, 3946, 3911, 386, 770, 77, 773, 775, 3765, 3906]

private theorem valid61_03_13 : ∀ code ∈ codes61_03_13, validRelationCode code := by
  decide

private theorem cover61_03_13 : ∀ q : IncreasingTwo 41,
    coveredNat 61 codes61_03_13 (blockValues 5 19 q) = true := by
  decide

private def codes61_03_14 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1546, 1528, 2485, 4230, 4225, 4385, 4234, 643, 642, 85, 3785, 3025, 3185, 3756, 4224, 641, 1187, 1347, 2786, 14, 449, 21, 403, 1907, 772, 20, 12, 402, 525, 15, 2648, 386, 401, 23, 2945, 4885, 4227, 2628, 2958, 24, 524, 28, 770, 705, 321, 93, 769, 155, 775, 5184, 3765, 5510, 3747]

private theorem valid61_03_14 : ∀ code ∈ codes61_03_14, validRelationCode code := by
  decide

private theorem cover61_03_14 : ∀ q : IncreasingTwo 40,
    coveredNat 61 codes61_03_14 (blockValues 5 20 q) = true := by
  decide

private def codes61_03_15 : List ℕ := [17, 521, 261, 1527, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 2485, 1187, 3785, 1347, 15, 14, 449, 3264, 2631, 13, 12, 385, 2944, 4230, 3025, 4225, 386, 402, 77, 387, 3185, 4385, 642, 770, 403, 643, 4224, 772, 465, 705, 401, 21, 3024, 2950, 4870, 2188, 2308, 524, 898, 774, 22, 217, 897, 641, 153, 25, 155, 775, 527, 3344, 5514, 5505]

private theorem valid61_03_15 : ∀ code ∈ codes61_03_15, validRelationCode code := by
  decide

private theorem cover61_03_15 : ∀ q : IncreasingTwo 39,
    coveredNat 61 codes61_03_15 (blockValues 5 21 q) = true := by
  decide

private def codes61_03_16 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1528, 3785, 2485, 15, 14, 449, 3264, 4230, 4225, 4385, 3185, 3025, 4234, 643, 4227, 642, 385, 641, 20, 524, 12, 386, 402, 85, 772, 28, 770, 77, 773, 387, 4237, 2308, 774, 526, 769, 525, 2628, 2648, 154, 26, 705, 589, 401, 25, 899, 775, 527, 31, 5504, 2944, 4224, 5514, 5505, 2945]

private theorem valid61_03_16 : ∀ code ∈ codes61_03_16, validRelationCode code := by
  decide

private theorem cover61_03_16 : ∀ q : IncreasingTwo 38,
    coveredNat 61 codes61_03_16 (blockValues 5 22 q) = true := by
  decide

private def codes61_03_17 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1187, 15, 14, 449, 3264, 13, 12, 385, 2944, 3785, 2626, 77, 386, 387, 2954, 3025, 4225, 3756, 154, 403, 643, 3105, 2546, 4237, 772, 20, 524, 897, 401, 769, 3024, 4224, 4234, 3747, 3767, 4227, 2628, 2308, 24, 898, 22, 526, 465, 641, 153, 25, 3344, 5514, 2945, 4865, 5510, 2476, 3586]

private theorem valid61_03_17 : ∀ code ∈ codes61_03_17, validRelationCode code := by
  decide

private theorem cover61_03_17 : ∀ q : IncreasingTwo 37,
    coveredNat 61 codes61_03_17 (blockValues 5 23 q) = true := by
  decide

private def codes61_03_18 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 15, 14, 449, 3264, 2704, 337, 522, 523, 3904, 577, 18, 19, 13, 12, 385, 2944, 77, 386, 387, 2954, 3785, 3756, 3105, 3025, 4225, 2308, 402, 642, 2628, 772, 20, 524, 154, 403, 643, 2945, 2950, 4230, 4227, 4237, 774, 89, 85, 401, 641, 769, 25, 525, 899, 155, 775, 5504, 5505, 2476, 4871]

private theorem valid61_03_18 : ∀ code ∈ codes61_03_18, validRelationCode code := by
  decide

private theorem cover61_03_18 : ∀ q : IncreasingTwo 36,
    coveredNat 61 codes61_03_18 (blockValues 5 24 q) = true := by
  decide

private def codes61_03_19 : List ℕ := [17, 521, 261, 2024, 201, 262, 14, 449, 3264, 2704, 337, 522, 523, 3904, 577, 18, 19, 2485, 13, 12, 385, 2944, 3756, 77, 386, 387, 2954, 2786, 3105, 3785, 2945, 2546, 3746, 3586, 2788, 772, 642, 4225, 2466, 2067, 2308, 24, 524, 402, 26, 774, 89, 85, 589, 401, 769, 525, 643, 5514, 4234, 4385, 5505, 4866]

private theorem valid61_03_19 : ∀ code ∈ codes61_03_19, validRelationCode code := by
  decide

private theorem cover61_03_19 : ∀ q : IncreasingTwo 35,
    coveredNat 61 codes61_03_19 (blockValues 5 25 q) = true := by
  decide

private def codes61_03_20 : List ℕ := [17, 521, 261, 15, 14, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1347, 13, 12, 385, 2944, 77, 386, 387, 2954, 3105, 3785, 2945, 2950, 2546, 3746, 3025, 4225, 2626, 3586, 772, 402, 642, 4230, 2866, 2466, 2306, 2631, 4227, 20, 524, 321, 85, 589, 897, 401, 641, 403, 643, 775, 4234, 3906]

private theorem valid61_03_20 : ∀ code ∈ codes61_03_20, validRelationCode code := by
  decide

private theorem cover61_03_20 : ∀ q : IncreasingTwo 34,
    coveredNat 61 codes61_03_20 (blockValues 5 26 q) = true := by
  decide

private def codes61_03_21 : List ℕ := [17, 521, 261, 14, 449, 201, 262, 13, 12, 385, 2944, 77, 386, 387, 2704, 337, 522, 523, 3904, 577, 18, 19, 2954, 3586, 3746, 1837, 3105, 2945, 2950, 897, 3785, 2786, 2866, 4066, 2546, 2626, 2706, 772, 642, 321, 837, 773, 5514, 4225, 5191]

private theorem valid61_03_21 : ∀ code ∈ codes61_03_21, validRelationCode code := by
  decide

private theorem cover61_03_21 : ∀ q : IncreasingTwo 33,
    coveredNat 61 codes61_03_21 (blockValues 5 27 q) = true := by
  decide

private def codes61_03_22 : List ℕ := [449, 17, 521, 3264, 2024, 201, 12, 385, 2944, 77, 386, 387, 2704, 337, 522, 523, 3904, 577, 18, 19, 2954, 3105, 2945, 2950, 1827, 899, 3785, 2866, 2706, 1987, 772, 28, 154, 961, 897, 4066, 2626, 2631, 3911, 898, 642, 321, 837, 4225, 5510, 4230, 3906]

private theorem valid61_03_22 : ∀ code ∈ codes61_03_22, validRelationCode code := by
  decide

private theorem cover61_03_22 : ∀ q : IncreasingTwo 32,
    coveredNat 61 codes61_03_22 (blockValues 5 28 q) = true := by
  decide

private def codes61_03_23 : List ℕ := [17, 521, 261, 13, 12, 201, 262, 263, 77, 386, 387, 2954, 2704, 337, 522, 523, 3904, 577, 18, 19, 3105, 2945, 2950, 3911, 3906, 4066, 772, 3785, 2706, 2147, 3767, 4227, 1667, 1992, 774, 217, 321, 899, 5514, 4225, 2786, 2227]

private theorem valid61_03_23 : ∀ code ∈ codes61_03_23, validRelationCode code := by
  decide

private theorem cover61_03_23 : ∀ q : IncreasingTwo 31,
    coveredNat 61 codes61_03_23 (blockValues 5 29 q) = true := by
  decide

private def codes61_03_24 : List ℕ := [12, 385, 17, 521, 2024, 201, 262, 386, 387, 2954, 2485, 3105, 2945, 2950, 2546, 2704, 337, 522, 523, 2866, 3746, 3904, 577, 18, 19, 4066, 774, 3785, 899, 5504]

private theorem valid61_03_24 : ∀ code ∈ codes61_03_24, validRelationCode code := by
  decide

private theorem cover61_03_24 : ∀ q : IncreasingTwo 30,
    coveredNat 61 codes61_03_24 (blockValues 5 30 q) = true := by
  decide

private def codes61_03_25 : List ℕ := [1186]

private theorem valid61_03_25 : ∀ code ∈ codes61_03_25, validRelationCode code := by
  decide

private theorem cover61_03_25 : ∀ q : IncreasingTwo 29,
    coveredNat 61 codes61_03_25 (blockValues 5 31 q) = true := by
  decide

private def codes61_03_26 : List ℕ := [77, 386, 17, 521, 387, 201, 262, 263, 2945, 2950, 2485, 3786, 2704, 337, 522, 523, 3906, 3904, 577, 18, 19, 3785, 899, 898, 774, 217, 93, 772, 897, 153, 775, 5505, 5510]

private theorem valid61_03_26 : ∀ code ∈ codes61_03_26, validRelationCode code := by
  decide

private theorem cover61_03_26 : ∀ q : IncreasingTwo 28,
    coveredNat 61 codes61_03_26 (blockValues 5 32 q) = true := by
  decide

private def codes61_03_27 : List ℕ := [1346]

private theorem valid61_03_27 : ∀ code ∈ codes61_03_27, validRelationCode code := by
  decide

private theorem cover61_03_27 : ∀ q : IncreasingTwo 27,
    coveredNat 61 codes61_03_27 (blockValues 5 33 q) = true := by
  decide

private def codes61_03_28 : List ℕ := [17, 521, 261, 3105, 2024, 201, 262, 263, 3946, 2704, 337, 522, 523, 3904, 577, 18, 19, 3785, 2485, 772, 4227, 2308, 774, 153, 773, 4087, 4387, 4547, 898, 775, 4884, 5045, 1827, 2067, 4237, 2628]

private theorem valid61_03_28 : ∀ code ∈ codes61_03_28, validRelationCode code := by
  decide

private theorem cover61_03_28 : ∀ q : IncreasingTwo 26,
    coveredNat 61 codes61_03_28 (blockValues 5 34 q) = true := by
  decide

private def codes61_03_29 : List ℕ := [17, 521, 261, 2950, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 2485, 3786, 3785, 772, 1837, 774, 773, 775, 4885, 4397, 1667, 898, 154, 217, 321, 897, 29, 899, 5514, 2147, 2227, 4552]

private theorem valid61_03_29 : ∀ code ∈ codes61_03_29, validRelationCode code := by
  decide

private theorem cover61_03_29 : ∀ q : IncreasingTwo 25,
    coveredNat 61 codes61_03_29 (blockValues 5 35 q) = true := by
  decide

private def codes61_03_30 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 3785, 2485, 3786, 1527, 1988, 4227, 772, 774, 93, 5504, 5045, 1987, 1828, 2308, 898, 154, 773, 775, 5824, 4885, 2067, 3927]

private theorem valid61_03_30 : ∀ code ∈ codes61_03_30, validRelationCode code := by
  decide

private theorem cover61_03_30 : ∀ q : IncreasingTwo 24,
    coveredNat 61 codes61_03_30 (blockValues 5 36 q) = true := by
  decide

private def codes61_03_31 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1586, 4106, 3946, 3785, 772, 898, 155, 775, 2485, 1837, 3927, 4227, 1667, 2148, 2308]

private theorem valid61_03_31 : ∀ code ∈ codes61_03_31, validRelationCode code := by
  decide

private theorem cover61_03_31 : ∀ q : IncreasingTwo 23,
    coveredNat 61 codes61_03_31 (blockValues 5 37 q) = true := by
  decide

private def codes61_03_32 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1527, 2485, 772, 154, 773, 3785, 1586, 1546, 3946, 4237, 774, 209, 321, 93, 153, 155, 5514, 1907, 4232]

private theorem valid61_03_32 : ∀ code ∈ codes61_03_32, validRelationCode code := by
  decide

private theorem cover61_03_32 : ∀ q : IncreasingTwo 22,
    coveredNat 61 codes61_03_32 (blockValues 5 38 q) = true := by
  decide

private def codes61_03_33 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 772, 4227, 2308, 155, 775, 3785, 2485, 4707, 2788, 1993, 774, 217, 899, 5514]

private theorem valid61_03_33 : ∀ code ∈ codes61_03_33, validRelationCode code := by
  decide

private theorem cover61_03_33 : ∀ q : IncreasingTwo 21,
    coveredNat 61 codes61_03_33 (blockValues 5 39 q) = true := by
  decide

private def codes61_03_34 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 772, 154, 774, 3785, 2485, 1546, 1827, 209, 321, 773, 155, 5665, 5505, 4885, 2468]

private theorem valid61_03_34 : ∀ code ∈ codes61_03_34, validRelationCode code := by
  decide

private theorem cover61_03_34 : ∀ q : IncreasingTwo 20,
    coveredNat 61 codes61_03_34 (blockValues 5 40 q) = true := by
  decide

private def codes61_03_35 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 772, 3785, 3765, 1837, 1667, 2148, 774, 209, 321, 155, 5045, 1668]

private theorem valid61_03_35 : ∀ code ∈ codes61_03_35, validRelationCode code := by
  decide

private theorem cover61_03_35 : ∀ q : IncreasingTwo 19,
    coveredNat 61 codes61_03_35 (blockValues 5 41 q) = true := by
  decide

private def codes61_03_36 : List ℕ := [17, 521, 261, 1546, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 774, 2485, 1827, 321, 153, 775, 5204]

private theorem valid61_03_36 : ∀ code ∈ codes61_03_36, validRelationCode code := by
  decide

private theorem cover61_03_36 : ∀ q : IncreasingTwo 18,
    coveredNat 61 codes61_03_36 (blockValues 5 42 q) = true := by
  decide

private def codes61_03_37 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 772, 18, 19, 3785, 2485, 3765, 4227, 2308]

private theorem valid61_03_37 : ∀ code ∈ codes61_03_37, validRelationCode code := by
  decide

private theorem cover61_03_37 : ∀ q : IncreasingTwo 17,
    coveredNat 61 codes61_03_37 (blockValues 5 43 q) = true := by
  decide

private def codes61_03_38 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 18, 577, 19, 3765, 772, 154, 774, 209, 321, 773, 775]

private theorem valid61_03_38 : ∀ code ∈ codes61_03_38, validRelationCode code := by
  decide

private theorem cover61_03_38 : ∀ q : IncreasingTwo 16,
    coveredNat 61 codes61_03_38 (blockValues 5 44 q) = true := by
  decide

private def codes61_03_39 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 523, 772, 18, 577, 19, 3904, 4227, 2308]

private theorem valid61_03_39 : ∀ code ∈ codes61_03_39, validRelationCode code := by
  decide

private theorem cover61_03_39 : ∀ q : IncreasingTwo 15,
    coveredNat 61 codes61_03_39 (blockValues 5 45 q) = true := by
  decide

private def codes61_03_40 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 522, 18, 774, 19, 3904, 772, 154, 209, 321, 577]

private theorem valid61_03_40 : ∀ code ∈ codes61_03_40, validRelationCode code := by
  decide

private theorem cover61_03_40 : ∀ q : IncreasingTwo 14,
    coveredNat 61 codes61_03_40 (blockValues 5 46 q) = true := by
  decide

private def codes61_03_41 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 2704, 337, 18, 522, 577, 3904, 2308, 772, 209]

private theorem valid61_03_41 : ∀ code ∈ codes61_03_41, validRelationCode code := by
  decide

private theorem cover61_03_41 : ∀ q : IncreasingTwo 13,
    coveredNat 61 codes61_03_41 (blockValues 5 47 q) = true := by
  decide

private def codes61_03_42 : List ℕ := [17, 521, 261, 2024, 201, 262, 263, 11, 10, 772, 154, 18, 522, 278, 518, 209, 321, 577]

private theorem valid61_03_42 : ∀ code ∈ codes61_03_42, validRelationCode code := by
  decide

private theorem cover61_03_42 : ∀ q : IncreasingTwo 12,
    coveredNat 61 codes61_03_42 (blockValues 5 48 q) = true := by
  decide

private def codes61_03_43 : List ℕ := [17, 521, 261, 2024, 201, 262, 11, 10, 2308, 772, 154, 278, 209, 337, 577]

private theorem valid61_03_43 : ∀ code ∈ codes61_03_43, validRelationCode code := by
  decide

private theorem cover61_03_43 : ∀ q : IncreasingTwo 11,
    coveredNat 61 codes61_03_43 (blockValues 5 49 q) = true := by
  decide

private def codes61_03_44 : List ℕ := [17, 521, 261, 3765, 3904, 577, 18, 518, 154]

private theorem valid61_03_44 : ∀ code ∈ codes61_03_44, validRelationCode code := by
  decide

private theorem cover61_03_44 : ∀ q : IncreasingTwo 10,
    coveredNat 61 codes61_03_44 (blockValues 5 50 q) = true := by
  decide

private def codes61_03_45 : List ℕ := [17, 521, 261, 2148, 3904, 577, 18, 209]

private theorem valid61_03_45 : ∀ code ∈ codes61_03_45, validRelationCode code := by
  decide

private theorem cover61_03_45 : ∀ q : IncreasingTwo 9,
    coveredNat 61 codes61_03_45 (blockValues 5 51 q) = true := by
  decide

private def codes61_03_46 : List ℕ := [17, 521, 261, 1988, 519, 518, 18]

private theorem valid61_03_46 : ∀ code ∈ codes61_03_46, validRelationCode code := by
  decide

private theorem cover61_03_46 : ∀ q : IncreasingTwo 8,
    coveredNat 61 codes61_03_46 (blockValues 5 52 q) = true := by
  decide

private def codes61_03_47 : List ℕ := [17, 521, 261, 11, 10, 201]

private theorem valid61_03_47 : ∀ code ∈ codes61_03_47, validRelationCode code := by
  decide

private theorem cover61_03_47 : ∀ q : IncreasingTwo 7,
    coveredNat 61 codes61_03_47 (blockValues 5 53 q) = true := by
  decide

private def codes61_03_48 : List ℕ := [17, 518, 209, 577, 18]

private theorem valid61_03_48 : ∀ code ∈ codes61_03_48, validRelationCode code := by
  decide

private theorem cover61_03_48 : ∀ q : IncreasingTwo 6,
    coveredNat 61 codes61_03_48 (blockValues 5 54 q) = true := by
  decide

private def codes61_03_49 : List ℕ := [7]

private theorem valid61_03_49 : ∀ code ∈ codes61_03_49, validRelationCode code := by
  decide

private theorem cover61_03_49 : ∀ q : IncreasingTwo 5,
    coveredNat 61 codes61_03_49 (blockValues 5 55 q) = true := by
  decide

private def codes61_03_50 : List ℕ := [6]

private theorem valid61_03_50 : ∀ code ∈ codes61_03_50, validRelationCode code := by
  decide

private theorem cover61_03_50 : ∀ q : IncreasingTwo 4,
    coveredNat 61 codes61_03_50 (blockValues 5 56 q) = true := by
  decide

private def codes61_03_51 : List ℕ := [193]

private theorem valid61_03_51 : ∀ code ∈ codes61_03_51, validRelationCode code := by
  decide

private theorem cover61_03_51 : ∀ q : IncreasingTwo 3,
    coveredNat 61 codes61_03_51 (blockValues 5 57 q) = true := by
  decide

private def codes61_03_52 : List ℕ := [772]

private theorem valid61_03_52 : ∀ code ∈ codes61_03_52, validRelationCode code := by
  decide

private theorem cover61_03_52 : ∀ q : IncreasingTwo 2,
    coveredNat 61 codes61_03_52 (blockValues 5 58 q) = true := by
  decide

theorem certificate61_a03
    (q : IncreasingFourTail 59 (⟨3, by norm_num⟩ : Fin 56)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 61 (increasingFourValues (N := 61) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  rcases q with ⟨b, c, d⟩
  fin_cases b
  · let c' : Fin (54 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (54 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 54 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_00 _ valid61_03_00 (cover61_03_00 q')
  · let c' : Fin (53 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (53 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 53 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_01 _ valid61_03_01 (cover61_03_01 q')
  · let c' : Fin (52 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (52 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 52 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_02 _ valid61_03_02 (cover61_03_02 q')
  · let c' : Fin (51 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (51 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 51 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_03 _ valid61_03_03 (cover61_03_03 q')
  · let c' : Fin (50 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (50 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 50 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_04 _ valid61_03_04 (cover61_03_04 q')
  · let c' : Fin (49 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (49 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 49 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_05 _ valid61_03_05 (cover61_03_05 q')
  · let c' : Fin (48 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (48 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 48 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_06 _ valid61_03_06 (cover61_03_06 q')
  · let c' : Fin (47 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (47 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 47 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_07 _ valid61_03_07 (cover61_03_07 q')
  · let c' : Fin (46 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (46 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 46 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_08 _ valid61_03_08 (cover61_03_08 q')
  · let c' : Fin (45 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (45 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 45 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_09 _ valid61_03_09 (cover61_03_09 q')
  · let c' : Fin (44 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (44 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 44 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_10 _ valid61_03_10 (cover61_03_10 q')
  · let c' : Fin (43 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (43 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 43 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_11 _ valid61_03_11 (cover61_03_11 q')
  · let c' : Fin (42 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (42 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 42 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_12 _ valid61_03_12 (cover61_03_12 q')
  · let c' : Fin (41 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (41 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 41 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_13 _ valid61_03_13 (cover61_03_13 q')
  · let c' : Fin (40 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (40 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 40 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_14 _ valid61_03_14 (cover61_03_14 q')
  · let c' : Fin (39 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (39 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 39 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_15 _ valid61_03_15 (cover61_03_15 q')
  · let c' : Fin (38 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (38 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 38 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_16 _ valid61_03_16 (cover61_03_16 q')
  · let c' : Fin (37 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (37 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 37 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_17 _ valid61_03_17 (cover61_03_17 q')
  · let c' : Fin (36 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (36 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 36 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_18 _ valid61_03_18 (cover61_03_18 q')
  · let c' : Fin (35 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (35 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 35 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_19 _ valid61_03_19 (cover61_03_19 q')
  · let c' : Fin (34 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (34 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 34 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_20 _ valid61_03_20 (cover61_03_20 q')
  · let c' : Fin (33 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (33 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 33 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_21 _ valid61_03_21 (cover61_03_21 q')
  · let c' : Fin (32 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (32 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 32 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_22 _ valid61_03_22 (cover61_03_22 q')
  · let c' : Fin (31 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (31 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 31 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_23 _ valid61_03_23 (cover61_03_23 q')
  · let c' : Fin (30 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (30 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 30 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_24 _ valid61_03_24 (cover61_03_24 q')
  · let c' : Fin (29 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (29 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 29 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_25 _ valid61_03_25 (cover61_03_25 q')
  · let c' : Fin (28 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (28 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 28 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_26 _ valid61_03_26 (cover61_03_26 q')
  · let c' : Fin (27 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (27 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 27 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_27 _ valid61_03_27 (cover61_03_27 q')
  · let c' : Fin (26 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (26 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 26 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_28 _ valid61_03_28 (cover61_03_28 q')
  · let c' : Fin (25 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (25 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 25 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_29 _ valid61_03_29 (cover61_03_29 q')
  · let c' : Fin (24 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (24 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 24 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_30 _ valid61_03_30 (cover61_03_30 q')
  · let c' : Fin (23 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (23 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 23 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_31 _ valid61_03_31 (cover61_03_31 q')
  · let c' : Fin (22 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (22 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 22 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_32 _ valid61_03_32 (cover61_03_32 q')
  · let c' : Fin (21 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (21 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 21 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_33 _ valid61_03_33 (cover61_03_33 q')
  · let c' : Fin (20 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (20 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 20 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_34 _ valid61_03_34 (cover61_03_34 q')
  · let c' : Fin (19 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 19 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_35 _ valid61_03_35 (cover61_03_35 q')
  · let c' : Fin (18 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 18 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_36 _ valid61_03_36 (cover61_03_36 q')
  · let c' : Fin (17 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 17 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_37 _ valid61_03_37 (cover61_03_37 q')
  · let c' : Fin (16 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 16 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_38 _ valid61_03_38 (cover61_03_38 q')
  · let c' : Fin (15 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 15 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_39 _ valid61_03_39 (cover61_03_39 q')
  · let c' : Fin (14 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 14 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_40 _ valid61_03_40 (cover61_03_40 q')
  · let c' : Fin (13 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 13 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_41 _ valid61_03_41 (cover61_03_41 q')
  · let c' : Fin (12 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 12 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_42 _ valid61_03_42 (cover61_03_42 q')
  · let c' : Fin (11 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 11 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_43 _ valid61_03_43 (cover61_03_43 q')
  · let c' : Fin (10 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 10 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_44 _ valid61_03_44 (cover61_03_44 q')
  · let c' : Fin (9 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 9 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_45 _ valid61_03_45 (cover61_03_45 q')
  · let c' : Fin (8 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 8 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_46 _ valid61_03_46 (cover61_03_46 q')
  · let c' : Fin (7 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 7 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_47 _ valid61_03_47 (cover61_03_47 q')
  · let c' : Fin (6 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 6 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_48 _ valid61_03_48 (cover61_03_48 q')
  · let c' : Fin (5 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 5 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_49 _ valid61_03_49 (cover61_03_49 q')
  · let c' : Fin (4 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 4 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_50 _ valid61_03_50 (cover61_03_50 q')
  · let c' : Fin (3 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 3 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_51 _ valid61_03_51 (cover61_03_51 q')
  · let c' : Fin (2 - 1) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (2 - c'.val - 1) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let q' : IncreasingTwo 2 := ⟨c', d'⟩
    simpa [increasingFourValues, blockValues, q', c', d', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      coveredNat_exists_valid 61 codes61_03_52 _ valid61_03_52 (cover61_03_52 q')

end MinModulus.SHCFiveCertificate.Generated
