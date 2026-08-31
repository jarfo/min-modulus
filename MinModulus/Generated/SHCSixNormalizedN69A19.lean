import MinModulus.Generated.SHCSixNormalizedN69A19B00
import MinModulus.Generated.SHCSixNormalizedN69A19B01
import MinModulus.Generated.SHCSixNormalizedN69A19B02
import MinModulus.Generated.SHCSixNormalizedN69A19B03
import MinModulus.Generated.SHCSixNormalizedN69A19B04
import MinModulus.Generated.SHCSixNormalizedN69A19B05
import MinModulus.Generated.SHCSixNormalizedN69A19B06
import MinModulus.Generated.SHCSixNormalizedN69A19B07
import MinModulus.Generated.SHCSixNormalizedN69A19B08
import MinModulus.Generated.SHCSixNormalizedN69A19B09
import MinModulus.Generated.SHCSixNormalizedN69A19B10
import MinModulus.Generated.SHCSixNormalizedN69A19B11
import MinModulus.Generated.SHCSixNormalizedN69A19B12
import MinModulus.Generated.SHCSixNormalizedN69A19B13
import MinModulus.Generated.SHCSixNormalizedN69A19B14
import MinModulus.Generated.SHCSixNormalizedN69A19B15
import MinModulus.Generated.SHCSixNormalizedN69A19B16
import MinModulus.Generated.SHCSixNormalizedN69A19B17
import MinModulus.Generated.SHCSixNormalizedN69A19B18
import MinModulus.Generated.SHCSixNormalizedN69A19B19
import MinModulus.Generated.SHCSixNormalizedN69A19B20
import MinModulus.Generated.SHCSixNormalizedN69A19B21
import MinModulus.Generated.SHCSixNormalizedN69A19B22
import MinModulus.Generated.SHCSixNormalizedN69A19B23
import MinModulus.Generated.SHCSixNormalizedN69A19B24
import MinModulus.Generated.SHCSixNormalizedN69A19B25
import MinModulus.Generated.SHCSixNormalizedN69A19B26
import MinModulus.Generated.SHCSixNormalizedN69A19B27
import MinModulus.Generated.SHCSixNormalizedN69A19B28
import MinModulus.Generated.SHCSixNormalizedN69A19B29
import MinModulus.Generated.SHCSixNormalizedN69A19B30
import MinModulus.Generated.SHCSixNormalizedN69A19B31
import MinModulus.Generated.SHCSixNormalizedN69A19B32
import MinModulus.Generated.SHCSixNormalizedN69A19B33
import MinModulus.Generated.SHCSixNormalizedN69A19B34
import MinModulus.Generated.SHCSixNormalizedN69A19B35
import MinModulus.Generated.SHCSixNormalizedN69A19B36
import MinModulus.Generated.SHCSixNormalizedN69A19B37
import MinModulus.Generated.SHCSixNormalizedN69A19B38
import MinModulus.Generated.SHCSixNormalizedN69A19B39
import MinModulus.Generated.SHCSixNormalizedN69A19B40
import MinModulus.Generated.SHCSixNormalizedN69A19B41
import MinModulus.Generated.SHCSixNormalizedN69A19B42
import MinModulus.Generated.SHCSixNormalizedN69A19B43

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem certificate69_a19
    (q : IncreasingFiveTail 67 (⟨19, by norm_num⟩ : Fin 63)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 69 (increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), q⟩) code = true := by
  rcases q with ⟨b, c, d, e⟩
  fin_cases b
  · let c' : Fin (46 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (46 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (46 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 46 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨0, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 22 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b00 q'
  · let c' : Fin (45 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (45 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (45 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 45 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨1, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 23 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b01 q'
  · let c' : Fin (44 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (44 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (44 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 44 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨2, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 24 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b02 q'
  · let c' : Fin (43 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (43 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (43 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 43 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨3, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 25 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b03 q'
  · let c' : Fin (42 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (42 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (42 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 42 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨4, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 26 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b04 q'
  · let c' : Fin (41 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (41 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (41 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 41 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨5, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 27 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b05 q'
  · let c' : Fin (40 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (40 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (40 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 40 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨6, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 28 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b06 q'
  · let c' : Fin (39 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (39 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (39 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 39 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨7, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 29 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b07 q'
  · let c' : Fin (38 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (38 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (38 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 38 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨8, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 30 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b08 q'
  · let c' : Fin (37 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (37 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (37 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 37 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨9, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 31 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b09 q'
  · let c' : Fin (36 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (36 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (36 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 36 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨10, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 32 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b10 q'
  · let c' : Fin (35 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (35 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (35 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 35 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨11, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 33 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b11 q'
  · let c' : Fin (34 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (34 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (34 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 34 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨12, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 34 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b12 q'
  · let c' : Fin (33 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (33 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (33 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 33 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨13, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 35 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b13 q'
  · let c' : Fin (32 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (32 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (32 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 32 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨14, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 36 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b14 q'
  · let c' : Fin (31 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (31 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (31 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 31 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨15, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 37 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b15 q'
  · let c' : Fin (30 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (30 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (30 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 30 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨16, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 38 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b16 q'
  · let c' : Fin (29 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (29 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (29 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 29 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨17, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 39 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b17 q'
  · let c' : Fin (28 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (28 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (28 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 28 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨18, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 40 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b18 q'
  · let c' : Fin (27 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (27 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (27 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 27 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨19, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 41 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b19 q'
  · let c' : Fin (26 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (26 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (26 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 26 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨20, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 42 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b20 q'
  · let c' : Fin (25 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (25 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (25 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 25 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨21, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 43 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b21 q'
  · let c' : Fin (24 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (24 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (24 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 24 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨22, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 44 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b22 q'
  · let c' : Fin (23 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (23 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (23 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 23 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨23, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 45 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b23 q'
  · let c' : Fin (22 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (22 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (22 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 22 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨24, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 46 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b24 q'
  · let c' : Fin (21 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (21 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (21 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 21 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨25, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 47 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b25 q'
  · let c' : Fin (20 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (20 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (20 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 20 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨26, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 48 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b26 q'
  · let c' : Fin (19 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (19 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (19 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 19 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨27, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 49 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b27 q'
  · let c' : Fin (18 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (18 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (18 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 18 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨28, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 50 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b28 q'
  · let c' : Fin (17 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (17 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (17 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 17 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨29, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 51 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b29 q'
  · let c' : Fin (16 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (16 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (16 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 16 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨30, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 52 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b30 q'
  · let c' : Fin (15 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (15 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (15 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 15 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨31, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 53 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b31 q'
  · let c' : Fin (14 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (14 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (14 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 14 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨32, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 54 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b32 q'
  · let c' : Fin (13 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (13 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (13 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 13 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨33, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 55 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b33 q'
  · let c' : Fin (12 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (12 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (12 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 12 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨34, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 56 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b34 q'
  · let c' : Fin (11 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (11 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (11 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 11 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨35, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 57 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b35 q'
  · let c' : Fin (10 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (10 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (10 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 10 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨36, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 58 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b36 q'
  · let c' : Fin (9 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (9 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (9 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 9 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨37, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 59 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b37 q'
  · let c' : Fin (8 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (8 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (8 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 8 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨38, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 60 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b38 q'
  · let c' : Fin (7 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (7 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (7 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 7 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨39, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 61 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b39 q'
  · let c' : Fin (6 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (6 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (6 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 6 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨40, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 62 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b40 q'
  · let c' : Fin (5 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (5 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (5 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 5 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨41, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 63 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b41 q'
  · let c' : Fin (4 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (4 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (4 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 4 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨42, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 64 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b42 q'
  · let c' : Fin (3 - 2) := ⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩
    let d' : Fin (3 - c'.val - 2) := ⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩
    let e' : Fin (3 - (c'.val + 1 + d'.val) - 1) := ⟨e.val, by have he := e.isLt; dsimp only at he; dsimp [c', d']; omega⟩
    let q' : IncreasingThree 3 := ⟨c', d', e'⟩
    have hv : increasingFiveValues (N := 69) ⟨(⟨19, by norm_num⟩ : Fin 63), ⟨⟨43, by norm_num⟩, c, d, e⟩⟩ =
        blockValues 21 65 q' := by
      funext i
      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] <;> omega
    rw [hv]
    exact certificate69_a19_b43 q'

end MinModulus.SHCSixCertificate.Generated
