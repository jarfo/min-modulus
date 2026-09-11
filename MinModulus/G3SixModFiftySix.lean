import MinModulus.CyclicUnitNormalization
import MinModulus.G1Triangle
import MinModulus.SixModFiftySixCertificate
import MinModulus.G3FiveModTwentyFour

namespace MinModulus
/-- The 24 possible strict orders of four distinct natural values. -/
private theorem four_distinct_order (a b c d : ℕ) (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    (a < b ∧ b < c ∧ c < d) ∨
    (a < b ∧ b < d ∧ d < c) ∨
    (a < c ∧ c < b ∧ b < d) ∨
    (a < c ∧ c < d ∧ d < b) ∨
    (a < d ∧ d < b ∧ b < c) ∨
    (a < d ∧ d < c ∧ c < b) ∨
    (b < a ∧ a < c ∧ c < d) ∨
    (b < a ∧ a < d ∧ d < c) ∨
    (b < c ∧ c < a ∧ a < d) ∨
    (b < c ∧ c < d ∧ d < a) ∨
    (b < d ∧ d < a ∧ a < c) ∨
    (b < d ∧ d < c ∧ c < a) ∨
    (c < a ∧ a < b ∧ b < d) ∨
    (c < a ∧ a < d ∧ d < b) ∨
    (c < b ∧ b < a ∧ a < d) ∨
    (c < b ∧ b < d ∧ d < a) ∨
    (c < d ∧ d < a ∧ a < b) ∨
    (c < d ∧ d < b ∧ b < a) ∨
    (d < a ∧ a < b ∧ b < c) ∨
    (d < a ∧ a < c ∧ c < b) ∨
    (d < b ∧ b < a ∧ a < c) ∨
    (d < b ∧ b < c ∧ c < a) ∨
    (d < c ∧ c < a ∧ a < b) ∨
    (d < c ∧ c < b ∧ b < a) := by
  by_cases hba : b < a
  · by_cases hcb : c < b
    · by_cases hdc : d < c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega,by omega,by omega⟩)))))))))))))))))))))))
      · by_cases hdb : d < b
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))))))))
        · by_cases hda : d < a
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))))
    · by_cases hca : c < a
      · by_cases hdb : d < b
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))))))))))))
        · by_cases hdc : d < c
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))
          · by_cases hda : d < a
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))
      · by_cases hdb : d < b
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))))))))))
        · by_cases hda : d < a
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))
          · by_cases hdc : d < c
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))
  · by_cases hca : c < a
    · by_cases hdc : d < c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))))))))))))
      · by_cases hda : d < a
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))))))
        · by_cases hdb : d < b
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))
    · by_cases hcb : c < b
      · by_cases hda : d < a
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))))))))))))))))
        · by_cases hdc : d < c
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))))
          · by_cases hdb : d < b
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)))
            · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))
      · by_cases hda : d < a
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))))))))))))))))
        · by_cases hdb : d < b
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))
          · by_cases hdc : d < c
            · exact Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)
            · exact Or.inl ⟨by omega,by omega,by omega⟩


set_option maxHeartbeats 0 in
/-- Coordinate permutations preserve validity and put a distinct normalized tail in order. -/
theorem not_validTuple_six_normalized_of_sorted
    (hsorted : ∀ a b c d : ℕ, 2 ≤ a → a < b → b < c → c < d → d < 56 →
      ¬ ValidTuple (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]))
    (g : Fin 6 → ZMod 56) (h0 : g 0=0) (h1 : g 1=1) : ¬ ValidTuple g := by
  intro hg
  have hi : Function.Injective (fun i ↦ (g i).val) :=
    (ZMod.val_injective 56).comp (validTuple_injective g hg)
  have h0v : (g 0).val=0 := by simp [h0]
  have h1v : (g 1).val=1 := by rw [h1]; decide
  have hlo2 : 2 ≤ (g 2).val := by
    have hz := hi.ne (by decide : (2 : Fin 6) ≠ 0)
    have ho := hi.ne (by decide : (2 : Fin 6) ≠ 1)
    rw [h0v] at hz
    rw [h1v] at ho
    omega
  have hlo3 : 2 ≤ (g 3).val := by
    have hz := hi.ne (by decide : (3 : Fin 6) ≠ 0)
    have ho := hi.ne (by decide : (3 : Fin 6) ≠ 1)
    rw [h0v] at hz
    rw [h1v] at ho
    omega
  have hlo4 : 2 ≤ (g 4).val := by
    have hz := hi.ne (by decide : (4 : Fin 6) ≠ 0)
    have ho := hi.ne (by decide : (4 : Fin 6) ≠ 1)
    rw [h0v] at hz
    rw [h1v] at ho
    omega
  have hlo5 : 2 ≤ (g 5).val := by
    have hz := hi.ne (by decide : (5 : Fin 6) ≠ 0)
    have ho := hi.ne (by decide : (5 : Fin 6) ≠ 1)
    rw [h0v] at hz
    rw [h1v] at ho
    omega
  have hne23 := hi.ne (by decide : (2 : Fin 6) ≠ 3)
  have hne24 := hi.ne (by decide : (2 : Fin 6) ≠ 4)
  have hne25 := hi.ne (by decide : (2 : Fin 6) ≠ 5)
  have hne34 := hi.ne (by decide : (3 : Fin 6) ≠ 4)
  have hne35 := hi.ne (by decide : (3 : Fin 6) ≠ 5)
  have hne45 := hi.ne (by decide : (4 : Fin 6) ≠ 5)
  have hord := four_distinct_order (g 2).val (g 3).val (g 4).val (g 5).val hne23 hne24 hne25 hne34 hne35 hne45
  rcases hord with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · apply hsorted (g 2).val (g 3).val (g 4).val (g 5).val hlo2 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,3,4,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 3,g 4,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 2).val (g 3).val (g 5).val (g 4).val hlo2 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,3,5,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 3,g 5,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 2).val (g 4).val (g 3).val (g 5).val hlo2 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,4,3,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 4,g 3,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 2).val (g 4).val (g 5).val (g 3).val hlo2 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,4,5,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 4,g 5,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 2).val (g 5).val (g 3).val (g 4).val hlo2 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,5,3,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 5,g 3,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 2).val (g 5).val (g 4).val (g 3).val hlo2 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,2,5,4,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 2,g 5,g 4,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 2).val (g 4).val (g 5).val hlo3 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,2,4,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 2,g 4,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 2).val (g 5).val (g 4).val hlo3 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,2,5,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 2,g 5,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 4).val (g 2).val (g 5).val hlo3 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,4,2,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 4,g 2,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 4).val (g 5).val (g 2).val hlo3 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,4,5,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 4,g 5,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 5).val (g 2).val (g 4).val hlo3 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,5,2,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 5,g 2,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 3).val (g 5).val (g 4).val (g 2).val hlo3 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,3,5,4,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 3,g 5,g 4,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 2).val (g 3).val (g 5).val hlo4 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,2,3,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 2,g 3,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 2).val (g 5).val (g 3).val hlo4 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,2,5,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 2,g 5,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 3).val (g 2).val (g 5).val hlo4 h.1 h.2.1 h.2.2 (g 5).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,3,2,5], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 3,g 2,g 5] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 3).val (g 5).val (g 2).val hlo4 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,3,5,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 3,g 5,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 5).val (g 2).val (g 3).val hlo4 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,5,2,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 5,g 2,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 4).val (g 5).val (g 3).val (g 2).val hlo4 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,4,5,3,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 4,g 5,g 3,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 2).val (g 3).val (g 4).val hlo5 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,2,3,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 2,g 3,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 2).val (g 4).val (g 3).val hlo5 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,2,4,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 2,g 4,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 3).val (g 2).val (g 4).val hlo5 h.1 h.2.1 h.2.2 (g 4).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,3,2,4], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 3,g 2,g 4] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 3).val (g 4).val (g 2).val hlo5 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,3,4,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 3,g 4,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 4).val (g 2).val (g 3).val hlo5 h.1 h.2.1 h.2.2 (g 3).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,4,2,3], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 4,g 2,g 3] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg
  · apply hsorted (g 5).val (g 4).val (g 3).val (g 2).val hlo5 h.1 h.2.1 h.2.2 (g 2).val_lt
    let e : Fin 6 ↪ Fin 6 := ⟨![0,1,5,4,3,2], by decide⟩
    have heq : (fun i ↦ g (e i)) = ![0,1,g 5,g 4,g 3,g 2] := by
      funext i
      fin_cases i <;> simp [e,h0,h1]
    simpa only [heq,ZMod.natCast_zmod_val] using validTuple_embedding e g hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Quotients modulo two and seven force a unit difference for any hypothetical valid six-tuple. -/
theorem not_validTuple_six_mod_fifty_six_of_sorted
    (hsorted : ∀ a b c d : ℕ, 2 ≤ a → a < b → b < c → c < d → d < 56 →
      ¬ ValidTuple (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]))
    (g : Fin 6 → ZMod 56) : ¬ ValidTuple g := by
  intro hg
  letI : Nontrivial (ZMod 56) := ⟨⟨0,1,by decide⟩⟩
  obtain ⟨a,ha⟩ := exists_nonzero_cast_difference_of_valid_subbinary
    (by decide : 2 ∣ 56) g hg (by decide) (by decide)
  obtain ⟨b,hb⟩ := exists_nonzero_cast_difference_of_valid_subbinary
    (by decide : 7 ∣ 56) g hg (by decide) (by decide)
  have hunit : ∀ x y : ZMod 56,
      ZMod.castHom (by decide : 2 ∣ 56) (ZMod 2) x ≠ 0 →
      ZMod.castHom (by decide : 7 ∣ 56) (ZMod 7) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y) := by decide
  have hdiff : ∃ i j, IsUnit (g j-g i) := by
    rcases hunit (g a-g 0) (g b-g 0) ha hb with h | h | h
    · exact ⟨0,a,h⟩
    · exact ⟨0,b,h⟩
    · exact ⟨b,a,by simpa only [sub_sub_sub_cancel_right] using h⟩
  obtain ⟨i,j,hu⟩ := hdiff
  obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_of_unit_difference g hg i j hu
  exact not_validTuple_six_normalized_of_sorted hsorted w h0 h1 hw

/-- The complete six-coordinate exclusion modulo 56, with no escape hypotheses. -/
theorem not_validTuple_six_mod_fifty_six (g : Fin 6 → ZMod 56) : ¬ ValidTuple g :=
  not_validTuple_six_mod_fifty_six_of_sorted
    (SixModFiftySixCertificate.not_validTuple_sorted SixModFiftySixCertificate.all_covered) g

/-- The complete six-coordinate exclusion removes the next quantitative G3 case. -/
theorem exceptionalQuantitativeEscapeObstructionFrom_six_iff_seven :
    ExceptionalQuantitativeEscapeObstructionFrom 6 ↔
      ExceptionalQuantitativeEscapeObstructionFrom 7 := by
  constructor
  · intro h n hn hnpow g hg hquant
    exact h n (by omega) hnpow g hg hquant
  · intro h n hn hnpow g hg hquant
    by_cases hn7 : 7 ≤ n
    · exact h n hn7 hnpow g hg hquant
    · have hn6 : n=6 := by omega
      subst n
      exact not_validTuple_six_mod_fifty_six g hg

end MinModulus
