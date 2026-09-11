import MinModulus.CyclicUnitNormalization

namespace MinModulus
open Finset

namespace FourModTenCertificate

/-- Explicit candidate multiplicities; coverage is proved separately. -/
def rivals : List (Fin 4 → ℕ) := [
  ![0,0,0,4],
  ![0,1,3,0],
  ![1,0,3,0],
  ![1,1,0,2],
  ![0,1,0,3],
  ![0,1,1,2],
  ![1,0,0,3],
  ![1,0,1,2],
  ![0,1,2,1],
  ![1,0,2,1],
  ![0,0,2,2],
  ![0,0,4,0],
  ![1,3,0,0],
  ![3,1,0,0],
  ![0,2,0,2],
  ![0,2,2,0],
  ![0,4,0,0],
  ![4,0,0,0]]

/-- Check the total count, a differing coordinate, and the weighted sum. -/
def covered (a b : ℕ) : Bool := rivals.any fun k ↦
  decide ((∑ i, k i)=4 ∧ (∃ i, k i ≠ 1) ∧
    (∑ i, k i*(![0,1,a,b]) i)%10=(∑ i, (![0,1,a,b]) i)%10)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks all 100 normalized pairs, including repetitions. -/
theorem all_covered :
    ((List.range 10).all fun a ↦ (List.range 10).all fun b ↦ covered a b)=true := by
  decide

/-- Each checked candidate is an actual forbidden multiplicity rival. -/
theorem not_validTuple_of_covered (a b : ℕ) (hc : covered a b=true) :
    ¬ ValidTuple (![0,1,(a : ZMod 10),(b : ZMod 10)]) := by
  simp only [covered,List.any_eq_true,decide_eq_true_eq] at hc
  obtain ⟨k,_,hs,hn,hv⟩ := hc
  have hh := not_validTuple_natCast_of_checked_rival (![0,1,a,b]) k hs hn hv
  have heq : (fun i ↦ ((![0,1,a,b]) i : ZMod 10)) = ![0,1,(a : ZMod 10),(b : ZMod 10)] := by
    funext i
    fin_cases i <;> simp
  rwa [heq] at hh

/-- Every normalized four-tuple modulo ten has a multiplicity rival. -/
theorem not_validTuple_normalized (a b : ZMod 10) :
    ¬ ValidTuple (![0,1,a,b]) := by
  have hh := all_covered
  simp only [List.all_eq_true] at hh
  have hc := hh a.val (List.mem_range.mpr a.val_lt)
    b.val (List.mem_range.mpr b.val_lt)
  simpa using not_validTuple_of_covered a.val b.val hc
end FourModTenCertificate

/-- Seeing both parity and reduction modulo five forces a unit difference. -/
theorem unit_difference_mod_ten (x y : ZMod 10)
    (hx : ZMod.castHom (by decide : 2 ∣ 10) (ZMod 2) x ≠ 0)
    (hy : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) y ≠ 0) :
    IsUnit x ∨ IsUnit y ∨ IsUnit (x-y) := by
  have h : ∀ x y : ZMod 10,
      ZMod.castHom (by decide : 2 ∣ 10) (ZMod 2) x ≠ 0 →
      ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y) := by decide
  exact h x y hx hy

/-- Subbinary validity forces a unit coordinate difference modulo ten. -/
theorem exists_unit_difference_of_valid_four_mod_ten
    (g : Fin 4 → ZMod 10) (hg : ValidTuple g) :
    ∃ a b, IsUnit (g b-g a) := by
  obtain ⟨a,ha⟩ := exists_nonzero_cast_difference_of_valid_subbinary
    (by decide : 2 ∣ 10) g hg (by decide) (by decide)
  obtain ⟨b,hb⟩ := exists_nonzero_cast_difference_of_valid_subbinary
    (by decide : 5 ∣ 10) g hg (by decide) (by decide)
  rcases unit_difference_mod_ten (g a-g 0) (g b-g 0) ha hb with h | h | h
  · exact ⟨0,a,h⟩
  · exact ⟨0,b,h⟩
  · exact ⟨b,a,by simpa only [sub_sub_sub_cancel_right] using h⟩

/-- The complete four-coordinate exclusion modulo ten. -/
theorem not_validTuple_four_mod_ten (g : Fin 4 → ZMod 10) :
    ¬ ValidTuple g := by
  intro hg
  letI : Nontrivial (ZMod 10) := ⟨⟨0,1,by decide⟩⟩
  obtain ⟨a,b,hu⟩ := exists_unit_difference_of_valid_four_mod_ten g hg
  obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_of_unit_difference g hg a b hu
  have heq : w = ![0,1,w 2,w 3] := by
    funext i
    fin_cases i <;> simp [h0,h1]
  rw [heq] at hw
  exact FourModTenCertificate.not_validTuple_normalized _ _ hw


end MinModulus
