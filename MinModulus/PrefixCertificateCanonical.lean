import MinModulus.PrefixCertificateAssembly

namespace MinModulus.PrefixCertificate

def PairMinimal (N a : ℕ) (p : List ℕ) : Prop :=
  ∀ x ∈ p, ∀ y ∈ p, ∀ u v : ZMod N, u * v = 1 →
    (u * ((y : ZMod N) - (x : ZMod N))).val ≠ 0 →
    a ≤ (u * ((y : ZMod N) - (x : ZMod N))).val

def ThirdMinimal (N a : ℕ) (p : List ℕ) : Prop :=
  ∀ x ∈ p, ∀ y ∈ p, ∀ z ∈ p, ∀ u : ZMod N,
    u * ((y : ZMod N) - (x : ZMod N)) = 1 →
    1 < (u * ((z : ZMod N) - (x : ZMod N))).val →
    a ≤ (u * ((z : ZMod N) - (x : ZMod N))).val

def SortedZero (n N : ℕ) (v : Fin (n + 3) → ℕ) : Prop :=
  StrictMono v ∧ v 0 = 0 ∧ (∀ i, v i < N) ∧
    ValidTuple (fun i ↦ (v i : ZMod N))

theorem scalar_injective_of_inverse {N : ℕ} (u v : ZMod N) (huv : u * v = 1) :
    Function.Injective (fun x : ZMod N ↦ u * x) := by
  intro x y h
  have hvu : v * u = 1 := by simpa only [mul_comm] using huv
  have hh := congrArg (fun z ↦ v * z) h
  simpa only [← mul_assoc, hvu, one_mul] using hh

theorem exists_sorted_affine_valid {n N : ℕ} [NeZero N]
    (g : Fin (n + 3) → ZMod N) (hg : ValidTuple g)
    (u : ZMod N) (hu : Function.Injective (fun x : ZMod N ↦ u * x))
    (a : Fin (n + 3)) :
    ∃ v : Fin (n + 3) → ℕ, SortedZero n N v ∧
      ∀ i, ∃ j, v j = (u * (g i - g a)).val := by
  classical
  let e : Equiv.Perm (Fin (n + 3)) := Equiv.swap 0 a
  let φ : ZMod N →+ ZMod N := {
    toFun := fun x ↦ u * x
    map_zero' := mul_zero _
    map_add' := mul_add _ }
  let w : Fin (n + 3) → ZMod N := fun i ↦ φ (g (e i) - g a)
  have hw : ValidTuple w := validTuple_comp
    (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) (g a)) φ hu
  have hw0 : w 0 = 0 := by simp [w, e, φ]
  obtain ⟨v, hv, h0, hlt, hvalid, hpre, _⟩ := exists_sorted_valid_nat_tuple w hw
  refine ⟨v, ⟨hv, h0, hlt, hvalid⟩, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hpre (e.symm i)
  rw [hw0, sub_zero] at hj
  exact ⟨j, by simpa [w, φ] using hj⟩

theorem sorted_second_le {n : ℕ} {v : Fin (n + 3) → ℕ}
    (hv : StrictMono v) (h0 : v 0 = 0) {j : Fin (n + 3)} (hj : v j ≠ 0) :
    v 1 ≤ v j := by
  have hj0 : j ≠ 0 := by intro heq; exact hj (heq ▸ h0)
  have hle : (1 : Fin (n + 3)) ≤ j := by
    have : j.val ≠ 0 := by simpa using hj0
    change 1 ≤ j.val
    omega
  exact hv.monotone hle

theorem sorted_second_eq_one {n : ℕ} {v : Fin (n + 3) → ℕ}
    (hv : StrictMono v) (h0 : v 0 = 0) (hmem : ∃ j, v j = 1) : v 1 = 1 := by
  obtain ⟨j, hj⟩ := hmem
  have hle := sorted_second_le hv h0 (show v j ≠ 0 by omega)
  have hpos := hv (show (0 : Fin (n + 3)) < 1 by simp)
  omega

theorem sorted_third_le {n : ℕ} {v : Fin (n + 3) → ℕ}
    (hv : StrictMono v) (h1 : v 1 = 1) {j : Fin (n + 3)} (hj : 1 < v j) :
    v 2 ≤ v j := by
  have hlt : (1 : Fin (n + 3)) < j := hv.lt_iff_lt.mp (by omega)
  apply hv.monotone
  change 2 ≤ j.val
  change 1 < j.val at hlt
  omega

theorem exists_minimal_pair {n N : ℕ} [NeZero N]
    (g : Fin (n + 3) → ZMod N) (hg : ValidTuple g) :
    ∃ v : Fin (n + 3) → ℕ, SortedZero n N v ∧
      PairMinimal N (v 1) (List.ofFn v) := by
  classical
  let P : ℕ → Prop := fun a ↦ ∃ v : Fin (n + 3) → ℕ, SortedZero n N v ∧ v 1 = a
  have hex : ∃ a, P a := by
    obtain ⟨v, hv, h0, hlt, hw, _, _⟩ := exists_sorted_valid_nat_tuple g hg
    exact ⟨v 1, v, ⟨hv, h0, hlt, hw⟩, rfl⟩
  obtain ⟨v, hv, ha⟩ := Nat.find_spec hex
  refine ⟨v, hv, ?_⟩
  intro x hx y hy u w huw hnonzero
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  obtain ⟨z, hz, hpre⟩ := exists_sorted_affine_valid
    (fun k ↦ (v k : ZMod N)) hv.2.2.2 u (scalar_injective_of_inverse u w huw) i
  obtain ⟨k, hk⟩ := hpre j
  have hle := sorted_second_le hz.1 hz.2.1 (show z k ≠ 0 by simpa [hk] using hnonzero)
  have hmin : Nat.find hex ≤ z 1 := Nat.find_min' hex ⟨z, hz, rfl⟩
  omega

theorem exists_minimal_third {n N : ℕ} [NeZero N]
    (hexisting : ∃ v : Fin (n + 3) → ℕ, SortedZero n N v ∧ v 1 = 1) :
    ∃ v : Fin (n + 3) → ℕ, SortedZero n N v ∧ v 1 = 1 ∧
      ThirdMinimal N (v 2) (List.ofFn v) := by
  classical
  let P : ℕ → Prop := fun a ↦ ∃ v : Fin (n + 3) → ℕ,
    SortedZero n N v ∧ v 1 = 1 ∧ v 2 = a
  have hex : ∃ a, P a := by
    obtain ⟨v, hv, h1⟩ := hexisting
    exact ⟨v 2, v, hv, h1, rfl⟩
  obtain ⟨v, hv, h1, ha⟩ := Nat.find_spec hex
  refine ⟨v, hv, h1, ?_⟩
  intro x hx y hy z hz u hu hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  obtain ⟨w, hw, hpre⟩ := exists_sorted_affine_valid
    (fun t ↦ (v t : ZMod N)) hv.2.2.2 u
    (scalar_injective_of_inverse u ((v j : ZMod N) - (v i : ZMod N)) hu) i
  have hw1 : w 1 = 1 := by
    apply sorted_second_eq_one hw.1 hw.2.1
    obtain ⟨l, hl⟩ := hpre j
    have hN : N ≠ 1 := by have := hv.2.2.1 1; omega
    exact ⟨l, by simpa only [hu, ZMod.val_one'' hN] using hl⟩
  obtain ⟨l, hl⟩ := hpre k
  have hle := sorted_third_le hw.1 hw1 (show 1 < w l by simpa [hl] using hb)
  have hmin : Nat.find hex ≤ w 2 := Nat.find_min' hex ⟨w, hw, hw1, rfl⟩
  omega

end MinModulus.PrefixCertificate
