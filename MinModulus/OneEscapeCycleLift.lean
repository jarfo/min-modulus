import MinModulus.PrimitiveCriticalInduction

/-!
# Recover actual cycles from half-quotient cycles

Actual predecessor targets recover an affine cycle in the original
coordinates from an injective half-quotient cycle. The chosen lifts may
change: doubling kills the two-element kernel, making the reconstructed
cycle law exact. One-escape closure supplies the targets automatically
for a selected quotient cycle away from the exceptional coordinate.

Fibre capacity, the full global bound for half-sized cycles, and direct
G3 exclusion now consume these quotient data instead of an assumed actual
cycle. No theorem extracts the required quotient cycle from every critical
tuple; the exceptional-on-cycle case and the unrestricted gates remain open.
-/

namespace MinModulus
open Finset

/-- A half-quotient affine cycle lifts to an ACTUAL cycle as soon as the
selected original predecessors have actual doubling targets. The targets,
not arbitrary quotient representatives, supply the lifted coordinates.
Parent validity is not needed for this structural construction. -/
theorem exists_actual_affine_cycle_of_half_quotient_cycle
    {m n M : ℕ} [NeZero M]
    (g : Fin n → ZMod (2*M)) (b : ZMod (2*M)) (e : Fin m → Fin n)
    (R : Equiv.Perm (Fin m))
    (hclosed : ∀ i, ∃ j, g j=2 • g (e i)+b)
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) b) :
    ∃ f : Fin m ↪ Fin n,
      (∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (f i))=
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))) ∧
      ∀ i, g (f (R i))=2 • g (f i)+b := by
  classical
  choose F hF using hclosed
  let f : Fin m → Fin n := fun i ↦ F (R.symm i)
  have hproj (i : Fin m) :
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (f i))=
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i)) := by
    dsimp only [f]
    rw [hF,map_add,map_nsmul]
    simpa only [Equiv.apply_symm_apply] using (hcycle (R.symm i)).symm
  have hf : Function.Injective f := by
    intro i j heq
    apply hinj
    dsimp only
    rw [← hproj i,← hproj j,heq]
  refine ⟨⟨f,hf⟩,hproj,?_⟩
  intro i
  have hd : 2 • g (f i)=2 • g (e i) := by
    rw [← zmodScaleHom_castHom,← zmodScaleHom_castHom,hproj]
  change g (f (R i))=2 • g (f i)+b
  dsimp only [f]
  rw [Equiv.symm_apply_apply,hF]
  exact congrArg (fun x ↦ x+b) hd.symm

/-- One-escape closure supplies the predecessor targets automatically
for any actual half-quotient cycle selected away from the exception.
The selected lifts may change, but every recovered coordinate is actual. -/
theorem exists_actual_affine_cycle_of_one_escape_half_quotient_cycle
    {m n M : ℕ} [NeZero M]
    (g : Fin n → ZMod (2*M)) (a : Fin n) (b : ZMod (2*M))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin n) (he : ∀ i, e i ≠ a) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) b) :
    ∃ f : Fin m ↪ Fin n,
      (∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (f i))=
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))) ∧
      ∀ i, g (f (R i))=2 • g (f i)+b :=
  exists_actual_affine_cycle_of_half_quotient_cycle g b e R
    (fun i ↦ hclosed (e i) (he i)) hinj hcycle

/-- Put the recovered actual cycle into the prefix convention used by
the existing fibre-capacity and global-bound consumers. -/
theorem exists_perm_actual_affine_cycle_of_half_quotient_cycle
    {m k M : ℕ} [NeZero M]
    (g : Fin (m+k) → ZMod (2*M)) (b : ZMod (2*M)) (e : Fin m → Fin (m+k))
    (R : Equiv.Perm (Fin m))
    (hclosed : ∀ i, ∃ j, g j=2 • g (e i)+b)
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) b) :
    ∃ E : Equiv.Perm (Fin (m+k)),
      ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b := by
  obtain ⟨f,_,hf⟩ := exists_actual_affine_cycle_of_half_quotient_cycle g b e R hclosed hinj hcycle
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) f
    (Fin.castAdd_injective m k) f.injective
  exact ⟨E,by intro i; simpa only [hE] using hf i⟩

/-- The ACTUAL Mersenne divisor and full outside cube capacity now follow
from a half-quotient cycle and its actual predecessor targets. -/
theorem fibre_capacity_of_actual_half_quotient_cycle_targets
    {m k M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (b : ZMod (2*M)) (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hclosed : ∀ i, ∃ j, g j=2 • g (e i)+b)
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) b) :
    (2^m-1) ∣ 2*M ∧ 2^k*(2^m-1) ≤ 2*M := by
  letI : NeZero (2*M) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne M)⟩
  obtain ⟨E,hE⟩ := exists_perm_actual_affine_cycle_of_half_quotient_cycle g b e R hclosed hinj hcycle
  exact affine_doubling_cycle_fibre_capacity hm g hg E b R hE

/-- The full global bound for any half-sized quotient cycle with actual
predecessor targets; no actual cycle embedding is assumed in the input. -/
theorem global_lower_bound_of_half_sized_quotient_cycle_targets
    {m k M : ℕ} [NeZero M] (hm : 2 ≤ m) (hk : k ≤ m+1)
    (g : Fin (m+k) → ZMod (2*M)) (hg : ValidTuple g)
    (b : ZMod (2*M)) (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hclosed : ∀ i, ∃ j, g j=2 • g (e i)+b)
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) b) :
    globalBound (m+k) ≤ 2*M := by
  letI : NeZero (2*M) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne M)⟩
  obtain ⟨E,hE⟩ := exists_perm_actual_affine_cycle_of_half_quotient_cycle g b e R hclosed hinj hcycle
  exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm hk g hg E b R hE

/-- Direct G3 extraction: a half-sized affine cycle in the actual half
quotient is already excluded when its selected original predecessors
have actual doubling targets. A one-escape tuple supplies these targets
automatically when the selected quotient cycle avoids its exception. -/
theorem not_validTuple_exceptional_of_half_sized_quotient_cycle_targets
    {m k : ℕ} (hm : 2 ≤ m) (hk : k ≤ m+1)
    (hnpow : 2^Nat.log 2 (m+k) ≠ m+k)
    (g : Fin (m+k) → ZMod (2*globalBound (m+k-1)))
    (b : ZMod (2*globalBound (m+k-1))) (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hclosed : ∀ i, ∃ j, g j=2 • g (e i)+b)
    (hinj : Function.Injective (fun i ↦ ZMod.castHom
      (dvd_mul_left (globalBound (m+k-1)) 2) (ZMod (globalBound (m+k-1))) (g (e i))))
    (hcycle : ∀ i, ZMod.castHom
      (dvd_mul_left (globalBound (m+k-1)) 2) (ZMod (globalBound (m+k-1))) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left (globalBound (m+k-1)) 2)
        (ZMod (globalBound (m+k-1))) (g (e i))+
      ZMod.castHom (dvd_mul_left (globalBound (m+k-1)) 2) (ZMod (globalBound (m+k-1))) b) :
    ¬ ValidTuple g := by
  have hn3 : 3 ≤ m+k := by
    by_contra hnot
    have hn2 : m+k=2 := by omega
    norm_num [hn2] at hnpow
  have hB : 2 ≤ globalBound (m+k-1) := (nmin_eq (by omega : 2 ≤ m+k-1)).1.1
  letI : NeZero (globalBound (m+k-1)) := ⟨by omega⟩
  obtain ⟨E,hE⟩ := exists_perm_actual_affine_cycle_of_half_quotient_cycle g b e R hclosed hinj hcycle
  exact not_validTuple_exceptional_of_half_sized_affine_doubling_cycle hm hk hnpow g E b R hE

end MinModulus
