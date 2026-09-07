import MinModulus.OneEscapeCycleLift

/-!
# Actual cycle recovery across arbitrary dyadic quotients

A quotient cycle avoiding the exceptional IMAGE stays among actual
coordinates during doubling. If the kernel is killed by 2^r, r steps
produce an original cycle: the quotient discrepancies disappear. The
structural theorem works in arbitrary abelian groups, and affine
translation and every cyclic dyadic quotient are included.

No parent validity or induction hypothesis is needed for extraction.
Actual Mersenne capacity and the half-sized-cycle global bound follow
for valid parents. Avoiding the exceptional coordinate alone is NOT
enough at deeper quotients; its quotient image must be avoided.
General cycle existence and the unrestricted global gates remain open.
-/

namespace MinModulus
open Finset

/-- A quotient cycle avoiding the exceptional image stays among actual
coordinates under arbitrarily many doubling steps. -/
theorem exists_actual_iterate_of_one_escape_quotient_cycle
    {m n : ℕ} {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (φ : G →+ Q) (g : Fin n → G) (a : Fin n)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i)
    (e : Fin m → Fin n) (R : Equiv.Perm (Fin m))
    (havoid : ∀ i, φ (g (e i)) ≠ φ (g a))
    (hcycle : ∀ i, φ (g (e (R i)))=2 • φ (g (e i))) :
    ∀ t : ℕ, ∀ i : Fin m, ∃ j : Fin n,
      g j=2^t • g (e i) ∧ φ (g j)=φ (g (e ((R^t) i))) := by
  intro t
  induction t with
  | zero => intro i; exact ⟨e i,by simp,by simp⟩
  | succ t ih =>
    intro i
    obtain ⟨j,hj,hproj⟩ := ih i
    have hja : j ≠ a := by
      intro heq
      exact havoid ((R^t) i) (hproj.symm.trans (congrArg (fun x ↦ φ (g x)) heq))
    obtain ⟨l,hl⟩ := hclosed j hja
    refine ⟨l,?_,?_⟩
    · rw [hl,hj,pow_succ',mul_smul]
    · rw [hl,map_nsmul,hproj,pow_succ',Equiv.Perm.mul_apply]
      exact (hcycle ((R^t) i)).symm

/-- If the quotient kernel is killed by 2^r, r actual doubling steps
recover a full ORIGINAL cycle. This is uniform in the kernel exponent
and works in arbitrary abelian groups, without parent validity. -/
theorem exists_actual_cycle_of_one_escape_quotient_cycle_of_kernel_killed
    {r m n : ℕ} {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (φ : G →+ Q) (hkill : ∀ x, φ x=0 → 2^r • x=0)
    (g : Fin n → G) (a : Fin n)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i)
    (e : Fin m → Fin n) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦ φ (g (e i))))
    (havoid : ∀ i, φ (g (e i)) ≠ φ (g a))
    (hcycle : ∀ i, φ (g (e (R i)))=2 • φ (g (e i))) :
    ∃ f : Fin m ↪ Fin n,
      (∀ i, φ (g (f i))=φ (g (e ((R^r) i)))) ∧
      (∀ i, g (f i)=2^r • g (e i)) ∧ ∀ i, g (f (R i))=2 • g (f i) := by
  classical
  choose F hF hproj using exists_actual_iterate_of_one_escape_quotient_cycle
    φ g a hclosed e R havoid hcycle r
  have hf : Function.Injective F := by
    intro i j heq
    apply (R^r).injective
    apply hinj
    dsimp only
    rw [← hproj i,← hproj j,heq]
  refine ⟨⟨F,hf⟩,hproj,hF,?_⟩
  intro i
  have hzero : φ (g (e (R i))-2 • g (e i))=0 := by
    rw [map_sub,map_nsmul,hcycle,sub_self]
  have h := hkill _ hzero
  rw [smul_sub,sub_eq_zero] at h
  change g (F (R i))=2 • g (F i)
  rw [hF,hF,h]
  simp only [smul_smul,Nat.mul_comm]

/-- Affine version of the uniform kernel-killing construction. Translation
by the doubling offset reduces the dynamics to pure doubling. -/
theorem exists_actual_affine_cycle_of_one_escape_quotient_cycle_of_kernel_killed
    {r m n : ℕ} {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (φ : G →+ Q) (hkill : ∀ x, φ x=0 → 2^r • x=0)
    (g : Fin n → G) (a : Fin n) (b : G)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin n) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦ φ (g (e i))))
    (havoid : ∀ i, φ (g (e i)) ≠ φ (g a))
    (hcycle : ∀ i, φ (g (e (R i)))=2 • φ (g (e i))+φ b) :
    ∃ f : Fin m ↪ Fin n,
      (∀ i, φ (g (f i))=φ (g (e ((R^r) i)))) ∧
      ∀ i, g (f (R i))=2 • g (f i)+b := by
  let u : Fin n → G := fun i ↦ g i+b
  have huclosed : ∀ i, i ≠ a → ∃ j, u j=2 • u i := by
    intro i hia
    obtain ⟨j,hj⟩ := hclosed i hia
    refine ⟨j,?_⟩
    dsimp only [u]
    rw [hj]
    simp only [two_nsmul]
    abel
  have huinj : Function.Injective (fun i ↦ φ (u (e i))) := by
    intro i j heq
    apply hinj
    dsimp only [u] at heq
    simp only [map_add,add_left_inj] at heq
    exact heq
  have huavoid : ∀ i, φ (u (e i)) ≠ φ (u a) := by
    intro i heq
    apply havoid i
    simpa only [u,map_add,add_left_inj] using heq
  have hucycle : ∀ i, φ (u (e (R i)))=2 • φ (u (e i)) := by
    intro i
    simp only [u,map_add,hcycle,two_nsmul]
    abel
  obtain ⟨f,hproj,_,hf⟩ := exists_actual_cycle_of_one_escape_quotient_cycle_of_kernel_killed
    φ hkill u a huclosed e R huinj huavoid hucycle
  refine ⟨f,?_,?_⟩
  · intro i
    simpa only [u,map_add,add_left_inj] using hproj i
  · intro i
    have h := hf i
    dsimp only [u] at h
    simp only [two_nsmul] at h ⊢
    have heq : g (f (R i))+b=(g (f i)+g (f i)+b)+b := by
      rw [h]
      abel
    exact add_right_cancel heq

/-- At any dyadic quotient index 2^r, the kernel is killed by 2^r.
An injective quotient cycle avoiding the exceptional IMAGE therefore
recovers an original affine cycle, with all coordinates constructed. -/
theorem exists_actual_affine_cycle_of_one_escape_dyadic_quotient_cycle
    {r m n M : ℕ} [NeZero M]
    (g : Fin n → ZMod (2^r*M)) (a : Fin n) (b : ZMod (2^r*M))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin n) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))))
    (havoid : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i)) ≠
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g a))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) b) :
    ∃ f : Fin m ↪ Fin n,
      (∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (f i))=
        ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e ((R^r) i)))) ∧
      ∀ i, g (f (R i))=2 • g (f i)+b := by
  letI : NeZero (2^r*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  let φ := (ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M)).toAddMonoidHom
  apply exists_actual_affine_cycle_of_one_escape_quotient_cycle_of_kernel_killed
    φ ?_ g a b hclosed e R hinj havoid hcycle
  intro x hx
  rw [← zmodScaleHom_castHom]
  change ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) x=0 at hx
  rw [hx,map_zero]

/-- The uniform recovered cycle is placed among the ORIGINAL coordinates
in the prefix convention needed by the existing sharp cycle consumers. -/
theorem exists_perm_actual_affine_cycle_of_one_escape_dyadic_quotient_cycle
    {r m k M : ℕ} [NeZero M]
    (g : Fin (m+k) → ZMod (2^r*M)) (a : Fin (m+k)) (b : ZMod (2^r*M))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))))
    (havoid : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i)) ≠
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g a))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) b) :
    ∃ E : Equiv.Perm (Fin (m+k)),
      ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b := by
  obtain ⟨f,_,hf⟩ := exists_actual_affine_cycle_of_one_escape_dyadic_quotient_cycle
    g a b hclosed e R hinj havoid hcycle
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) f
    (Fin.castAdd_injective m k) f.injective
  exact ⟨E,by intro i; simpa only [hE] using hf i⟩

/-- Uniform numerical consumer at EVERY dyadic quotient index: actual
Mersenne capacity always holds, and a half-sized recovered cycle gives
the full global bound. There is no fixed valuation or induction premise. -/
theorem fibre_capacity_and_global_bound_of_one_escape_dyadic_quotient_cycle
    {r m k M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod (2^r*M)) (hg : ValidTuple g)
    (a : Fin (m+k)) (b : ZMod (2^r*M))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))))
    (havoid : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i)) ≠
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g a))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) b) :
    ((2^m-1) ∣ 2^r*M ∧ 2^k*(2^m-1) ≤ 2^r*M) ∧
      (k ≤ m+1 → globalBound (m+k) ≤ 2^r*M) := by
  letI : NeZero (2^r*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨E,hE⟩ := exists_perm_actual_affine_cycle_of_one_escape_dyadic_quotient_cycle
    g a b hclosed e R hinj havoid hcycle
  exact ⟨affine_doubling_cycle_fibre_capacity hm g hg E b R hE,
    fun hk ↦ global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm hk g hg E b R hE⟩

end MinModulus
