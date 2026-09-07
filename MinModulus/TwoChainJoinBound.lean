import MinModulus.TwoChainJoin

/-! Full global and exact-stratum common-endpoint bounds. The actual
half deletion identifies the two exceptions and retains one exception
with its affine targets. The completed one-escape child bounds and
common-endpoint G3 close every valuation without conjectural inputs. -/

namespace MinModulus

/-- Identifying and deleting one of TWO exceptional endpoints leaves
one actual exception. Targets at the deleted endpoint redirect to its
identified partner; no arbitrary smaller tuple is substituted. -/
theorem one_escape_after_identifying_two_exceptions
    {n : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : Fin (n+1) → G) (j a : Fin (n+1)) (b : G)
    (haj : a ≠ j) (hpair : φ (g j)=φ (g a))
    (hclosed : ∀ i, i ≠ j → i ≠ a → ∃ l, g l=2 • g i+b) :
    ∃ a' : Fin n, j.succAbove a'=a ∧
      ∀ i, i ≠ a' → ∃ l, φ (g (j.succAbove l))=2 • φ (g (j.succAbove i))+φ b := by
  obtain ⟨a',ha'⟩ := Fin.exists_succAbove_eq haj
  refine ⟨a',ha',?_⟩
  intro i hia
  have hi : j.succAbove i ≠ a := by
    intro heq
    exact hia (Fin.succAbove_right_injective (heq.trans ha'.symm))
  obtain ⟨l,hl⟩ := hclosed _ (Fin.succAbove_ne j i) hi
  have hvalue : φ (g l)=2 • φ (g (j.succAbove i))+φ b := by rw [hl,map_add,map_nsmul]
  by_cases hlj : l=j
  · refine ⟨a',?_⟩
    rw [ha',← hpair]
    simpa only [hlj] using hvalue
  · obtain ⟨l',hl'⟩ := Fin.exists_succAbove_eq hlj
    exact ⟨l',by rw [hl']; exact hvalue⟩

/-- Equal doubled exceptions give an ACTUAL valid one-escape half
child, retaining its original anchor and affine doubling offset. -/
theorem exists_actual_one_escape_half_of_equal_double_exceptions
    {n M : ℕ} [NeZero M]
    (g : Fin (n+1) → ZMod (2*M)) (hg : ValidTuple g)
    (j a : Fin (n+1)) (b : ZMod (2*M)) (haj : a ≠ j)
    (hdouble : 2 • g j=2 • g a)
    (hclosed : ∀ i, i ≠ j → i ≠ a → ∃ l, g l=2 • g i+b) :
    ∃ a' : Fin n, j.succAbove a'=a ∧
      ValidTuple (fun i : Fin n ↦ ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))) ∧
      ∀ i, i ≠ a' → ∃ l,
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (j.succAbove l))=
        2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))+
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) b := by
  let π := (ZMod.castHom (dvd_mul_left M 2) (ZMod M)).toAddMonoidHom
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hzero : (g j-g a)+(g j-g a)=0 := by
    simp only [two_nsmul] at hdouble
    calc
      _=(g j+g j)-(g a+g a) := by abel
      _=0 := sub_eq_zero.mpr hdouble
  have hpair : π (g j)=π (g a) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero rfl _ hzero with hz | hh
    · simp [hz]
    · simp [hh,π]
  obtain ⟨a',ha',hc⟩ := one_escape_after_identifying_two_exceptions π g j a b haj hpair hclosed
  exact ⟨a',ha',validTuple_actual_half_of_doubled_collision g hg j a haj hdouble,hc⟩

/-- Actual two-chain arrows close away from their two distinct terminal
coordinates; a common endpoint supplies the actual doubled collision. -/
theorem exists_equal_double_exceptions_of_two_chain_join
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) :
    ∃ j a : Fin (A+L), a ≠ j ∧ 2 • g j=2 • g a ∧
      ∀ i, i ≠ j → i ≠ a → ∃ l, g l=2 • g i := by
  let j : Fin (A+L) := Fin.castAdd L ⟨A-1,by omega⟩
  let a : Fin (A+L) := Fin.natAdd A ⟨L-1,by omega⟩
  refine ⟨j,a,?_,?_,?_⟩
  · intro he
    have hv := congrArg Fin.val he
    simp only [a,j,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · simp only [j,a,hleft,hright,← mul_nsmul,← pow_succ,
      Nat.sub_add_cancel (by omega : 1 ≤ A),Nat.sub_add_cancel (by omega : 1 ≤ L)]
    exact hjoin
  · intro i hij hia
    refine Fin.addCases (fun i hij _ ↦ ?_) (fun i _ hia ↦ ?_) i hij hia
    · have hn : i.val+1 < A := by
        by_contra h
        apply hij
        apply congrArg (Fin.castAdd L)
        apply Fin.ext
        change i.val=A-1
        omega
      refine ⟨Fin.castAdd L ⟨i.val+1,hn⟩,?_⟩
      rw [hleft,hleft,← mul_nsmul,← pow_succ]
    · have hn : i.val+1 < L := by
        by_contra h
        apply hia
        apply congrArg (Fin.natAdd A)
        apply Fin.ext
        change i.val=L-1
        omega
      refine ⟨Fin.natAdd A ⟨i.val+1,hn⟩,?_⟩
      rw [hright,hright,← mul_nsmul,← pow_succ]

/-- A common-endpoint two-chain tuple has a specified ACTUAL
one-escape half child. The original deleted coordinate is retained. -/
theorem exists_actual_one_escape_half_of_two_chain_join
    {A L N M : ℕ} [NeZero M] (hA : 0 < A) (hNM : N=2*M)
    (g : Fin (A+(L+1)) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd (L+1) i)=2^i.val • x)
    (hright : ∀ i : Fin (L+1), g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^(L+1) • y) :
    ∃ j : Fin (A+(L+1)), ∃ a' : Fin (A+L),
      ValidTuple (fun i : Fin (A+L) ↦ ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))) ∧
      ∀ i, i ≠ a' → ∃ l,
        ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove l))=
        2 • ZMod.castHom (by rw [hNM]; exact dvd_mul_left M 2) (ZMod M) (g (j.succAbove i)) := by
  subst N
  obtain ⟨j,a,haj,hd,hc⟩ := exists_equal_double_exceptions_of_two_chain_join hA (by omega) g x y hleft hright hjoin
  obtain ⟨a',_,hv,hc'⟩ := exists_actual_one_escape_half_of_equal_double_exceptions
    g hg j a 0 haj hd (by
      intro i hij hia
      obtain ⟨l,hl⟩ := hc i hij hia
      exact ⟨l,by simpa only [add_zero] using hl⟩)
  exact ⟨j,a',hv,by simpa using hc'⟩

/-- Every exact stratum closes after ONE actual half deletion, because
the child belongs to the already completed one-escape class. The new
common-endpoint G3 theorem consumes the sole high-stratum boundary. -/
theorem stratum_lower_bound_of_valid_two_chain_join_succ
    {A L s q : ℕ} (hA : 0 < A) (hn : 3 ≤ A+(L+1)) (hq : Odd q)
    (g : Fin (A+(L+1)) → ZMod (2^s*q)) (hg : ValidTuple g) (x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd (L+1) i)=2^i.val • x)
    (hright : ∀ i : Fin (L+1), g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^(L+1) • y) : stratumBound (A+(L+1)) s ≤ 2^s*q := by
  cases s with
  | zero =>
    letI : NeZero q := ⟨hq.pos.ne'⟩
    obtain ⟨j,a,haj,hd,_⟩ := exists_equal_double_exceptions_of_two_chain_join hA (by omega) g x y hleft hright hjoin
    have he : g j=g a := by
      apply add_self_injective_zmod (by simpa using hq)
      simpa only [two_nsmul] using hd
    exact False.elim (haj (validTuple_injective g hg he).symm)
  | succ s =>
    have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
    letI : NeZero (2^s*q) := ⟨hM.ne'⟩
    letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
    have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
    obtain ⟨j,a',hv,hc⟩ := exists_actual_one_escape_half_of_two_chain_join hA hN g hg x y hleft hright hjoin
    have hchild := stratum_lower_bound_of_valid_one_escape_affine_doubling
      (by omega : 2 ≤ A+L) hq _ hv a' 0 (by simpa using hc)
    by_cases hs : s+1 ≤ Nat.log 2 (A+(L+1))
    · have huncap : 2^(A+L)-2^s ≤ stratumBound (A+L) s := by
        unfold stratumBound
        exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) (min_le_left _ _)) _
      have hb : 2^(A+(L+1))-2^(s+1) ≤ 2^(s+1)*q := by
        calc
          _=2*(2^(A+L)-2^s) := by rw [show A+(L+1)=(A+L)+1 by omega,pow_succ',pow_succ',Nat.mul_sub_left_distrib]
          _≤2*(2^s*q) := Nat.mul_le_mul_left 2 (huncap.trans hchild)
          _=_ := hN.symm
      simpa only [stratumBound,min_eq_left hs] using hb
    · have hgchild := global_lower_bound_of_valid_one_escape_affine_doubling
        (by omega : 2 ≤ A+L) _ hv a' 0 (by simpa using hc)
      have hb : globalBound ((A+L)+1) ≤ 2^(s+1)*q := by
        apply globalBound_succ_le_of_high_stratum_half_bound (by omega)
          (by simpa only [Nat.add_assoc] using (Nat.lt_of_not_ge hs)) hgchild
        intro hp he
        have hboundary : 2^(s+1)*q=2*globalBound (A+(L+1)-1) := by
          rw [hN,he]
          congr 2
        exact not_validTuple_of_equal_endpoint_chains_at_exceptional_modulus hA (by omega) hn hp hboundary
          g (Equiv.refl _) 0 x y (by simpa using hleft) (by simpa using hright) hjoin hg
      simpa only [Nat.add_assoc,stratumBound,min_eq_right (by omega : Nat.log 2 (A+(L+1)) ≤ s+1),globalBound] using hb

/-- FULL global bound for every pair of actual chains with a common
doubled endpoint, regardless of depth, parity, orientation or target
membership. No unrestricted conjectural premise remains. -/
theorem global_lower_bound_of_valid_two_chain_join
    {A L N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 3 ≤ A+L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : globalBound (A+L) ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  cases L with
  | zero => omega
  | succ L =>
    have hb := stratum_lower_bound_of_valid_two_chain_join_succ hA hn hq g hg x y hleft hright hjoin
    have hle : globalBound (A+(L+1)) ≤ stratumBound (A+(L+1)) s := by
      unfold globalBound stratumBound
      exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) (min_le_right _ _)) _
    exact hle.trans hb

/-- Every exact stratum, including odd G2, for the whole common-
endpoint class. The odd case is impossible by actual doubled collision. -/
theorem stratum_lower_bound_of_valid_two_chain_join
    {A L s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hn : 3 ≤ A+L)
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g) (x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : stratumBound (A+L) s ≤ 2^s*q := by
  cases L with
  | zero => omega
  | succ L => exact stratum_lower_bound_of_valid_two_chain_join_succ hA hn hq g hg x y hleft hright hjoin

/-- Full global common-endpoint closure for arbitrary original affine
offsets and reindexings, with no unit or arm-order input. -/
theorem global_lower_bound_of_valid_affine_two_chain_join
    {A L N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 3 ≤ A+L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : globalBound (A+L) ≤ N := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact global_lower_bound_of_valid_two_chain_join hA hL hn _ hv x y hleft hright hjoin

/-- Full exact-stratum common-endpoint closure on the original affine
tuple, including all high valuations and odd-modulus impossibility. -/
theorem stratum_lower_bound_of_valid_affine_two_chain_join
    {A L s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hn : 3 ≤ A+L)
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : stratumBound (A+L) s ≤ 2^s*q := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact stratum_lower_bound_of_valid_two_chain_join hq hA hL hn _ hv x y hleft hright hjoin

end MinModulus
