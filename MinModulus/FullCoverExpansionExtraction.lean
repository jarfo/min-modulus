import MinModulus.ThinExpansionLifting

/-!
# Inductive extraction of an actual first outside expansion

An arbitrary full-cover fibre forces every squarefree outside quotient
sum to be uniquely shortest. A strictly smaller-dimensional lower bound
then constructs a one-coin expansion, and a thin fibre lifts it exactly.
For actual cycles with at least two outsiders, subbinary validity supplies
the required index window automatically. Every such expansion has a head
used at least three times. The induction hypothesis remains explicit:
neither unrestricted global bounds nor a full repeated-expansion path
are asserted here.
-/

namespace MinModulus
open Finset

/-- A nonstandard multiset with no more coins than a squarefree target
must omit one of its target coordinates. -/
theorem exists_mem_finset_not_mem_multiset_of_card_le
    {α : Type*} (S : Finset α) (p : Multiset α)
    (hc : p.card ≤ S.card) (hne : p ≠ S.val) : ∃ j ∈ S, j ∉ p := by
  classical
  by_contra hnot
  push Not at hnot
  have hle : S.val ≤ p := (Multiset.le_iff_subset S.nodup).mpr hnot
  exact hne (Multiset.eq_of_le_of_card_le hle hc).symm

/-- A full actual fibre cover forces every squarefree outside quotient
sum to have its unique original representation among ALL multisets with
no more coins. This excludes arbitrary contractions, not just doubles. -/
theorem quotient_multiset_eq_of_card_le_of_actual_fibre_cover
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (S : Finset (Fin k)) (p : Multiset (Fin k)) (hc : p.card ≤ S.card)
    (hq : (p.map (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)))).sum=
      ∑ i ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) :
    p=S.val := by
  classical
  by_contra hne
  obtain ⟨j,hj,hjp⟩ := exists_mem_finset_not_mem_multiset_of_card_le S p hc hne
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let i0 : Fin m := ⟨0,hm⟩
  let δ := S.card-p.card
  have hker : π ((∑ i ∈ S, g (e i))-(p.map (fun i ↦ g (e i))).sum)=0 := by
    simp only [map_sub,map_sum,map_multiset_sum,Multiset.map_map,Function.comp_def]
    change (∑ i ∈ S, π (g (e i)))-(p.map (fun i ↦ π (g (e i)))).sum=0
    rw [hq,sub_self]
  obtain ⟨w,hw⟩ := exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ _ hker
  let z : ZMod M := (∑ i, u i)+w-δ • u i0
  let t : Multiset (Fin (m+k)) := Multiset.replicate δ (f i0)+
    ((Finset.univ \ S).val+p).map e
  have htcard : m+t.card=m+k := by
    simp only [t,Multiset.card_add,Multiset.card_map,Multiset.card_replicate]
    change m+(δ+((Finset.univ \ S).card+p.card))=m+k
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    have hle : S.card ≤ k := by simpa using Finset.card_le_univ S
    dsimp only [δ]
    omega
  have hsum : τ z+(t.map g).sum=∑ i, g i := by
    simp only [t,Multiset.map_add,Multiset.sum_add,Multiset.map_replicate,
      Multiset.sum_replicate,Multiset.map_map,Function.comp_def]
    change τ z+(δ • g (f i0)+((∑ i ∈ Finset.univ \ S, g (e i))+
      (p.map (fun i ↦ g (e i))).sum))=∑ i, g i
    rw [show g (f i0)=τ (u i0) from hpref i0]
    dsimp only [z]
    rw [map_sub,map_add,map_nsmul,hw,Fin.sum_univ_add]
    simp only [hpref,← map_sum]
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    dsimp only [e]
    abel
  have hef (a : Fin m) (b : Fin k) : f a ≠ e b := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [f,e,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref z (hcover z) t htcard hsum
    (e j) (fun i ↦ hef i j) ?_ hg
  intro hmem
  rcases Multiset.mem_add.mp hmem with hrep | hout
  · exact hef i0 j (Multiset.mem_replicate.mp hrep).2.symm
  · obtain ⟨i,hi,heq⟩ := Multiset.mem_map.mp hout
    have hij : i=j := by
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simpa only [e,Fin.val_natAdd,Nat.add_left_cancel_iff] using hv
    subst i
    rcases Multiset.mem_add.mp hi with hcomp | hp
    · exact (Finset.mem_sdiff.mp hcomp).2 hj
    · exact hjp hp

/-- With unique minimal-length representation of the outside total,
failure of zero-adjoined quotient validity extracts a one-coin expansion.
The replacement is constructed from a genuine rival, not hypothesized. -/
theorem exists_one_coin_expansion_of_not_valid_zero_cons
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (hmin : ∀ p : Multiset (Fin k), p.card ≤ k → (p.map q).sum=∑ i, q i →
      p=(Finset.univ : Finset (Fin k)).val)
    (hnot : ¬ ValidTuple (Fin.cons 0 q)) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧ (p.map q).sum=∑ i, q i := by
  classical
  by_contra hex
  apply hnot
  intro c hc hsum
  let p : Multiset (Fin k) := ∑ i : Fin k, Multiset.replicate (c i.succ) i
  have hp : p.card=∑ i : Fin k, c i.succ := by simp [p]
  have hpsum : (p.map q).sum=∑ i : Fin k, c i.succ • q i := by
    have haux (S : Finset (Fin k)) :
        ((∑ i ∈ S, Multiset.replicate (c i.succ) i).map q).sum=∑ i ∈ S, c i.succ • q i := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih => simp [Finset.sum_insert,ha,Multiset.map_add,Multiset.sum_add,ih]
    exact haux Finset.univ
  have htotal : c 0+p.card=k+1 := by
    rw [Fin.sum_univ_succ] at hc
    rwa [hp]
  have hvalue : (p.map q).sum=∑ i, q i := by
    rw [hpsum]
    simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,smul_zero,zero_add] using hsum
  have hcpos : 0 < c 0 := by
    by_contra hnon
    have hzero : c 0=0 := by omega
    exact hex ⟨p,by omega,hvalue⟩
  have heq : p=(Finset.univ : Finset (Fin k)).val := hmin p (by omega) hvalue
  have hpcard : p.card=k := by simp [heq]
  have hcounts (i : Fin k) : p.count i=c i.succ := by
    simp [p,Multiset.count_sum',Multiset.count_replicate]
  intro i
  refine Fin.cases (by omega) (fun j ↦ ?_) i
  have hcount := congrArg (Multiset.count j) heq
  have hjcount : (Finset.univ : Finset (Fin k)).val.count j=1 :=
    Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin k)).nodup (Finset.mem_univ j)
  simpa only [hcounts,hjcount] using hcount

/-- A smaller-dimensional exclusion constructs an actual outside
quotient expansion beside ANY full-cover fibre. The exclusion is kept
explicit; there is no assumption that the global conjecture is proved. -/
theorem exists_quotient_expansion_of_actual_fibre_cover_of_no_smaller_tuple
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (hno : ¬ AdmitsValidTuple (k+1) d) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧
      (p.map (fun i ↦ ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)))).sum=
      ∑ i, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)) := by
  apply exists_one_coin_expansion_of_not_valid_zero_cons
  · intro p hc hsum
    exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover hm τ hτ g hg u hpref hcover
      Finset.univ p (by simpa using hc) hsum
  · intro hv
    exact hno ⟨_,hv⟩

/-- If that actual fibre is also thin, the extracted quotient expansion
is an exact original-group expansion, with all independent lifts intact. -/
theorem exists_actual_expansion_of_full_thin_fibre_of_no_smaller_tuple
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (hthin : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    (hno : ¬ AdmitsValidTuple (k+1) d) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i, g (Fin.natAdd m i) := by
  obtain ⟨p,hp,hq⟩ := exists_quotient_expansion_of_actual_fibre_cover_of_no_smaller_tuple
    hm τ hτ g hg u hpref hcover hno
  exact ⟨p,hp,outside_expansion_eq_of_valid_actual_thin_fibre_quotient hm τ hτ u g hg hpref hthin
    Finset.univ p (by simpa using hp) hq⟩

/-- Induction-ready form: only the bound in dimension k+1 is used,
strictly below the parent dimension m+k when m>=2. This proves existence
of the first actual expansion, not an m-step expansion path. -/
theorem exists_actual_expansion_of_full_thin_fibre_of_lower_dimensional_bound
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 2 ≤ m)
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (hthin : ∀ z : ZMod M, z ≠ ∑ i, u i →
      ∃ s : Multiset (Fin m), s.card=m-1 ∧ (s.map u).sum=z)
    (hbound : ∀ {a L : ℕ}, a < m+k → 0 < L → AdmitsValidTuple a L → globalBound a ≤ L)
    (hsmall : d < globalBound (k+1)) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i, g (Fin.natAdd m i) := by
  apply exists_actual_expansion_of_full_thin_fibre_of_no_smaller_tuple (by omega)
    τ hτ g hg u hpref hcover hthin
  intro hv
  have hdpos : 0 < d := Nat.pos_of_mul_pos_right (NeZero.pos (d*M))
  have hle := hbound (by omega : k+1 < m+k) hdpos hv
  omega

/-- Mapped cycles supply both covers automatically. A smaller-dimensional
bound and the explicit quotient-index window therefore EXTRACT the first
exact outside expansion at arbitrary positive index, with no cycle graph
or replacement support supplied by the caller. -/
theorem exists_actual_expansion_of_mapped_cycle_of_lower_dimensional_bound
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hbound : ∀ {a L : ℕ}, a < m+k → 0 < L → AdmitsValidTuple a L → globalBound a ≤ L)
    (hsmall : d < globalBound (k+1)) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i, g (Fin.natAdd m i) := by
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply exists_actual_expansion_of_full_thin_fibre_of_lower_dimensional_bound hm τ hτ g hg
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm) ?_ hbound hsmall
  intro z hz
  have hsum : (∑ i : Fin m, ((2^i.val : ℕ) : ZMod (2^m-1)))=0 := by
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self]
  exact exists_power_multiset_card_pred_of_ne_zero hm z (by simpa only [hsum] using hz)

/-- Any one-coin expansion beside a uniquely shortest squarefree total
has a coordinate used at least THREE times. If every count were at most
two, complementing it inside two copies of the full set would contract
the same total. This is a lower bound on a head, not a head-three cap. -/
theorem exists_three_le_count_of_one_coin_expansion_of_short_sum_rigidity
    {k : ℕ} {Q : Type*} [AddCommGroup Q] (q : Fin k → Q)
    (hmin : ∀ p : Multiset (Fin k), p.card ≤ k → (p.map q).sum=∑ i, q i →
      p=(Finset.univ : Finset (Fin k)).val)
    (p : Multiset (Fin k)) (hp : p.card=k+1) (hsum : (p.map q).sum=∑ i, q i) :
    ∃ i, 3 ≤ p.count i := by
  classical
  by_contra hnot
  push Not at hnot
  let U := (Finset.univ : Finset (Fin k)).val
  have hcount (i : Fin k) : U.count i=1 :=
    Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin k)).nodup (Finset.mem_univ i)
  have hle : p ≤ U+U := by
    apply Multiset.le_iff_count.mpr
    intro i
    rw [Multiset.count_add,hcount]
    have := hnot i
    omega
  let t := U+U-p
  have heq : t+p=U+U := Multiset.sub_add_cancel hle
  have hcard : t.card+(k+1)=k+k := by
    have h := congrArg Multiset.card heq
    simpa only [Multiset.card_add,hp,show U.card=k by simp [U]] using h
  have hvalue : (t.map q).sum=∑ i, q i := by
    have h := congrArg (fun s : Multiset (Fin k) ↦ (s.map q).sum) heq
    simp only [Multiset.map_add,Multiset.sum_add,hsum] at h
    change (t.map q).sum+(∑ i, q i)=(∑ i, q i)+(∑ i, q i) at h
    exact add_right_cancel h
  have ht := hmin t (by omega) hvalue
  have htc : t.card=k := by simp [ht]
  omega

/-- Subbinary validity supplies the smaller-dimensional index window
automatically for every m>=2, k>=2 cycle. No logarithmic cutoff or
fixed deficit is used. -/
theorem subbinary_cycle_index_lt_outside_succ_globalBound
    {m k d : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hsmall : d*(2^m-1) < 2^(m+k)) : d < globalBound (k+1) := by
  have hlog : Nat.log 2 (k+1) ≤ k-1 := by
    have hp := Nat.pow_log_le_self 2 (by omega : k+1 ≠ 0)
    have htwo := two_mul_le_two_pow k
    by_contra hnot
    have hle : k ≤ Nat.log 2 (k+1) := by omega
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hle
    omega
  have hlogpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  have hsplit : 2^k=2*2^(k-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hnext : 2^(k+1)=4*2^(k-1) := by rw [pow_succ',hsplit]; ring
  have hbound : 3*2^(k-1) ≤ globalBound (k+1) := by
    unfold globalBound
    rw [hnext]
    omega
  have hmexp : 4 ≤ 2^m := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
    simpa using h
  have hratio : 2*2^m ≤ 3*(2^m-1) := by omega
  have hprod := Nat.mul_le_mul_right (2^(k-1)) hratio
  have hleft : 2^(m+k) ≤ (3*2^(k-1))*(2^m-1) := by
    rw [pow_add,hsplit]
    nlinarith
  have hd : d < 3*2^(k-1) := by
    by_contra hnot
    have hmul := Nat.mul_le_mul_right (2^m-1) (by omega : 3*2^(k-1) ≤ d)
    omega
  omega

/-- In a putative minimal-dimensional subbinary counterexample with an
actual m-cycle and k>=2 outsiders, the induction hypothesis EXTRACTS an
exact first outside expansion and a head used at least three times.
Neither an index window nor a proposed replacement pattern is assumed.
This does not supply the further m-1 legal rewrites needed for exclusion. -/
theorem exists_actual_expansion_with_large_head_of_subbinary_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hbound : ∀ {a L : ℕ}, a < m+k → 0 < L → AdmitsValidTuple a L → globalBound a ≤ L)
    (hsmall : d*(2^m-1) < 2^(m+k)) :
    ∃ p : Multiset (Fin k), p.card=k+1 ∧
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i, g (Fin.natAdd m i) ∧
      ∃ i, 3 ≤ p.count i := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨p,hp,hs⟩ := exists_actual_expansion_of_mapped_cycle_of_lower_dimensional_bound
    hm τ hτ g hg hpref hbound (subbinary_cycle_index_lt_outside_succ_globalBound hm hk hsmall)
  let π := ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
  let q : Fin k → ZMod d := fun i ↦ π (g (Fin.natAdd m i))
  have hq : (p.map q).sum=∑ i, q i := by
    simpa only [q,map_multiset_sum,Multiset.map_map,Function.comp_def,map_sum] using congrArg π hs
  refine ⟨p,hp,hs,exists_three_le_count_of_one_coin_expansion_of_short_sum_rigidity q ?_ p hp hq⟩
  intro s hc hsum
  exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover (by omega) τ hτ g hg
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm) Finset.univ s (by simpa using hc) hsum

end MinModulus
