import research.WeightedProbeCardinality
import Mathlib.Data.Nat.Prime.Infinite

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- A new coordinate in a sufficiently large cyclic factor preserves validity. -/
theorem valid_tuple_cons_in_large_cyclic_factor
    {n p : ℕ} [NeZero p] {G : Type*} [AddCommGroup G]
    (hp : n+1 < p) (g : Fin n → G) (hg : ValidTuple g) :
    ValidTuple (Fin.cons (0, (1 : ZMod p)) (fun i ↦ (g i, (0 : ZMod p)))) := by
  intro k hc hs
  have hk0 : k 0 < p := by
    have h := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (k i)) (Finset.mem_univ 0)
    rw [hc] at h
    omega
  have hz : (k 0 : ZMod p)=1 := by
    have h := congrArg (AddMonoidHom.snd G (ZMod p)) hs
    simp only [map_sum,map_nsmul] at h
    simpa [Fin.sum_univ_succ,nsmul_eq_mul] using h
  have hk : k 0=1 := by
    have h := (ZMod.natCast_eq_natCast_iff' (k 0) 1 p).mp (by simpa using hz)
    simpa only [Nat.mod_eq_of_lt hk0,Nat.mod_eq_of_lt (by omega : 1 < p)] using h
  have hrest : ∑ i : Fin n, k i.succ=n := by
    rw [Fin.sum_univ_succ,hk] at hc
    omega
  have hsum : (∑ i : Fin n, k i.succ • g i)=∑ i, g i := by
    have h := congrArg (AddMonoidHom.fst G (ZMod p)) hs
    simp only [map_sum,map_nsmul] at h
    simpa [Fin.sum_univ_succ] using h
  have hh := hg (fun i ↦ k i.succ) hrest hsum
  intro i
  refine Fin.cases hk (fun j ↦ hh j) i

/-- Any valid tuple at odd cyclic order embeds into a valid tuple with
one more coordinate at another odd cyclic order. -/
theorem exists_odd_cyclic_valid_extension_one
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) :
    ∃ L : ℕ, Odd L ∧ ∃ h : Fin (n+1) → ZMod L, ValidTuple h ∧
      ∃ φ : ZMod N →+ ZMod L, Function.Injective φ ∧
        ∀ i : Fin n, h i.succ=φ (g i) := by
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (N+n+3)
  have hpN : N < p := by omega
  have hpn : n+1 < p := by omega
  have hpodd : Odd p := hprime.odd_of_ne_two (by omega)
  let _ : NeZero p := ⟨hprime.ne_zero⟩
  have hcop : N.Coprime p := (hprime.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (NeZero.pos N) hpN)).symm
  let e := (ZMod.chineseRemainder hcop).symm.toAddEquiv
  let q : Fin (n+1) → ZMod N × ZMod p :=
    Fin.cons (0,1) (fun i ↦ (g i,0))
  have hq : ValidTuple q := valid_tuple_cons_in_large_cyclic_factor hpn g hg
  let h := fun i ↦ e (q i)
  have hh : ValidTuple h := by
    intro k hc hs
    apply hq k hc
    apply e.injective
    simpa only [map_sum,map_nsmul,h] using hs
  let φ : ZMod N →+ ZMod (N*p) := {
    toFun := fun x ↦ e (x,0)
    map_zero' := by simp
    map_add' := by intro x y; rw [← map_add]; congr 1; simp }
  have hφ : Function.Injective φ := by
    intro x y he
    exact congrArg Prod.fst (e.injective he)
  exact ⟨N*p,hN.mul hpodd,h,hh,φ,hφ,fun i ↦ rfl⟩

/-- A valid tuple at odd cyclic order embeds into valid odd cyclic tuples
in every larger dimension. All original additive relations are preserved. -/
theorem exists_odd_cyclic_valid_extension
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (r : ℕ) :
    ∃ L : ℕ, Odd L ∧ ∃ h : Fin (n+r) → ZMod L, ValidTuple h ∧
      ∃ ι : Fin n ↪ Fin (n+r), ∃ φ : ZMod N →+ ZMod L,
        Function.Injective φ ∧ ∀ i, h (ι i)=φ (g i) := by
  induction r with
  | zero =>
    exact ⟨N,hN,g,hg,Function.Embedding.refl _,AddMonoidHom.id _,
      Function.injective_id,fun _ ↦ rfl⟩
  | succ r ih =>
    obtain ⟨L,hL,h,hh,ι,φ,hφ,hprefix⟩ := ih
    let _ : NeZero L := ⟨hL.pos.ne'⟩
    obtain ⟨M,hM,q,hq,ψ,hψ,hnext⟩ := exists_odd_cyclic_valid_extension_one hL h hh
    let j : Fin n ↪ Fin (n+r+1) := ι.trans ⟨Fin.succ,Fin.succ_injective _⟩
    refine ⟨M,hM,q,hq,j,ψ.comp φ,hψ.comp hφ,?_⟩
    intro i
    change q (ι i).succ=ψ (φ (g i))
    rw [hnext,hprefix]

end MinModulus.Research
