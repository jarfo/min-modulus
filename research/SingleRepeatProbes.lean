import research.HigherMidpointEscapes

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Replace a chosen coordinate in each squarefree d-support by a doubled
anchor, then collect the coefficients at one residue. -/
noncomputable def singleRepeatProbe {n N : ℕ} [NeZero N]
    {K : Type*} [AddCommMonoid K] (g : Fin n → ZMod N) (d : ℕ)
    (a b : Fin n) (y : ZMod N) (f : Finset (Fin n) → K) : K := by
  classical
  exact ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
    if b ∈ T ∧ 2 • g a+(∑ i ∈ T.erase b, g i)=y then f T else 0

/-- For a fixed anchor and removed coordinate, validity makes the probe
at the image of a support equal to precisely that support's coefficient. -/
theorem single_repeat_probe_isolates_coefficient {n N d : ℕ} [NeZero N]
    {K : Type*} [AddCommMonoid K] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (T : Finset (Fin n)) (hT : T.card=d) (a b : Fin n) (hb : b ∈ T)
    (f : Finset (Fin n) → K) :
    singleRepeatProbe g d a b (2 • g a+(∑ i ∈ T.erase b, g i)) f=f T := by
  classical
  unfold singleRepeatProbe
  rw [Finset.sum_eq_single T]
  · simp [hb]
  · intro U hU hUT
    by_cases h : b ∈ U ∧
        2 • g a+(∑ i ∈ U.erase b, g i)=2 • g a+(∑ i ∈ T.erase b, g i)
    · have hUcard := (Finset.mem_powersetCard.mp hU).2
      have hsum := add_left_cancel h.2
      have he : (U.erase b).val=(T.erase b).val := by
        apply multiset_eq_finset_of_validTuple_card_sum g hg (T.erase b) (U.erase b).val
        · change (U.erase b).card=(T.erase b).card
          rw [Finset.card_erase_of_mem h.1,Finset.card_erase_of_mem hb,hUcard,hT]
        · exact hsum
      have heq : U=T := by
        calc
          U = insert b (U.erase b) := (Finset.insert_erase h.1).symm
          _ = insert b (T.erase b) := congrArg (insert b) (Finset.val_injective he)
          _ = T := Finset.insert_erase hb
      exact (hUT heq).elim
    · exact if_neg h
  · intro hnot
    exact (hnot (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hT⟩)).elim

/-- The complete family of probes outside the doubled half-degree cover
jointly determines every squarefree coefficient in odd degree 2k+1. -/
theorem outside_single_repeat_probes_determine_coefficients {n N k : ℕ} [NeZero N]
    {K : Type*} [AddCommMonoid K] (hk : 1 ≤ k) (hn : 2*k+2 ≤ n)
    (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (f h : Finset (Fin n) → K)
    (hprobe : ∀ a b y, y ∉ (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x) →
      singleRepeatProbe g (2*k+1) a b y f=singleRepeatProbe g (2*k+1) a b y h) :
    ∀ T : Finset (Fin n), T.card=2*k+1 → f T=h T := by
  classical
  intro T hT
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hS : (T.erase b).card=2*k := by rw [Finset.card_erase_of_mem hb,hT]; omega
  have hc := squarefree_doubled_coin_escape_count hk hN g hg (T.erase b) hS
  have hp : 0 < (Finset.univ.filter (fun a : Fin n ↦
      2 • g a+(∑ i ∈ T.erase b, g i) ∉
        (actualFibreCoinCover g (k+1)).image (fun x ↦ 2 • x))).card := by omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  have he := hprobe a b (2 • g a+(∑ i ∈ T.erase b, g i)) (Finset.mem_filter.mp ha).2
  rw [single_repeat_probe_isolates_coefficient g hg T hT a b hb f,
    single_repeat_probe_isolates_coefficient g hg T hT a b hb h] at he
  exact he

end MinModulus.Research
