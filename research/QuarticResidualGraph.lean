import research.ResidualCycleBalances
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- The graph whose edges are the two-element residual supports of an
anchor family. Vertices retain their original coordinate indices. -/
def residualFamilyGraph {n : ℕ} (R : Finset (Fin n))
    (B : Fin n → Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ a ∈ R, B a={u,v}
  symm := by
    constructor
    intro u v h
    obtain ⟨hne,a,ha,hB⟩ := h
    exact ⟨hne.symm,a,ha,hB.trans (Finset.pair_comm u v)⟩
  loopless := by constructor; intro u h; exact h.1 rfl

/-- Residual supports of single-repeat representations avoid the entire
anchor family, uniformly in their degree. -/
theorem residual_support_disjoint_anchor_family
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x) :
    ∀ a ∈ R, Disjoint (B a) R := by
  classical
  intro a har
  apply Finset.disjoint_left.mpr
  intro b hb hbr
  have hab : a ≠ b := by intro hh; subst b; exact ha a har hb
  have hsum (c : Fin n) (hcr : c ∈ R) :
      (∑ i ∈ insert c (B c), g i)+g c=x := by
    rw [Finset.sum_insert (ha c hcr)]
    calc
      _ = 2 • g c+(∑ i ∈ B c, g i) := by simp only [two_nsmul]; abel
      _ = x := hv c hcr
  have hcard : (insert a (B a)).card=(insert b (B b)).card := by
    rw [Finset.card_insert_of_notMem (ha a har),
      Finset.card_insert_of_notMem (ha b hbr),hc a har,hc b hbr]
  have hn := single_repeat_support_avoids_other_anchor g hg a b hab
    (insert a (B a)) (insert b (B b)) (by simp) hcard
    ((hsum a har).trans (hsum b hbr).symm)
  exact hn (Finset.mem_insert_of_mem hb)

/-- Equal residual supports in one fibre have the same anchor when
doubling is injective. -/
theorem residual_support_determines_anchor
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (a b : Fin n) (ha : a ∈ R) (hb : b ∈ R) (he : B a=B b) : a=b := by
  have hh := (hv a ha).trans (hv b hb).symm
  rw [he] at hh
  exact validTuple_injective g hg (hd (add_right_cancel hh))

/-- Every edge endpoint of a single-repeat residual graph lies outside
the full anchor family. -/
theorem residual_graph_adj_outside_anchor_family
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (u v : Fin n) (he : (residualFamilyGraph R B).Adj u v) :
    u ∉ R ∧ v ∉ R := by
  classical
  obtain ⟨_,a,har,hB⟩ := he
  have hh := residual_support_disjoint_anchor_family g hg x R B hc ha hv a har
  constructor
  · intro hu
    exact Finset.disjoint_left.mp hh (by rw [hB]; simp) hu
  · intro hv
    exact Finset.disjoint_left.mp hh (by rw [hB]; simp) hv

end MinModulus.Research
