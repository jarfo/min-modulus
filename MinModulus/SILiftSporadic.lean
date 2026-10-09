import MinModulus.SILiftPairCert

/-!
# The sporadic `(5,1)` children do not lift

`L(5,1)` contains, besides the super-increasing class, four sporadic
classes modulo `30`.  The top-stratum step at `n = 6` needs every lift of
every class to `B(6) = 2 ^ 6 - 2 ^ 2 = 60` to be affine-super-increasing.
For the four sporadics the answer is stronger: **they admit no valid lift
at all**, whatever the sheet pattern and whatever the extra entry.

Each class is excluded by thirty `pair_cert_not_valid` certificates, one
per residue of the child modulus `30`.  A certificate is a pair of rivals
with matching multiplicity parities whose values differ by the sheet; it
therefore kills BOTH lifts of its residue at once, for every one of the
`2 ^ 5` sheet patterns simultaneously.  That is why thirty pairs suffice
per class instead of `32 · 60` separate witnesses.
-/

namespace MinModulus

section Sporadic

/-- Split an extra entry into its child residue and sheet. -/
lemma split_sixty (e : ZMod (siFull 4 1)) :
    ∃ r : ℕ, r < 30 ∧
      (e = ((r : ℕ) : ZMod (siFull 4 1))
        ∨ e = ((r : ℕ) : ZMod (siFull 4 1)) + siSheet 4 1) := by
  have h60 : siFull 4 1 = 60 := rfl
  haveI : NeZero (siFull 4 1) := ⟨by rw [h60]; norm_num⟩
  refine ⟨e.val % 30, Nat.mod_lt _ (by norm_num), ?_⟩
  have hlt : e.val < 60 := by have := ZMod.val_lt e; omega
  have hc : ((e.val : ℕ) : ZMod (siFull 4 1)) = e := ZMod.natCast_rightInverse e
  rcases Nat.lt_or_ge e.val 30 with h | h
  · left; rw [Nat.mod_eq_of_lt h, hc]
  · right
    rw [show e.val % 30 = e.val - 30 from by omega,
      show siSheet 4 1 = ((30 : ℕ) : ZMod (siFull 4 1)) from rfl,
      ← Nat.cast_add, show e.val - 30 + 30 = e.val from by omega, hc]


/-- The sporadic `(5,1)` class `{0, 1, 3, 15, 25}` modulo `30`, lifted. -/
abbrev sporA : Fin 5 → ZMod (siFull 4 1) := ![0, 1, 3, 15, 25]

/-- No lift of `sporA` is valid, for any sheet pattern or extra entry. -/
theorem sporA_not_valid (b : ℕ → ℕ) (e : ZMod (siFull 4 1)) :
    ¬ ValidTuple (siLiftParent 4 1 sporA b e) := by
  obtain ⟨r, hr, hev⟩ := split_sixty e
  interval_cases r
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((0 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 1, 1, 1] ![0, 1, 1, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((1 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 0, 2, 3] ![3, 0, 0, 0, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((2 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 2, 1, 1] ![0, 0, 2, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((3 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 3, 0] ![3, 2, 0, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((4 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 1, 2, 3] ![2, 0, 1, 0, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((5 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 3, 0] ![3, 1, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((6 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 1, 3, 0] ![2, 2, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((7 : ℕ) : ZMod (siFull 4 1)) ![3, 1, 0, 0, 2] ![1, 1, 0, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((8 : ℕ) : ZMod (siFull 4 1)) ![2, 2, 0, 0, 2] ![0, 2, 0, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((9 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 1, 0, 2] ![1, 0, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((10 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 1, 0, 2] ![0, 1, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((11 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 0, 2, 1] ![1, 0, 0, 4, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((12 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 2, 0, 2] ![0, 0, 2, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((13 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 2, 1] ![3, 2, 0, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((14 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 2, 1] ![0, 0, 1, 4, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((15 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 2, 1] ![3, 1, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((16 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 1, 2, 1] ![2, 2, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((17 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 2, 1] ![3, 0, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((18 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 2, 2, 1] ![2, 1, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((19 : ℕ) : ZMod (siFull 4 1)) ![3, 3, 0, 0, 0] ![1, 3, 0, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((20 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 3, 2, 1] ![2, 0, 3, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((21 : ℕ) : ZMod (siFull 4 1)) ![3, 2, 1, 0, 0] ![1, 2, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((22 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 0, 1, 2] ![0, 1, 0, 3, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((23 : ℕ) : ZMod (siFull 4 1)) ![3, 1, 2, 0, 0] ![1, 1, 2, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((24 : ℕ) : ZMod (siFull 4 1)) ![2, 2, 2, 0, 0] ![0, 2, 2, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((25 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 3, 0, 0] ![1, 0, 3, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((26 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 3, 0, 0] ![0, 1, 3, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((27 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 3, 1] ![3, 1, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((28 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 0, 3, 1] ![2, 2, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporA b e
      ((29 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 1, 3, 1] ![3, 0, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev

/-- The sporadic `(5,1)` class `{0, 1, 4, 6, 16}` modulo `30`, lifted. -/
abbrev sporB : Fin 5 → ZMod (siFull 4 1) := ![0, 1, 4, 6, 16]

/-- No lift of `sporB` is valid, for any sheet pattern or extra entry. -/
theorem sporB_not_valid (b : ℕ → ℕ) (e : ZMod (siFull 4 1)) :
    ¬ ValidTuple (siLiftParent 4 1 sporB b e) := by
  obtain ⟨r, hr, hev⟩ := split_sixty e
  interval_cases r
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((0 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 2, 0, 1] ![0, 1, 2, 0, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((1 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 1, 1, 1] ![1, 0, 1, 1, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((2 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 1, 1, 1] ![0, 1, 1, 1, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((3 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 2, 1] ![1, 0, 0, 2, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((4 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 0, 2, 1] ![0, 1, 0, 2, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((5 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 2, 1, 1] ![0, 0, 2, 1, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((6 : ℕ) : ZMod (siFull 4 1)) ![3, 1, 0, 0, 2] ![3, 3, 0, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((7 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 1, 2, 1] ![0, 0, 1, 2, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((8 : ℕ) : ZMod (siFull 4 1)) ![1, 3, 0, 0, 2] ![1, 1, 0, 0, 4]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((9 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 0, 3, 1] ![0, 0, 0, 3, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((10 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 1, 0, 2] ![2, 3, 1, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((11 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 0, 1, 2] ![3, 2, 0, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((12 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 0, 1, 2] ![2, 3, 0, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((13 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 2, 0, 2] ![2, 2, 2, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((14 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 2, 0, 2] ![1, 3, 2, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((15 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 1, 2] ![2, 2, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((16 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 1, 2] ![1, 3, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((17 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 0, 2, 2] ![2, 2, 0, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((18 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 2, 2] ![1, 3, 0, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((19 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 1, 2] ![1, 2, 2, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((20 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 2, 1, 2] ![0, 3, 2, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((21 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 1, 2, 2] ![1, 2, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((22 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 1, 2, 2] ![0, 3, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((23 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 3, 1, 2] ![0, 2, 3, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((24 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 0, 3, 2] ![0, 3, 0, 3, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((25 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 2, 2, 2] ![0, 2, 2, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((26 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 0, 3] ![1, 3, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((27 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 0, 1, 3] ![2, 2, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((28 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 1, 3] ![1, 3, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporB b e
      ((29 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 0, 3] ![1, 2, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev

/-- The sporadic `(5,1)` class `{0, 1, 4, 16, 24}` modulo `30`, lifted. -/
abbrev sporC : Fin 5 → ZMod (siFull 4 1) := ![0, 1, 4, 16, 24]

/-- No lift of `sporC` is valid, for any sheet pattern or extra entry. -/
theorem sporC_not_valid (b : ℕ → ℕ) (e : ZMod (siFull 4 1)) :
    ¬ ValidTuple (siLiftParent 4 1 sporC b e) := by
  obtain ⟨r, hr, hev⟩ := split_sixty e
  interval_cases r
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((0 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 0, 2, 3] ![0, 3, 0, 0, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((1 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 1, 1, 1] ![1, 0, 1, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((2 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 1, 1, 1] ![0, 1, 1, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((3 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 1, 2, 3] ![0, 2, 1, 0, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((4 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 0, 3, 0] ![2, 3, 0, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((5 : ℕ) : ZMod (siFull 4 1)) ![2, 2, 0, 0, 2] ![2, 0, 0, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((6 : ℕ) : ZMod (siFull 4 1)) ![1, 3, 0, 0, 2] ![1, 1, 0, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((7 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 3, 0] ![2, 2, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((8 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 3, 0] ![1, 3, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((9 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 1, 0, 2] ![1, 0, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((10 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 1, 0, 2] ![0, 1, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((11 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 3, 0] ![1, 2, 2, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((12 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 0, 2, 1] ![2, 3, 0, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((13 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 2, 0, 2] ![0, 0, 2, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((14 : ℕ) : ZMod (siFull 4 1)) ![0, 3, 0, 2, 1] ![0, 1, 0, 4, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((15 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 2, 1] ![2, 2, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((16 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 2, 1] ![1, 3, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((17 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 1, 2, 1] ![0, 0, 1, 4, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((18 : ℕ) : ZMod (siFull 4 1)) ![3, 3, 0, 0, 0] ![3, 1, 0, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((19 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 2, 1] ![1, 2, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((20 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 2, 2, 1] ![0, 3, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((21 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 1, 2] ![1, 0, 0, 3, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((22 : ℕ) : ZMod (siFull 4 1)) ![2, 3, 1, 0, 0] ![2, 1, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((23 : ℕ) : ZMod (siFull 4 1)) ![0, 0, 3, 2, 1] ![0, 2, 3, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((24 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 1, 4, 0] ![0, 3, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((25 : ℕ) : ZMod (siFull 4 1)) ![2, 2, 2, 0, 0] ![2, 0, 2, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((26 : ℕ) : ZMod (siFull 4 1)) ![1, 3, 2, 0, 0] ![1, 1, 2, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((27 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 0, 3, 1] ![2, 2, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((28 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 3, 1] ![1, 3, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporC b e
      ((29 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 0, 3] ![1, 0, 0, 2, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev

/-- The sporadic `(5,1)` class `{0, 1, 9, 15, 19}` modulo `30`, lifted. -/
abbrev sporD : Fin 5 → ZMod (siFull 4 1) := ![0, 1, 9, 15, 19]

/-- No lift of `sporD` is valid, for any sheet pattern or extra entry. -/
theorem sporD_not_valid (b : ℕ → ℕ) (e : ZMod (siFull 4 1)) :
    ¬ ValidTuple (siLiftParent 4 1 sporD b e) := by
  obtain ⟨r, hr, hev⟩ := split_sixty e
  interval_cases r
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((0 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 1, 1, 1] ![0, 1, 1, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((1 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 0, 3, 0] ![1, 0, 0, 5, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((2 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 3, 0, 1] ![0, 0, 3, 2, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((3 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 1, 0, 2] ![1, 0, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((4 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 1, 0, 2] ![0, 1, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((5 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 2, 2, 0] ![3, 1, 2, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((6 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 2, 2, 0] ![2, 2, 2, 0, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((7 : ℕ) : ZMod (siFull 4 1)) ![1, 2, 0, 2, 1] ![3, 2, 0, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((8 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 2, 1, 1] ![0, 0, 2, 3, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((9 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 0, 1, 2] ![1, 0, 0, 3, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((10 : ℕ) : ZMod (siFull 4 1)) ![2, 1, 0, 1, 2] ![0, 1, 0, 3, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((11 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 3, 0] ![3, 1, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((12 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 2, 0, 2] ![0, 0, 2, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((13 : ℕ) : ZMod (siFull 4 1)) ![3, 0, 0, 0, 3] ![1, 0, 0, 2, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((14 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 2, 1] ![0, 0, 1, 4, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((15 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 1, 2, 1] ![3, 1, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((16 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 1, 2, 1] ![2, 2, 1, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((17 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 4, 0] ![3, 1, 0, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((18 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 1, 1, 2] ![0, 0, 1, 3, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((19 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 3, 0] ![3, 0, 2, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((20 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 2, 3, 0] ![2, 1, 2, 1, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((21 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 3, 1] ![3, 1, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((22 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 0, 3, 1] ![2, 2, 0, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((23 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 2, 2, 1] ![3, 0, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((24 : ℕ) : ZMod (siFull 4 1)) ![0, 1, 2, 2, 1] ![2, 1, 2, 0, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((25 : ℕ) : ZMod (siFull 4 1)) ![1, 1, 0, 2, 2] ![3, 1, 0, 0, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((26 : ℕ) : ZMod (siFull 4 1)) ![0, 2, 0, 2, 2] ![2, 2, 0, 0, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((27 : ℕ) : ZMod (siFull 4 1)) ![3, 2, 1, 0, 0] ![1, 2, 1, 2, 0]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((28 : ℕ) : ZMod (siFull 4 1)) ![2, 0, 0, 1, 3] ![0, 0, 0, 3, 3]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev
  · exact pair_cert_not_valid (by norm_num) sporD b e
      ((29 : ℕ) : ZMod (siFull 4 1)) ![1, 0, 1, 3, 1] ![3, 0, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) hev

end Sporadic

end MinModulus
