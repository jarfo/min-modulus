import MinModulus.G3FiveModTwentyFour

/-!
# Kernel-checked rival certificates for odd moduli below `2^n - 1`, `n ≤ 5`

Each `Rival` is a natural multiplicity vector.  A rival *covers* a normalized
tuple when its total is the tuple length, it differs from the all-ones vector,
and its weighted sum agrees with the tuple sum modulo `N`.  The lists below are
data; coverage of every normalized tuple is established by kernel evaluation
(`decide`), and soundness is proved separately by turning a covering rival into
an actual multiplicity rival of the tuple.  No additional axiom is used.

Normalizations used by the consumers:
* `n = 3, 4`: translation puts the first coordinate at `0`; all remaining
  coordinates range over `ZMod N`.
* `n = 5`: if some coordinate difference is a unit, translation, permutation
  and unit scaling give `(0,1,a,b,c)`; otherwise translation gives
  `(0,a,b,c,d)` with every `a,b,c,d` a non-unit.
-/

namespace MinModulus.OddSmallCertificate

/-- A candidate multiplicity vector for a three-coordinate tuple. -/
structure Rival3 where
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ

/-- A candidate multiplicity vector for a four-coordinate tuple. -/
structure Rival4 where
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ

/-- A candidate multiplicity vector for a five-coordinate tuple. -/
structure Rival5 where
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ

def Rival3.vector (r : Rival3) : Fin 3 → ℕ := ![r.k0,r.k1,r.k2]
def Rival4.vector (r : Rival4) : Fin 4 → ℕ := ![r.k0,r.k1,r.k2,r.k3]
def Rival5.vector (r : Rival5) : Fin 5 → ℕ := ![r.k0,r.k1,r.k2,r.k3,r.k4]

def Rival3.valid (r : Rival3) : Bool :=
  decide (r.k0+r.k1+r.k2=3 ∧ ¬ (r.k0=1 ∧ r.k1=1 ∧ r.k2=1))
def Rival4.valid (r : Rival4) : Bool :=
  decide (r.k0+r.k1+r.k2+r.k3=4 ∧ ¬ (r.k0=1 ∧ r.k1=1 ∧ r.k2=1 ∧ r.k3=1))
def Rival5.valid (r : Rival5) : Bool :=
  decide (r.k0+r.k1+r.k2+r.k3+r.k4=5 ∧
    ¬ (r.k0=1 ∧ r.k1=1 ∧ r.k2=1 ∧ r.k3=1 ∧ r.k4=1))

/-- Weighted-sum hit on the translated tuple `(0,a,b)` modulo `N`. -/
def Rival3.hits (N : ℕ) (r : Rival3) (a b : ℕ) : Bool :=
  decide ((r.k1*a+r.k2*b)%N=(a+b)%N)
/-- Weighted-sum hit on the translated tuple `(0,a,b,c)` modulo `N`. -/
def Rival4.hits (N : ℕ) (r : Rival4) (a b c : ℕ) : Bool :=
  decide ((r.k1*a+r.k2*b+r.k3*c)%N=(a+b+c)%N)
/-- Weighted-sum hit on the normalized tuple `(0,1,a,b,c)` modulo `N`. -/
def Rival5.hitsUnit (N : ℕ) (r : Rival5) (a b c : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c)%N=(1+a+b+c)%N)
/-- Weighted-sum hit on the translated tuple `(0,a,b,c,d)` modulo `N`. -/
def Rival5.hitsZero (N : ℕ) (r : Rival5) (a b c d : ℕ) : Bool :=
  decide ((r.k1*a+r.k2*b+r.k3*c+r.k4*d)%N=(a+b+c+d)%N)

/-- Rivals covering every translated triple modulo `5`. -/
def rivals3 : List Rival3 := [
  ⟨0,0,3⟩,
  ⟨0,1,2⟩,
  ⟨0,2,1⟩,
  ⟨0,3,0⟩,
  ⟨1,0,2⟩,
  ⟨3,0,0⟩]

/-- Rivals covering every translated four-tuple modulo `9`. -/
def rivals4_9 : List Rival4 := [
  ⟨0,0,0,4⟩,
  ⟨0,0,1,3⟩,
  ⟨0,0,2,2⟩,
  ⟨1,1,0,2⟩,
  ⟨0,0,3,1⟩,
  ⟨0,0,4,0⟩,
  ⟨0,1,0,3⟩,
  ⟨0,1,1,2⟩,
  ⟨0,1,2,1⟩,
  ⟨0,2,0,2⟩,
  ⟨1,0,1,2⟩,
  ⟨1,0,2,1⟩,
  ⟨1,0,3,0⟩,
  ⟨0,2,1,1⟩,
  ⟨0,2,2,0⟩,
  ⟨0,1,3,0⟩,
  ⟨1,0,0,3⟩]

/-- Rivals covering every translated four-tuple modulo `11`. -/
def rivals4_11 : List Rival4 := [
  ⟨0,0,0,4⟩,
  ⟨0,0,1,3⟩,
  ⟨0,0,2,2⟩,
  ⟨0,0,3,1⟩,
  ⟨0,0,4,0⟩,
  ⟨1,1,0,2⟩,
  ⟨0,1,0,3⟩,
  ⟨0,1,1,2⟩,
  ⟨0,1,2,1⟩,
  ⟨0,1,3,0⟩,
  ⟨1,0,1,2⟩,
  ⟨1,0,2,1⟩,
  ⟨0,2,0,2⟩,
  ⟨0,2,2,0⟩,
  ⟨0,2,1,1⟩,
  ⟨0,4,0,0⟩,
  ⟨3,1,0,0⟩,
  ⟨0,3,0,1⟩,
  ⟨0,3,1,0⟩,
  ⟨1,3,0,0⟩,
  ⟨1,0,0,3⟩,
  ⟨1,0,3,0⟩]

/-- Rivals covering every translated four-tuple modulo `13`. -/
def rivals4_13 : List Rival4 := [
  ⟨0,0,0,4⟩,
  ⟨0,0,1,3⟩,
  ⟨0,0,2,2⟩,
  ⟨0,0,3,1⟩,
  ⟨0,0,4,0⟩,
  ⟨1,1,0,2⟩,
  ⟨0,1,0,3⟩,
  ⟨0,1,1,2⟩,
  ⟨0,1,2,1⟩,
  ⟨0,1,3,0⟩,
  ⟨1,0,1,2⟩,
  ⟨1,0,2,1⟩,
  ⟨0,2,0,2⟩,
  ⟨0,2,2,0⟩,
  ⟨0,2,1,1⟩,
  ⟨0,4,0,0⟩,
  ⟨3,1,0,0⟩,
  ⟨0,3,0,1⟩,
  ⟨0,3,1,0⟩,
  ⟨1,3,0,0⟩,
  ⟨1,0,0,3⟩,
  ⟨1,0,3,0⟩,
  ⟨3,0,0,1⟩,
  ⟨3,0,1,0⟩,
  ⟨4,0,0,0⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `17`. -/
def rivals5Unit17 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,1,0,2,2⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,3,0,1,0⟩,
  ⟨0,0,0,1,4⟩,
  ⟨1,0,0,1,3⟩,
  ⟨0,0,1,2,2⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `19`. -/
def rivals5Unit19 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,0,2,1,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,3,0,0,2⟩,
  ⟨1,3,0,1,0⟩,
  ⟨0,4,0,0,1⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,1,1,3,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,3,2,0⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `21`. -/
def rivals5Unit21 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,3,0,1,0⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,4,0,1,0⟩,
  ⟨4,0,0,1,0⟩,
  ⟨0,1,1,0,3⟩,
  ⟨0,1,0,2,2⟩,
  ⟨0,1,3,0,1⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,1,1,3,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨2,3,0,0,0⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,2,3⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `23`. -/
def rivals5Unit23 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,0,1,0,3⟩,
  ⟨1,3,0,1,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,0,4,1⟩,
  ⟨0,0,1,4,0⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,0,3,0,2⟩,
  ⟨1,4,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,3,2,0⟩,
  ⟨0,5,0,0,0⟩,
  ⟨5,0,0,0,0⟩,
  ⟨0,1,0,4,0⟩,
  ⟨0,1,3,1,0⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `25`. -/
def rivals5Unit25 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,3,0,1,0⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,4,0,1,0⟩,
  ⟨4,0,0,1,0⟩,
  ⟨0,1,1,0,3⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,3,2,0,0⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,1,0,4,0⟩,
  ⟨1,0,0,4,0⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,0,3,1⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,1,1,3⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,3,1,1⟩,
  ⟨0,0,3,2,0⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,1,0,1,3⟩,
  ⟨1,0,3,1,0⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `27`. -/
def rivals5Unit27 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,3,0,1,0⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,3,2,0,0⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,4,0,1,0⟩,
  ⟨4,0,0,1,0⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨1,3,0,0,1⟩,
  ⟨1,4,0,0,0⟩,
  ⟨0,5,0,0,0⟩,
  ⟨0,4,0,0,1⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,1,1,3⟩,
  ⟨0,0,2,0,3⟩,
  ⟨3,1,1,0,0⟩,
  ⟨0,0,4,0,1⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,0,3,1,1⟩,
  ⟨0,1,0,1,3⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,1,0,3,1⟩,
  ⟨1,0,0,3,1⟩,
  ⟨1,0,3,1,0⟩,
  ⟨1,3,1,0,0⟩,
  ⟨3,1,0,0,1⟩,
  ⟨0,0,4,1,0⟩,
  ⟨0,1,0,4,0⟩,
  ⟨0,2,0,0,3⟩,
  ⟨1,0,0,1,3⟩]

/-- Rivals covering every sorted normalized five-tuple `(0,1,a,b,c)`, `a ≤ b ≤ c`, modulo `29`. -/
def rivals5Unit29 : List Rival5 := [
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,2,0,3,0⟩,
  ⟨1,3,0,1,0⟩,
  ⟨2,0,0,3,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,4,0,1,0⟩,
  ⟨4,0,0,1,0⟩,
  ⟨0,1,1,0,3⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,0,3,0,1⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,3,2,0,0⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,3,2,0⟩,
  ⟨1,3,0,0,1⟩,
  ⟨3,1,1,0,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,0,1,1,3⟩,
  ⟨0,0,3,1,1⟩,
  ⟨1,4,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,0,3,1⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,1,3,1,0⟩,
  ⟨1,0,0,1,3⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,1,0,4,0⟩,
  ⟨1,0,0,4,0⟩,
  ⟨1,0,1,3,0⟩,
  ⟨1,3,1,0,0⟩,
  ⟨3,1,0,0,1⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,0,3,0,2⟩,
  ⟨0,2,3,0,0⟩,
  ⟨2,0,0,0,3⟩,
  ⟨0,0,0,4,1⟩,
  ⟨0,0,1,4,0⟩,
  ⟨0,2,0,0,3⟩,
  ⟨1,1,0,0,3⟩,
  ⟨1,1,3,0,0⟩,
  ⟨2,0,3,0,0⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `17`. -/
def rivals5Zero17 : List Rival5 := [
  ⟨0,0,0,0,5⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `19`. -/
def rivals5Zero19 : List Rival5 := [
  ⟨0,0,0,0,5⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `21`. -/
def rivals5Zero21 : List Rival5 := [
  ⟨0,0,1,1,3⟩,
  ⟨0,0,1,3,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,0,3,1,1⟩,
  ⟨1,1,0,1,2⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,1,0,1,3⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,1,1,1,2⟩,
  ⟨0,1,1,2,1⟩,
  ⟨0,2,1,1,1⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,0,1,1,2⟩,
  ⟨0,1,1,3,0⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,3,1,0⟩,
  ⟨0,3,0,1,1⟩,
  ⟨0,3,1,0,1⟩,
  ⟨0,3,1,1,0⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `23`. -/
def rivals5Zero23 : List Rival5 := [
  ⟨0,0,0,0,5⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `25`. -/
def rivals5Zero25 : List Rival5 := [
  ⟨0,0,0,0,5⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,0,4,1⟩,
  ⟨1,1,1,0,2⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `27`. -/
def rivals5Zero27 : List Rival5 := [
  ⟨0,0,0,0,5⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,2,3⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,0,4,1⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,0,1,0,4⟩,
  ⟨0,0,1,1,3⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,0,2,0,3⟩,
  ⟨1,1,0,1,2⟩,
  ⟨1,1,0,2,1⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,1,3,1⟩,
  ⟨0,0,3,0,2⟩]

/-- Rivals covering every translated five-tuple of non-units modulo `29`. -/
def rivals5Zero29 : List Rival5 := [
  ⟨0,0,0,0,5⟩]


/-- The four-coordinate rival list attached to a modulus. -/
def rivals4 (N : ℕ) : List Rival4 :=
  if N = 9 then rivals4_9 else if N = 11 then rivals4_11 else if N = 13 then rivals4_13 else []

/-- The unit-normalized five-coordinate rival list attached to a modulus. -/
def rivals5Unit (N : ℕ) : List Rival5 :=
  if N = 17 then rivals5Unit17 else if N = 19 then rivals5Unit19 else if N = 21 then rivals5Unit21
  else if N = 23 then rivals5Unit23 else if N = 25 then rivals5Unit25 else if N = 27 then rivals5Unit27
  else if N = 29 then rivals5Unit29 else []

/-- The translated non-unit five-coordinate rival list attached to a modulus. -/
def rivals5Zero (N : ℕ) : List Rival5 :=
  if N = 17 then rivals5Zero17 else if N = 19 then rivals5Zero19 else if N = 21 then rivals5Zero21
  else if N = 23 then rivals5Zero23 else if N = 25 then rivals5Zero25 else if N = 27 then rivals5Zero27
  else if N = 29 then rivals5Zero29 else []

def covered3 (N a b : ℕ) : Bool := rivals3.any fun r ↦ r.valid && r.hits N a b
def covered4 (N a b c : ℕ) : Bool := (rivals4 N).any fun r ↦ r.valid && r.hits N a b c
def covered5Unit (N a b c : ℕ) : Bool := (rivals5Unit N).any fun r ↦ r.valid && r.hitsUnit N a b c
def covered5Zero (N a b c d : ℕ) : Bool := (rivals5Zero N).any fun r ↦ r.valid && r.hitsZero N a b c d

/-- Residues below `N` that are not coprime to `N`; `0` is included. -/
def nonunitList (N : ℕ) : List ℕ := (List.range N).filter fun x ↦ Nat.gcd x N ≠ 1

def allCovered3 (N : ℕ) : Bool :=
  (List.range N).all fun a ↦ (List.range N).all fun b ↦ covered3 N a b
def allCovered4 (N : ℕ) : Bool :=
  (List.range N).all fun a ↦ (List.range N).all fun b ↦ (List.range N).all fun c ↦ covered4 N a b c
/-- Only sorted triples `a ≤ b ≤ c` are checked; validity is permutation-invariant. -/
def allCovered5Unit (N : ℕ) : Bool :=
  (List.range N).all fun a ↦ (List.range N).all fun b ↦ (List.range N).all fun c ↦
    (!(decide (a ≤ b ∧ b ≤ c)) || covered5Unit N a b c)
def allCovered5Zero (N : ℕ) : Bool :=
  (nonunitList N).all fun a ↦ (nonunitList N).all fun b ↦ (nonunitList N).all fun c ↦
    (nonunitList N).all fun d ↦ covered5Zero N a b c d


/-! ### Kernel-checked coverage facts

Each statement is decided by evaluating the Boolean checker in Lean's kernel.
The lists were produced by a greedy search, but nothing outside the kernel
check is trusted. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every translated triple modulo `5` has a listed rival. -/
theorem certificate_three : allCovered3 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every translated four-tuple modulo `9` has a listed rival. -/
theorem certificate_four_nine : allCovered4 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every translated four-tuple modulo `11` has a listed rival. -/
theorem certificate_four_eleven : allCovered4 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every translated four-tuple modulo `13` has a listed rival. -/
theorem certificate_four_thirteen : allCovered4 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `17` has a listed rival. -/
theorem certificate_five_seventeen : allCovered5Unit 17 = true ∧ allCovered5Zero 17 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `19` has a listed rival. -/
theorem certificate_five_nineteen : allCovered5Unit 19 = true ∧ allCovered5Zero 19 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `21` has a listed rival. -/
theorem certificate_five_twenty_one : allCovered5Unit 21 = true ∧ allCovered5Zero 21 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `23` has a listed rival. -/
theorem certificate_five_twenty_three : allCovered5Unit 23 = true ∧ allCovered5Zero 23 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `25` has a listed rival. -/
theorem certificate_five_twenty_five : allCovered5Unit 25 = true ∧ allCovered5Zero 25 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `27` has a listed rival. -/
theorem certificate_five_twenty_seven : allCovered5Unit 27 = true ∧ allCovered5Zero 27 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every sorted unit-normalized five-tuple and every translated non-unit
five-tuple modulo `29` has a listed rival. -/
theorem certificate_five_twenty_nine : allCovered5Unit 29 = true ∧ allCovered5Zero 29 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ### Soundness: a covering rival is an actual multiplicity rival -/

/-- The three-coordinate checker produces a forbidden multiplicity vector. -/
theorem not_validTuple_three_of_covered (N a b : ℕ) (hc : covered3 N a b = true) :
    ¬ ValidTuple (![0,(a : ZMod N),(b : ZMod N)]) := by
  intro hg
  simp only [covered3, List.any_eq_true, Bool.and_eq_true] at hc
  obtain ⟨r, _, hvalid, hhit⟩ := hc
  simp only [Rival3.valid, decide_eq_true_eq] at hvalid
  simp only [Rival3.hits, decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i) = 3 := by
    simpa [Rival3.vector, Fin.sum_univ_three] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,(a : ZMod N),(b : ZMod N)]) i) =
      ∑ i, (![0,(a : ZMod N),(b : ZMod N)]) i := by
    have hh : ((r.k1*a+r.k2*b : ℕ) : ZMod N) = ((a+b : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival3.vector, Fin.sum_univ_three, nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival3.vector] using hone 0,
    by simpa [Rival3.vector] using hone 1,
    by simpa [Rival3.vector] using hone 2⟩

/-- The four-coordinate checker produces a forbidden multiplicity vector. -/
theorem not_validTuple_four_of_covered (N a b c : ℕ) (hc : covered4 N a b c = true) :
    ¬ ValidTuple (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) := by
  intro hg
  simp only [covered4, List.any_eq_true, Bool.and_eq_true] at hc
  obtain ⟨r, _, hvalid, hhit⟩ := hc
  simp only [Rival4.valid, decide_eq_true_eq] at hvalid
  simp only [Rival4.hits, decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i) = 4 := by
    simpa [Rival4.vector, Fin.sum_univ_four] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i) =
      ∑ i, (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i := by
    have hh : ((r.k1*a+r.k2*b+r.k3*c : ℕ) : ZMod N) = ((a+b+c : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival4.vector, Fin.sum_univ_four, nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival4.vector] using hone 0,
    by simpa [Rival4.vector] using hone 1,
    by simpa [Rival4.vector] using hone 2,
    by simpa [Rival4.vector] using hone 3⟩

/-- The unit-normalized five-coordinate checker produces a forbidden
multiplicity vector. -/
theorem not_validTuple_five_unit_of_covered (N a b c : ℕ)
    (hc : covered5Unit N a b c = true) :
    ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) := by
  intro hg
  simp only [covered5Unit, List.any_eq_true, Bool.and_eq_true] at hc
  obtain ⟨r, _, hvalid, hhit⟩ := hc
  simp only [Rival5.valid, decide_eq_true_eq] at hvalid
  simp only [Rival5.hitsUnit, decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i) = 5 := by
    simpa [Rival5.vector, Fin.sum_univ_five] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i) =
      ∑ i, (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c : ℕ) : ZMod N) = ((1+a+b+c : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival5.vector, Fin.sum_univ_five, nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival5.vector] using hone 0,
    by simpa [Rival5.vector] using hone 1,
    by simpa [Rival5.vector] using hone 2,
    by simpa [Rival5.vector] using hone 3,
    by simpa [Rival5.vector] using hone 4⟩

/-- The translated five-coordinate checker produces a forbidden multiplicity
vector. -/
theorem not_validTuple_five_zero_of_covered (N a b c d : ℕ)
    (hc : covered5Zero N a b c d = true) :
    ¬ ValidTuple (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) := by
  intro hg
  simp only [covered5Zero, List.any_eq_true, Bool.and_eq_true] at hc
  obtain ⟨r, _, hvalid, hhit⟩ := hc
  simp only [Rival5.valid, decide_eq_true_eq] at hvalid
  simp only [Rival5.hitsZero, decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i) = 5 := by
    simpa [Rival5.vector, Fin.sum_univ_five] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) i) =
      ∑ i, (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) i := by
    have hh : ((r.k1*a+r.k2*b+r.k3*c+r.k4*d : ℕ) : ZMod N) = ((a+b+c+d : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival5.vector, Fin.sum_univ_five, nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival5.vector] using hone 0,
    by simpa [Rival5.vector] using hone 1,
    by simpa [Rival5.vector] using hone 2,
    by simpa [Rival5.vector] using hone 3,
    by simpa [Rival5.vector] using hone 4⟩

/-! ### Permutation invariance and sorting of the unit-normalized form -/

/-- Validity is invariant under permuting the coordinates. -/
theorem validTuple_perm {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (σ : Equiv.Perm (Fin n)) :
    ValidTuple (fun i ↦ g (σ i)) := by
  intro k hsum hval
  have hsum' : (∑ i, k (σ.symm i)) = n := by
    rw [Equiv.sum_comp σ.symm k]
    exact hsum
  have hval' : (∑ i, k (σ.symm i) • g i) = ∑ i, g i := by
    have h1 : (∑ i, k (σ.symm i) • g i) = ∑ i, k i • g (σ i) := by
      rw [← Equiv.sum_comp σ (fun i ↦ k (σ.symm i) • g i)]
      simp only [Equiv.symm_apply_apply]
    have h2 : (∑ i, g i) = ∑ i, g (σ i) := (Equiv.sum_comp σ g).symm
    rw [h1, h2]
    exact hval
  intro i
  have hh := hg (fun i ↦ k (σ.symm i)) hsum' hval' (σ i)
  simpa only [Equiv.symm_apply_apply] using hh

/-- Swapping the third and fourth coordinates of a unit-normalized five-tuple. -/
theorem validTuple_swap23_five {N : ℕ} (x y z : ZMod N)
    (h : ValidTuple (![0, 1, x, y, z])) : ValidTuple (![0, 1, y, x, z]) := by
  have hh := validTuple_perm _ h (Equiv.swap (2 : Fin 5) 3)
  have heq : (fun i ↦ (![0, 1, x, y, z] : Fin 5 → ZMod N) (Equiv.swap (2 : Fin 5) 3 i)) =
      ![0, 1, y, x, z] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rwa [heq] at hh

/-- Swapping the fourth and fifth coordinates of a unit-normalized five-tuple. -/
theorem validTuple_swap34_five {N : ℕ} (x y z : ZMod N)
    (h : ValidTuple (![0, 1, x, y, z])) : ValidTuple (![0, 1, x, z, y]) := by
  have hh := validTuple_perm _ h (Equiv.swap (3 : Fin 5) 4)
  have heq : (fun i ↦ (![0, 1, x, y, z] : Fin 5 → ZMod N) (Equiv.swap (3 : Fin 5) 4 i)) =
      ![0, 1, x, z, y] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rwa [heq] at hh

/-- A valid unit-normalized five-tuple can be permuted so that the last three
representatives are sorted. -/
theorem exists_sorted_valid_five {N : ℕ} [NeZero N] (a b c : ZMod N)
    (h : ValidTuple (![0, 1, a, b, c])) :
    ∃ a' b' c' : ZMod N, ValidTuple (![0, 1, a', b', c']) ∧
      a'.val ≤ b'.val ∧ b'.val ≤ c'.val := by
  rcases le_total a.val b.val with hab | hab
  · rcases le_total b.val c.val with hbc | hbc
    · exact ⟨a, b, c, h, hab, hbc⟩
    · rcases le_total a.val c.val with hac | hac
      · exact ⟨a, c, b, validTuple_swap34_five _ _ _ h, hac, hbc⟩
      · exact ⟨c, a, b, validTuple_swap23_five _ _ _ (validTuple_swap34_five _ _ _ h), hac, hab⟩
  · rcases le_total a.val c.val with hac | hac
    · exact ⟨b, a, c, validTuple_swap23_five _ _ _ h, hab, hac⟩
    · rcases le_total b.val c.val with hbc | hbc
      · exact ⟨b, c, a, validTuple_swap34_five _ _ _ (validTuple_swap23_five _ _ _ h), hbc, hac⟩
      · exact ⟨c, b, a, validTuple_swap23_five _ _ _
          (validTuple_swap34_five _ _ _ (validTuple_swap23_five _ _ _ h)), hbc, hab⟩

/-! ### From a checked modulus to an arbitrary tuple -/

/-- A complete three-coordinate certificate excludes every tuple, after
translating the first coordinate to zero. -/
theorem not_validTuple_three_of_certificate {N : ℕ} [NeZero N]
    (h : allCovered3 N = true) (g : Fin 3 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  have hw := validTuple_sub_const g hg (g 0)
  have heq : (fun i ↦ g i - g 0) =
      ![0, (((g 1 - g 0).val : ℕ) : ZMod N), (((g 2 - g 0).val : ℕ) : ZMod N)] := by
    funext i
    fin_cases i <;> simp [ZMod.natCast_zmod_val]
  rw [heq] at hw
  simp only [allCovered3, List.all_eq_true] at h
  exact not_validTuple_three_of_covered N _ _
    (h _ (List.mem_range.mpr (ZMod.val_lt _)) _ (List.mem_range.mpr (ZMod.val_lt _))) hw

/-- A complete four-coordinate certificate excludes every tuple, after
translating the first coordinate to zero. -/
theorem not_validTuple_four_of_certificate {N : ℕ} [NeZero N]
    (h : allCovered4 N = true) (g : Fin 4 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  have hw := validTuple_sub_const g hg (g 0)
  have heq : (fun i ↦ g i - g 0) =
      ![0, (((g 1 - g 0).val : ℕ) : ZMod N), (((g 2 - g 0).val : ℕ) : ZMod N),
        (((g 3 - g 0).val : ℕ) : ZMod N)] := by
    funext i
    fin_cases i <;> simp [ZMod.natCast_zmod_val]
  rw [heq] at hw
  simp only [allCovered4, List.all_eq_true] at h
  exact not_validTuple_four_of_covered N _ _ _
    (h _ (List.mem_range.mpr (ZMod.val_lt _)) _ (List.mem_range.mpr (ZMod.val_lt _))
      _ (List.mem_range.mpr (ZMod.val_lt _))) hw

/-- A residue that is not a unit appears in the non-unit list. -/
theorem val_mem_nonunits {N : ℕ} [NeZero N] (x : ZMod N) (hx : ¬ IsUnit x) :
    x.val ∈ nonunitList N := by
  simp only [nonunitList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨ZMod.val_lt x, ?_⟩
  intro hgcd
  apply hx
  have hu : IsUnit ((x.val : ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime _ _).mpr hgcd
  simpa only [ZMod.natCast_zmod_val] using hu

/-- Complete five-coordinate certificates, in both normal forms, exclude every
tuple: a unit coordinate difference gives the form `(0,1,a,b,c)`, sorted by a
permutation, and otherwise translation gives `(0,a,b,c,d)` with non-unit
coordinates. -/
theorem not_validTuple_five_of_certificates {N : ℕ} [NeZero N] (h1 : N ≠ 1)
    (hu : allCovered5Unit N = true) (h0 : allCovered5Zero N = true)
    (g : Fin 5 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr h1
  by_cases hex : ∃ a b, IsUnit (g b - g a)
  · obtain ⟨a, b, hab⟩ := hex
    obtain ⟨w, hw, hw0, hw1⟩ := exists_normalized_valid_five_of_unit_difference g hg a b hab
    have heq : w = ![0, 1, w 2, w 3, w 4] := by
      funext i
      fin_cases i <;> simp [hw0, hw1]
    rw [heq] at hw
    obtain ⟨a', b', c', hw', hab', hbc'⟩ := exists_sorted_valid_five _ _ _ hw
    have heq' : (![0, 1, a', b', c'] : Fin 5 → ZMod N) =
        ![0, 1, ((a'.val : ℕ) : ZMod N), ((b'.val : ℕ) : ZMod N), ((c'.val : ℕ) : ZMod N)] := by
      funext i
      fin_cases i <;> simp [ZMod.natCast_zmod_val]
    rw [heq'] at hw'
    simp only [allCovered5Unit, List.all_eq_true] at hu
    have hh := hu _ (List.mem_range.mpr (ZMod.val_lt a')) _ (List.mem_range.mpr (ZMod.val_lt b'))
      _ (List.mem_range.mpr (ZMod.val_lt c'))
    have hcov : covered5Unit N a'.val b'.val c'.val = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hh
      rcases hh with h1 | h1
      · exact absurd ⟨hab', hbc'⟩ h1
      · exact h1
    exact not_validTuple_five_unit_of_covered N _ _ _ hcov hw'
  · push_neg at hex
    have hw := validTuple_sub_const g hg (g 0)
    have hmem : ∀ i, (g i - g 0).val ∈ nonunitList N := fun i ↦
      val_mem_nonunits _ (hex 0 i)
    have heq : (fun i ↦ g i - g 0) =
        ![0, (((g 1 - g 0).val : ℕ) : ZMod N), (((g 2 - g 0).val : ℕ) : ZMod N),
          (((g 3 - g 0).val : ℕ) : ZMod N), (((g 4 - g 0).val : ℕ) : ZMod N)] := by
      funext i
      fin_cases i <;> simp [ZMod.natCast_zmod_val]
    rw [heq] at hw
    simp only [allCovered5Zero, List.all_eq_true] at h0
    exact not_validTuple_five_zero_of_covered N _ _ _ _
      (h0 _ (hmem 1) _ (hmem 2) _ (hmem 3) _ (hmem 4)) hw

end MinModulus.OddSmallCertificate
