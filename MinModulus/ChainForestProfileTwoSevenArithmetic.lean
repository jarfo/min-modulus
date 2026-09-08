import MinModulus.ChainForestProfileThreeSix

/-! Complete arithmetic for companion lengths two and seven. The full
signed primitive basis supplies individually affordable representations
for all 444 nonintegral phases; the two integral phases use positive
sparse-boundary certificates. Finite certificates use kernel reduction,
and the consumers produce actual full-length representations and group
rivals for every n >= 67. The genuine-forest consumer is separate. The
unrestricted conjecture remains open. -/

namespace MinModulus

structure TwoSevenBasisPlan where
  κ : ℤ
  ν : ℤ
  ta : ℕ
  tb : ℕ
  R : ℕ
  deriving DecidableEq

def TwoSevenBasisCertificate (P Q r q : ℤ) (p : TwoSevenBasisPlan) : Prop :=
  let A := 223-(p.tb : ℤ)*Q+p.κ*P
  let B := 223-33*(p.tb : ℤ)-64*p.κ
  let J := 223*p.ν-(p.tb : ℤ)*q+p.κ*r
  (p.ta : ℤ)=p.tb+2*p.κ ∧ (p.ta ≠ 3 ∨ p.tb ≠ 127) ∧
  (p.R : ℤ)=p.tb*(Q+256*q)-p.κ*(P+256*r)-223*p.ν*256 ∧
  0 < p.R ∧ 0 < (p.R*4294967296)%223 ∧
  gmin 31 ((p.R*4294967296)/223)+gmin 1 p.ta+gmin 6 p.tb ≤ 41 ∧
  -100000 < A-223+min J 0*64 ∧ -100000 ≤ B ∧
  A+max J 0*64 ≤ 100000 ∧ B ≤ 100000

instance (P Q r q : ℤ) (p : TwoSevenBasisPlan) :
    Decidable (TwoSevenBasisCertificate P Q r q p) := by
  unfold TwoSevenBasisCertificate
  infer_instance

private def twoSevenBasis0 : List TwoSevenBasisPlan := [
  ⟨-6,12,0,12,30⟩,
  ⟨-94,188,3,191,127⟩,
  ⟨-14,30,3,31,751⟩,
  ⟨-85,162,0,170,169⟩,
  ⟨-70,134,3,143,7⟩,
  ⟨-11,23,3,25,224⟩,
  ⟨-88,163,4,180,68⟩,
  ⟨-99,178,2,200,181⟩,
  ⟨-99,174,1,199,210⟩,
  ⟨-10,18,1,21,789⟩,
  ⟨-20,37,4,44,240⟩,
  ⟨-84,139,0,168,164⟩,
  ⟨-18,30,1,37,317⟩,
  ⟨-16,27,2,34,278⟩,
  ⟨-66,103,0,132,74⟩,
  ⟨-12,22,5,29,171⟩,
  ⟨-27,44,5,59,246⟩,
  ⟨-14,24,5,33,181⟩,
  ⟨-72,104,1,145,75⟩,
  ⟨-109,153,0,218,33⟩,
  ⟨-114,159,4,232,198⟩,
  ⟨-106,144,3,215,187⟩,
  ⟨-20,28,3,43,269⟩,
  ⟨-18,23,0,36,346⟩,
  ⟨-7,11,4,18,175⟩,
  ⟨-14,17,0,28,838⟩,
  ⟨-8,10,1,17,267⟩,
  ⟨-3,5,3,9,184⟩,
  ⟨-95,108,3,193,132⟩,
  ⟨-78,85,0,156,134⟩,
  ⟨-4,7,6,14,102⟩,
  ⟨-25,27,3,53,294⟩,
  ⟨-28,30,5,61,251⟩,
  ⟨-1,3,5,7,116⟩,
  ⟨-5,7,6,16,107⟩,
  ⟨-71,64,0,142,99⟩,
  ⟨-67,59,2,136,21⟩,
  ⟨2,0,5,1,101⟩,
  ⟨-12,10,1,25,287⟩,
  ⟨-58,45,0,116,34⟩,
  ⟨-5,4,1,11,252⟩,
  ⟨-9,8,6,24,127⟩,
  ⟨-7,6,5,19,146⟩,
  ⟨-75,49,1,151,90⟩,
  ⟨1,0,3,1,676⟩,
  ⟨-80,47,0,160,144⟩,
  ⟨-9,5,0,18,301⟩,
  ⟨-28,15,2,58,338⟩,
  ⟨-75,37,0,150,119⟩,
  ⟨-13,6,0,26,321⟩,
  ⟨-23,10,1,47,342⟩,
  ⟨-24,10,5,53,231⟩,
  ⟨-2,1,4,8,150⟩,
  ⟨-77,26,2,156,71⟩,
  ⟨-16,5,4,36,220⟩,
  ⟨-73,20,2,148,51⟩,
  ⟨-95,215,2,192,161⟩,
  ⟨-19,42,0,38,351⟩,
  ⟨-23,53,3,49,284⟩,
  ⟨-2,9,5,9,121⟩,
  ⟨-60,127,0,120,44⟩,
  ⟨-14,31,2,30,268⟩,
  ⟨-97,201,2,196,171⟩,
  ⟨-6,13,1,13,257⟩,
  ⟨-12,29,6,30,142⟩,
  ⟨0,5,6,6,82⟩,
  ⟨-15,33,5,35,186⟩,
  ⟨-64,123,2,130,6⟩,
  ⟨-19,37,2,40,293⟩,
  ⟨-6,11,0,12,286⟩,
  ⟨-81,149,4,166,33⟩,
  ⟨-97,174,3,197,142⟩,
  ⟨-12,23,3,27,229⟩,
  ⟨-24,41,0,48,376⟩,
  ⟨3,-1,6,0,67⟩,
  ⟨-14,25,3,31,239⟩,
  ⟨-87,143,4,178,63⟩,
  ⟨-17,30,5,39,196⟩,
  ⟨-91,143,3,185,112⟩,
  ⟨-25,38,0,50,381⟩,
  ⟨-17,27,3,37,254⟩,
  ⟨-94,137,0,188,214⟩,
  ⟨-115,164,0,230,63⟩,
  ⟨-24,35,3,51,289⟩,
  ⟨-73,101,3,149,22⟩,
  ⟨-98,131,1,197,205⟩,
  ⟨-10,13,0,20,306⟩,
  ⟨-3,6,5,11,126⟩,
  ⟨-2,5,6,10,92⟩,
  ⟨1,0,3,1,164⟩,
  ⟨-22,27,3,47,279⟩,
  ⟨-7,8,0,14,291⟩,
  ⟨-74,83,2,150,56⟩,
  ⟨-29,32,2,60,343⟩,
  ⟨-81,85,0,162,149⟩,
  ⟨-23,24,2,48,313⟩,
  ⟨-8,9,4,20,180⟩,
  ⟨-67,64,0,134,79⟩,
  ⟨-72,67,2,146,46⟩,
  ⟨1,0,4,2,135⟩,
  ⟨-98,85,3,199,147⟩,
  ⟨-102,85,2,206,196⟩,
  ⟨-10,9,6,26,132⟩,
  ⟨-30,23,0,60,406⟩,
  ⟨-1,1,2,4,203⟩,
  ⟨-65,46,2,132,11⟩,
  ⟨-7,5,3,17,204⟩,
  ⟨-92,59,0,184,204⟩,
  ⟨-8,5,2,18,238⟩,
  ⟨-88,51,2,178,126⟩,
  ⟨2,-1,4,0,642⟩,
  ⟨2,-1,4,0,130⟩,
  ⟨-64,159,0,128,64⟩,
  ⟨-20,51,2,42,298⟩,
  ⟨-69,169,2,140,31⟩,
  ⟨-21,53,3,45,274⟩,
  ⟨-26,65,4,56,270⟩,
  ⟨-113,263,0,226,53⟩,
  ⟨1,3,6,4,77⟩,
  ⟨-96,220,3,195,137⟩,
  ⟨1,2,5,3,106⟩,
  ⟨-76,169,2,154,66⟩,
  ⟨-88,191,0,176,184⟩,
  ⟨-3,8,2,8,213⟩,
  ⟨-65,137,0,130,69⟩,
  ⟨-6,17,6,18,112⟩,
  ⟨-1,5,4,6,145⟩,
  ⟨-74,149,0,148,114⟩,
  ⟨-56,111,0,112,24⟩,
  ⟨-76,151,4,156,8⟩,
  ⟨0,2,3,3,169⟩,
  ⟨-8,19,6,22,122⟩,
  ⟨-69,130,3,141,2⟩,
  ⟨-7,14,2,16,233⟩,
  ⟨-94,171,4,192,98⟩,
  ⟨-21,37,0,42,617⟩,
  ⟨-69,120,1,139,60⟩,
  ⟨-72,124,3,147,17⟩,
  ⟨-3,5,0,6,271⟩,
  ⟨0,1,2,2,710⟩,
  ⟨0,0,0,0,0⟩,
  ⟨-54,85,0,108,14⟩,
  ⟨-26,41,2,54,840⟩,
  ⟨-7,11,1,15,774⟩,
  ⟨-87,130,3,177,92⟩,
  ⟨-66,96,1,133,45⟩,
  ⟨-12,17,0,24,316⟩,
  ⟨-70,97,0,140,94⟩,
  ⟨-127,172,0,254,123⟩,
  ⟨-63,84,2,128,1⟩,
  ⟨-5,8,5,15,136⟩,
  ⟨-17,22,2,36,283⟩,
  ⟨-60,74,1,121,15⟩,
  ⟨-76,91,0,152,124⟩,
  ⟨-23,28,5,51,226⟩,
  ⟨-52,59,0,104,4⟩,
  ⟨-93,103,2,188,151⟩,
  ⟨-81,87,1,163,120⟩,
  ⟨-66,69,2,134,16⟩,
  ⟨-13,14,6,32,147⟩,
  ⟨-23,23,4,50,255⟩,
  ⟨-2,2,1,5,237⟩,
  ⟨-15,14,3,33,244⟩,
  ⟨-103,91,0,206,3⟩,
  ⟨-68,58,1,137,55⟩,
  ⟨-18,15,6,42,684⟩,
  ⟨-10,8,5,25,161⟩,
  ⟨0,0,1,1,227⟩,
  ⟨-7,25,6,20,117⟩,
  ⟨-82,221,0,164,154⟩,
  ⟨-11,35,6,28,137⟩,
  ⟨-68,179,0,136,84⟩,
  ⟨-5,13,0,10,281⟩,
  ⟨-6,19,4,16,170⟩,
  ⟨-75,193,3,153,32⟩,
  ⟨-9,26,4,22,185⟩,
  ⟨-61,151,0,122,49⟩,
  ⟨-71,176,3,145,12⟩,
  ⟨-14,37,4,32,210⟩,
  ⟨-74,177,1,149,85⟩,
  ⟨-82,195,3,167,67⟩,
  ⟨-22,51,0,44,366⟩,
  ⟨-75,173,2,152,61⟩,
  ⟨-100,227,2,202,186⟩,
  ⟨-107,238,0,214,23⟩,
  ⟨-17,40,4,38,225⟩,
  ⟨-64,139,1,129,35⟩,
  ⟨-90,193,2,182,136⟩,
  ⟨-5,13,4,14,165⟩,
  ⟨-71,148,2,144,41⟩,
  ⟨-28,57,0,56,396⟩,
  ⟨-1,2,0,2,261⟩,
  ⟨-4,9,2,10,218⟩,
  ⟨-21,44,6,48,187⟩,
  ⟨-79,153,4,162,23⟩,
  ⟨0,1,2,2,198⟩,
  ⟨-26,49,2,54,328⟩,
  ⟨-5,10,2,12,735⟩,
  ⟨-16,29,1,33,307⟩,
  ⟨-4,7,0,8,788⟩,
  ⟨-80,139,3,163,57⟩,
  ⟨-9,16,2,20,243⟩,
  ⟨-11,19,2,24,253⟩,
  ⟨-19,32,3,41,264⟩,
  ⟨-57,91,0,114,29⟩,
  ⟨-85,134,3,173,82⟩,
  ⟨-80,123,1,161,115⟩,
  ⟨-2,3,0,4,266⟩,
  ⟨-78,115,1,157,105⟩,
  ⟨0,1,4,4,140⟩,
  ⟨-10,15,4,24,702⟩,
  ⟨-80,111,4,164,28⟩,
  ⟨-18,25,4,40,230⟩,
  ⟨-9,12,1,19,272⟩,
  ⟨-108,139,3,219,197⟩,
  ⟨-4,5,0,8,276⟩,
  ⟨-4,5,1,9,247⟩,
  ⟨-69,82,0,138,89⟩,
  ⟨-121,140,0,242,93⟩,
  ⟨-8,9,0,16,296⟩,
  ⟨-19,21,4,42,235⟩,
  ⟨-16,17,0,32,336⟩,
  ⟨-63,65,1,127,30⟩,
  ⟨0,0,0,0,0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem twoSevenBasis0_checked : ∀ r : Fin 224,
    r.val < 223 → ((63 : ℤ)+256*r.val)%223 ≠ 0 →
    ∀ q : Fin 224, 0 < q.val → (4*r.val+q.val)%223=0 →
    TwoSevenBasisCertificate (63) (-29) r.val q.val
      (twoSevenBasis0.getD r.val ⟨0,0,0,0,0⟩) := by
  decide

private def twoSevenBasis1 : List TwoSevenBasisPlan := [
  ⟨0,0,0,0,0⟩,
  ⟨-59,125,9,127,28⟩,
  ⟨-79,154,1,159,272⟩,
  ⟨-19,40,4,42,105⟩,
  ⟨-87,164,1,175,264⟩,
  ⟨-3,11,6,12,55⟩,
  ⟨-69,125,0,138,187⟩,
  ⟨-50,89,0,100,718⟩,
  ⟨-33,62,5,71,186⟩,
  ⟨-46,79,0,92,210⟩,
  ⟨-86,145,0,172,170⟩,
  ⟨-18,33,4,40,106⟩,
  ⟨-11,21,4,26,113⟩,
  ⟨-13,23,3,29,16⟩,
  ⟨0,3,4,4,124⟩,
  ⟨-46,74,5,97,173⟩,
  ⟨-31,50,5,67,188⟩,
  ⟨-8,18,9,25,79⟩,
  ⟨-69,99,0,138,699⟩,
  ⟨-5,9,3,13,24⟩,
  ⟨-43,59,0,86,213⟩,
  ⟨-51,69,1,103,300⟩,
  ⟨-97,127,0,194,671⟩,
  ⟨-18,23,0,36,238⟩,
  ⟨-73,91,0,146,183⟩,
  ⟨-78,97,4,160,46⟩,
  ⟨-8,10,1,17,343⟩,
  ⟨-36,42,1,73,315⟩,
  ⟨-62,70,1,125,289⟩,
  ⟨-12,15,4,28,112⟩,
  ⟨-54,59,4,112,70⟩,
  ⟨-112,115,0,224,656⟩,
  ⟨-94,94,1,189,257⟩,
  ⟨-67,65,1,135,284⟩,
  ⟨-53,51,4,110,71⟩,
  ⟨-5,6,4,14,119⟩,
  ⟨-34,31,4,72,90⟩,
  ⟨-64,54,1,129,287⟩,
  ⟨-17,15,4,38,107⟩,
  ⟨-17,15,6,40,41⟩,
  ⟨-5,4,1,11,346⟩,
  ⟨-49,36,4,102,75⟩,
  ⟨-69,51,16,154,171⟩,
  ⟨-9,7,5,23,210⟩,
  ⟨-50,32,5,105,169⟩,
  ⟨-14,9,4,32,110⟩,
  ⟨-9,5,0,18,247⟩,
  ⟨-1,1,3,5,28⟩,
  ⟨-9,5,4,22,115⟩,
  ⟨-39,18,0,78,729⟩,
  ⟨-23,10,1,47,328⟩,
  ⟨-34,14,5,73,185⟩,
  ⟨-68,25,0,136,188⟩,
  ⟨-3,1,0,6,509⟩,
  ⟨-75,23,4,154,49⟩,
  ⟨-40,11,4,84,84⟩,
  ⟨-62,143,4,128,62⟩,
  ⟨-19,42,0,38,237⟩,
  ⟨-80,183,9,169,7⟩,
  ⟨-68,147,1,137,283⟩,
  ⟨-35,75,1,71,316⟩,
  ⟨-15,34,3,33,14⟩,
  ⟨-64,135,4,132,60⟩,
  ⟨-6,13,1,13,345⟩,
  ⟨-46,95,4,96,78⟩,
  ⟨-58,117,4,120,66⟩,
  ⟨-5,17,9,19,82⟩,
  ⟨-31,62,4,66,93⟩,
  ⟨-52,97,0,104,204⟩,
  ⟨-23,46,5,51,196⟩,
  ⟨-76,137,0,152,180⟩,
  ⟨-60,107,1,121,291⟩,
  ⟨-1,6,6,8,57⟩,
  ⟨-24,41,0,48,232⟩,
  ⟨-65,109,0,130,703⟩,
  ⟨3,-1,6,0,61⟩,
  ⟨-70,113,0,140,186⟩,
  ⟨-83,132,1,167,268⟩,
  ⟨-9,23,15,33,136⟩,
  ⟨-25,38,0,50,231⟩,
  ⟨6,-1,14,2,56⟩,
  ⟨-1,2,1,3,350⟩,
  ⟨-8,13,3,19,21⟩,
  ⟨-57,80,1,115,294⟩,
  ⟨-40,57,5,85,179⟩,
  ⟨-67,94,10,144,115⟩,
  ⟨-10,13,0,20,246⟩,
  ⟨-55,72,5,115,164⟩,
  ⟨-56,71,4,116,68⟩,
  ⟨-32,39,1,65,319⟩,
  ⟨-69,83,5,143,150⟩,
  ⟨-22,27,5,49,197⟩,
  ⟨-9,10,0,18,503⟩,
  ⟨0,1,3,3,29⟩,
  ⟨-15,17,4,34,109⟩,
  ⟨-6,7,3,15,23⟩,
  ⟨-83,83,4,170,41⟩,
  ⟨-1,2,4,6,123⟩,
  ⟨-39,37,4,82,85⟩,
  ⟨-92,83,4,188,32⟩,
  ⟨-65,57,5,135,154⟩,
  ⟨-88,73,0,176,168⟩,
  ⟨-109,87,0,218,147⟩,
  ⟨-30,23,0,60,226⟩,
  ⟨-28,21,3,59,1⟩,
  ⟨-32,23,4,68,92⟩,
  ⟨-58,39,0,116,710⟩,
  ⟨-26,17,4,56,98⟩,
  ⟨-21,13,3,45,8⟩,
  ⟨-102,59,0,204,154⟩,
  ⟨-7,4,6,20,51⟩,
  ⟨-64,33,0,128,192⟩,
  ⟨2,-1,4,0,126⟩,
  ⟨-53,130,0,106,203⟩,
  ⟨-46,120,9,101,41⟩,
  ⟨-70,172,5,145,149⟩,
  ⟨-92,217,0,184,164⟩,
  ⟨-7,19,3,17,22⟩,
  ⟨-98,225,0,196,158⟩,
  ⟨-61,139,1,123,290⟩,
  ⟨-65,146,1,131,286⟩,
  ⟨-5,11,0,10,507⟩,
  ⟨-22,51,4,48,102⟩,
  ⟨-36,77,0,72,220⟩,
  ⟨-30,64,1,61,321⟩,
  ⟨-105,218,0,210,151⟩,
  ⟨-90,187,4,184,34⟩,
  ⟨-1,2,0,2,767⟩,
  ⟨-13,30,6,32,45⟩,
  ⟨-81,158,0,162,175⟩,
  ⟨-25,52,6,56,33⟩,
  ⟨-107,202,0,214,149⟩,
  ⟨-36,70,5,77,183⟩,
  ⟨-22,42,3,47,7⟩,
  ⟨1,0,3,1,30⟩,
  ⟨-21,37,0,42,491⟩,
  ⟨-26,45,0,52,230⟩,
  ⟨-39,69,5,83,180⟩,
  ⟨-3,5,0,6,253⟩,
  ⟨-11,18,0,22,245⟩,
  ⟨-38,61,0,76,218⟩,
  ⟨-9,17,6,24,49⟩,
  ⟨-63,99,4,130,61⟩,
  ⟨-17,27,3,37,12⟩,
  ⟨-38,60,9,85,49⟩,
  ⟨-29,42,0,58,227⟩,
  ⟨-12,17,0,24,244⟩,
  ⟨-4,7,4,12,120⟩,
  ⟨-14,20,3,31,15⟩,
  ⟨-30,41,4,64,94⟩,
  ⟨-23,30,1,47,840⟩,
  ⟨-12,16,3,27,17⟩,
  ⟨-27,34,3,57,2⟩,
  ⟨-63,78,10,136,119⟩,
  ⟨-22,29,14,58,28⟩,
  ⟨-5,7,6,16,53⟩,
  ⟨-60,67,4,124,64⟩,
  ⟨-15,17,5,35,204⟩,
  ⟨-25,26,0,50,487⟩,
  ⟨-45,46,4,94,79⟩,
  ⟨-68,67,4,140,56⟩,
  ⟨-2,2,1,5,349⟩,
  ⟨-82,75,0,164,686⟩,
  ⟨-60,53,0,120,196⟩,
  ⟨-27,23,0,54,229⟩,
  ⟨-23,19,3,49,6⟩,
  ⟨-48,38,5,101,171⟩,
  ⟨0,0,1,1,351⟩,
  ⟨-106,289,0,212,150⟩,
  ⟨-13,36,1,27,338⟩,
  ⟨-47,129,4,98,77⟩,
  ⟨-2,9,4,8,122⟩,
  ⟨-5,13,0,10,251⟩,
  ⟨-72,185,0,144,184⟩,
  ⟨-82,209,1,165,269⟩,
  ⟨-82,209,4,168,42⟩,
  ⟨-34,85,1,69,317⟩,
  ⟨-38,97,5,81,181⟩,
  ⟨-17,41,0,34,751⟩,
  ⟨5,-4,10,0,187⟩,
  ⟨-23,61,9,55,64⟩,
  ⟨-22,51,0,44,234⟩,
  ⟨-42,99,4,88,82⟩,
  ⟨-11,32,10,32,171⟩,
  ⟨-58,129,0,116,198⟩,
  ⟨-83,182,0,166,173⟩,
  ⟨-31,67,0,62,225⟩,
  ⟨-100,213,0,200,156⟩,
  ⟨-71,149,0,142,185⟩,
  ⟨-38,81,4,80,86⟩,
  ⟨-84,171,0,168,684⟩,
  ⟨-1,2,0,2,255⟩,
  ⟨-25,51,3,53,4⟩,
  ⟨-17,33,0,34,495⟩,
  ⟨-79,153,4,162,45⟩,
  ⟨0,0,0,0,0⟩,
  ⟨-59,109,0,118,197⟩,
  ⟨-87,158,0,174,169⟩,
  ⟨-16,29,1,33,335⟩,
  ⟨-7,14,4,18,117⟩,
  ⟨-77,133,1,155,274⟩,
  ⟨-42,71,0,84,214⟩,
  ⟨-44,73,0,88,212⟩,
  ⟨-72,119,5,149,147⟩,
  ⟨-38,61,1,77,313⟩,
  ⟨-72,113,1,145,279⟩,
  ⟨-13,23,10,36,169⟩,
  ⟨-2,3,0,4,254⟩,
  ⟨-17,25,0,34,239⟩,
  ⟨-91,132,4,186,33⟩,
  ⟨-46,65,1,93,305⟩,
  ⟨-77,106,0,154,179⟩,
  ⟨-73,99,4,150,51⟩,
  ⟨-9,12,1,19,342⟩,
  ⟨-49,63,1,99,302⟩,
  ⟨-4,5,0,8,252⟩,
  ⟨-1,3,14,16,49⟩,
  ⟨-3,4,4,10,121⟩,
  ⟨-51,59,0,102,205⟩,
  ⟨-8,9,0,16,248⟩,
  ⟨-85,93,0,170,171⟩,
  ⟨-16,17,0,32,240⟩,
  ⟨-32,33,0,64,224⟩,
  ⟨-71,71,2,144,119⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem twoSevenBasis1_checked : ∀ r : Fin 224,
    0 < r.val → ((-191 : ℤ)+256*r.val)%223 ≠ 0 →
    ∀ q : Fin 224, q.val < 223 → (4*r.val+q.val)%223=0 →
    TwoSevenBasisCertificate (-191) (95) r.val q.val
      (twoSevenBasis1.getD r.val ⟨0,0,0,0,0⟩) := by
  decide

/-- Every nonintegral two-seven phase has a checked individual signed
basis rival, including phases not covered by complementary top shifts. -/
theorem exists_two_seven_nonintegral_basis_certificate
    {r q : ℕ} {P Q : ℤ}
    (hr : (P=63 ∧ Q = -29 ∧ r < 223 ∧ 1 ≤ q ∧ q ≤ 223) ∨
      (P = -191 ∧ Q=95 ∧ 1 ≤ r ∧ r ≤ 223 ∧ q < 223))
    (hlink : (4*r+q)%223=0) (hnon : (P+256*r)%223 ≠ 0) :
    ∃ p, TwoSevenBasisCertificate P Q r q p := by
  rcases hr with ⟨rfl,rfl,hr,hqlo,hqhi⟩ | ⟨rfl,rfl,hrlo,hrhi,hq⟩
  · exact ⟨_,twoSevenBasis0_checked ⟨r,by omega⟩ (by omega)
      (by simpa using hnon) ⟨q,by omega⟩ (by change 0 < q; omega) hlink⟩
  · exact ⟨_,twoSevenBasis1_checked ⟨r,by omega⟩ (by change 0 < r; omega)
      (by simpa using hnon) ⟨q,by omega⟩ (by omega) hlink⟩

/-- A checked individual basis certificate gives an actual group rival
and an affordable full-length representation for every n >= 67. -/
theorem exists_two_seven_rival_of_basis_certificate
    {n N L M E H c V α z : ℕ} {P Q r q : ℤ}
    (hn : 67 ≤ n) (hL : L+9=n)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=256*2^L) (hE : E ≤ 64*H)
    (hphase : 223*(α : ℤ)=P*((2 : ℤ)^L-H)+64*c+r*M)
    (hzphase : 223*(z : ℤ)=Q*(2 : ℤ)^L+(223-Q)*H+190*c-223+q*M)
    (x a b : ZMod N) (hα : α • x=2 • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0)
    (p : TwoSevenBasisPlan) (hp : TwoSevenBasisCertificate P Q r q p) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 3 ∨ tb ≠ 127) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 1 ta+gmin 6 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  rcases hp with ⟨hta,hne,hR,hRpos,hrem,hcost,hA0,hB0,hA1,hB1⟩
  let Z : ℤ := (p.tb : ℤ)*z-p.κ*α+(1-(p.tb : ℤ))*V-p.ν*M
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hMZ : (M : ℤ)+E=256*(2 : ℤ)^L := by exact_mod_cast hM
  have herr : 223*Z-(p.R : ℤ)*2^L =
      (223-(p.tb : ℤ)*Q+p.κ*P)*H+(223-33*(p.tb : ℤ)-64*p.κ)*c-223+
      (223*p.ν-(p.tb : ℤ)*q+p.κ*r)*E := by
    dsimp [Z]
    linear_combination (p.tb : ℤ)*hzphase-p.κ*hphase-
      223*(1-(p.tb : ℤ))*hbaseZ-
      (223*p.ν-(p.tb : ℤ)*q+p.κ*r)*hMZ-hR*(2 : ℤ)^L
  have hw := signed_rival_linear_error_window (S:=223) (W:=64)
    (A:=223-(p.tb : ℤ)*Q+p.κ*P) (B:=223-33*(p.tb : ℤ)-64*p.κ)
    (J:=223*p.ν-(p.tb : ℤ)*q+p.κ*r) (C:=100000)
    hH hnc hE (by decide) (by norm_num) hA0 hB0 hA1 hB1
  have hwindow : (p.R : ℤ)*2^L < 223*Z+(100000*n : ℕ) ∧
      223*Z < (p.R : ℤ)*2^L+(100000*n : ℕ) := by
    push_cast at hw ⊢
    constructor <;> linarith only [herr,hw.1,hw.2]
  have hsmall : 100000*n < 2^(L-32) := by
    rw [show L-32=n-41 by omega]
    exact hundred_thousand_length_lt_two_pow_sub_forty_one hn
  have hlarge : n ≤ 2^(L-32) := by omega
  have hbudget : gmin 31 ((p.R*2^32)/223)+(L-32)+(gmin 1 p.ta+gmin 6 p.tb) ≤ n := by
    change gmin 31 ((p.R*4294967296)/223)+(L-32)+(gmin 1 p.ta+gmin 6 p.tb) ≤ n
    omega
  obtain ⟨hZ,hnZ,_,u,hu,hcu⟩ := exists_rep_of_int_binary_prefix_fraction
    (n:=n) (L:=L) (w:=31) (e:=L-32) Z (by omega)
    (by decide : 0 < 223) (by norm_num) hRpos hrem hbudget hsmall hlarge hwindow
  refine ⟨Z.toNat,p.ta,p.tb,hnZ,hne,u,hu,by omega,?_⟩
  exact signed_axis_basis_rival_eq x a b p.κ p.ν hta hz hα hmx hZ

structure TwoSevenIntegralPlan where
  κ : ℤ
  ν : ℤ
  ta : ℕ
  tb : ℕ
  R : ℕ
  b : ℕ
  f : ℕ
  deriving DecidableEq

def TwoSevenIntegralCertificate (D F : ℕ) (P Q r q : ℤ)
    (p : TwoSevenIntegralPlan) : Prop :=
  let S : ℤ := 223*F
  let W : ℤ := 256*F
  let A := S-F*p.tb*Q+p.κ*P
  let B := S-33*F*p.tb-64*p.κ
  let J := S*p.ν-F*p.tb*q+p.κ*r
  (p.ta : ℤ)=p.tb+D*p.κ ∧ (p.ta ≠ 3 ∨ p.tb ≠ 127) ∧
  (p.R : ℤ)=F*p.tb*(Q+W*q)-p.κ*(P+W*r)-S*p.ν*W ∧
  (223*F)*p.b=2^p.f*p.R ∧ 1 ≤ p.b ∧ 1 ≤ p.f ∧ p.f ≤ 2 ∧
  gmin (p.f-1) p.b+gmin 1 p.ta+gmin 6 p.tb ≤ 40 ∧
  0 ≤ A+min J 0*(64*F) ∧ 0 ≤ B ∧ 0 < A+min J 0*(64*F)+B ∧
  A+max J 0*(64*F) ≤ 2000*(223*F) ∧ B ≤ 2000*(223*F)

instance (D F : ℕ) (P Q r q : ℤ) (p : TwoSevenIntegralPlan) :
    Decidable (TwoSevenIntegralCertificate D F P Q r q p) := by
  unfold TwoSevenIntegralCertificate
  infer_instance

private def twoSevenIntegral0 : TwoSevenIntegralPlan := ⟨-5,9,2,12,223,2,1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem twoSevenIntegral0_checked : ∀ r : Fin 224,
    r.val < 223 → ((63 : ℤ)+256*r.val)%223=0 →
    ∀ q : Fin 224, 0 < q.val → (4*r.val+q.val)%223=0 →
    TwoSevenIntegralCertificate 2 1 (63) (-29) r.val q.val twoSevenIntegral0 := by
  decide

private def twoSevenIntegral1 : TwoSevenIntegralPlan := ⟨-33,62,0,66,223,2,1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem twoSevenIntegral1_checked : ∀ r : Fin 224,
    0 < r.val → ((-191 : ℤ)+256*r.val)%223=0 →
    ∀ q : Fin 224, q.val < 223 → (4*r.val+q.val)%223=0 →
    TwoSevenIntegralCertificate 2 1 (-191) (95) r.val q.val twoSevenIntegral1 := by
  decide

/-- The two integral two-seven phases have positive sparse-boundary
certificates, with their exact second phases determined by the link. -/
theorem exists_two_seven_integral_certificate
    {r q : ℕ} {P Q : ℤ}
    (hr : (P=63 ∧ Q = -29 ∧ r < 223 ∧ 1 ≤ q ∧ q ≤ 223) ∨
      (P = -191 ∧ Q=95 ∧ 1 ≤ r ∧ r ≤ 223 ∧ q < 223))
    (hlink : (4*r+q)%223=0) (hint : (P+256*r)%223=0) :
    ∃ p, TwoSevenIntegralCertificate 2 1 P Q r q p := by
  rcases hr with ⟨rfl,rfl,hr,hqlo,hqhi⟩ | ⟨rfl,rfl,hrlo,hrhi,hq⟩
  · exact ⟨_,twoSevenIntegral0_checked ⟨r,by omega⟩ (by omega)
      (by simpa using hint) ⟨q,by omega⟩ (by change 0 < q; omega) hlink⟩
  · exact ⟨_,twoSevenIntegral1_checked ⟨r,by omega⟩ (by change 0 < r; omega)
      (by simpa using hint) ⟨q,by omega⟩ (by omega) hlink⟩

/-- A checked integral plan gives an actual sparse rival uniformly in
length, without requiring the period coprime to the primitive denominator. -/
theorem exists_two_seven_rival_of_integral_certificate
    {n N L D F M E H c V α z : ℕ} {P Q r q : ℤ}
    (hn : 67 ≤ n) (hL : L+9=n) (hF : 1 ≤ F)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=(256*F)*2^L) (hE : E ≤ (64*F)*H)
    (hphase : (223*F : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+64*c+r*M)
    (hzphase : 223*(z : ℤ)=Q*(2 : ℤ)^L+(223-Q)*H+190*c-223+q*M)
    (x a b : ZMod N) (hα : α • x=D • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0)
    (p : TwoSevenIntegralPlan) (hp : TwoSevenIntegralCertificate D F P Q r q p) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 3 ∨ tb ≠ 127) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 1 ta+gmin 6 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  rcases hp with ⟨hta,hne,hR,hb,hbp,hflo,hfhi,hcost,hA0,hB0,hpos,hA1,hB1⟩
  let Z : ℤ := (p.tb : ℤ)*z-p.κ*α+(1-(p.tb : ℤ))*V-p.ν*M
  have hS : 0 < 223*F := by omega
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hMZ : (M : ℤ)+E=(256*F : ℕ)*(2 : ℤ)^L := by exact_mod_cast hM
  have herr : (223*F : ℕ)*Z-(p.R : ℤ)*2^L =
      ((223*F : ℕ)-(F : ℤ)*p.tb*Q+p.κ*P)*H+
      ((223*F : ℕ)-33*(F : ℤ)*p.tb-64*p.κ)*c-(223*F : ℕ)+
      ((223*F : ℕ)*p.ν-(F : ℤ)*p.tb*q+p.κ*r)*E := by
    dsimp [Z]
    push_cast at hphase hMZ ⊢
    linear_combination (F : ℤ)*p.tb*hzphase-p.κ*hphase-
      (223*(F : ℤ))*(1-(p.tb : ℤ))*hbaseZ-
      (223*(F : ℤ)*p.ν-(F : ℤ)*p.tb*q+p.κ*r)*hMZ-hR*(2 : ℤ)^L
  have he : L-p.f+(p.f-1+1)=L := by omega
  have hpow : 2^L=2^p.f*2^(L-p.f) := by
    rw [← pow_add,show p.f+(L-p.f)=L by omega]
  have hboundaryeq : (223*F : ℕ)*(p.b*2^(L-p.f) : ℕ)=(p.R : ℤ)*2^L := by
    have hh : (223*F)*(p.b*2^(L-p.f))=p.R*2^L := by
      rw [← Nat.mul_assoc,hb,hpow]
      ring
    exact_mod_cast hh
  have htail := two_thousand_length_lt_two_pow_sub_forty hn
  have hboundary : n ≤ p.b*2^(L-p.f) := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show n-40 ≤ L-p.f by omega)
    have hh' := Nat.mul_le_mul_right (2^(L-p.f)) hbp
    omega
  have hsmall : (2000*(223*F))*n ≤ (223*F)*2^(n-40) := by
    have hh := Nat.mul_le_mul_left (223*F) (le_of_lt htail)
    nlinarith only [hh]
  have hcost' : gmin (p.f-1) p.b+(n-40)+(gmin 1 p.ta+gmin 6 p.tb) ≤ n := by omega
  have herr' : (223*F : ℕ)*(Z-(p.b*2^(L-p.f) : ℕ))=
      ((223*F : ℕ)-(F : ℤ)*p.tb*Q+p.κ*P)*H+
      ((223*F : ℕ)-33*(F : ℤ)*p.tb-64*p.κ)*c-(223*F : ℕ)+
      ((223*F : ℕ)*p.ν-(F : ℤ)*p.tb*q+p.κ*r)*E := by
    linear_combination herr-hboundaryeq
  obtain ⟨hZ,hnZ,u,hu,hcu⟩ := exists_rep_of_integral_rival_error_certificate
    (L:=L) (w:=p.f-1) (e:=L-p.f) (k:=n-40) Z he (by omega) hS hboundary hcost' hsmall
    hH hc hnc hE
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hA0)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hB0)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hpos)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hA1)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hB1) herr'
  refine ⟨Z.toNat,p.ta,p.tb,hnZ,hne,u,hu,by omega,?_⟩
  exact signed_axis_basis_rival_eq x a b p.κ p.ν hta hz hα hmx hZ


/-- Every bounded two-seven primitive phase gives an affordable actual
group rival, covering all 446 phases at every length at least 67. -/
theorem exists_two_seven_primitive_rival
    {n N L M E H c V α z r q : ℕ} {P Q : ℤ}
    (hn : 67 ≤ n) (hL : L+9=n)
    (hr : (P=63 ∧ Q = -29 ∧ r < 223 ∧ 1 ≤ q ∧ q ≤ 223) ∨
      (P = -191 ∧ Q=95 ∧ 1 ≤ r ∧ r ≤ 223 ∧ q < 223))
    (hlink : (4*r+q)%223=0)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=256*2^L) (hE : E ≤ 64*H)
    (hphase : 223*(α : ℤ)=P*((2 : ℤ)^L-H)+64*c+(r : ℤ)*M)
    (hzphase : 223*(z : ℤ)=Q*(2 : ℤ)^L+(223-Q)*H+190*c-223+(q : ℤ)*M)
    (x a b : ZMod N) (hα : α • x=2 • a)
    (hz : z • x+a+b=V • x) (hmx : M • x=0) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 3 ∨ tb ≠ 127) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 1 ta+gmin 6 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  by_cases hint : (P+256*r)%223=0
  · obtain ⟨p,hp⟩ := exists_two_seven_integral_certificate hr hlink hint
    exact exists_two_seven_rival_of_integral_certificate (D:=2) (F:=1) hn hL (by decide)
      hH hc hnc hbase hM hE (by simpa using hphase) hzphase x a b hα hz hmx p hp
  · obtain ⟨p,hp⟩ := exists_two_seven_nonintegral_basis_certificate hr hlink hint
    exact exists_two_seven_rival_of_basis_certificate hn hL hH hnc hbase
      hM hE hphase hzphase x a b hα hz hmx p hp

end MinModulus
