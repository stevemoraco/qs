import Mathlib

/-!
# Six-color packet quartic return: finite integer core

This file verifies only explicit integer-vector identities behind one
two-generation Fourier/Leray return. It does not formalize Fourier series,
Navier--Stokes, localization, a cascade, blowup, or any Clay statement.
-/

namespace NSQuarticReturnFinite

abbrev Vec3 := ℤ × ℤ × ℤ
@[simp] def add : Vec3 → Vec3 → Vec3
  | (x₁,x₂,x₃), (y₁,y₂,y₃) => (x₁+y₁,x₂+y₂,x₃+y₃)
@[simp] def neg : Vec3 → Vec3
  | (x,y,z) => (-x,-y,-z)
@[simp] def scale (c : ℤ) : Vec3 → Vec3
  | (x,y,z) => (c*x,c*y,c*z)
@[simp] def dot : Vec3 → Vec3 → ℤ
  | (x₁,x₂,x₃), (y₁,y₂,y₃) => x₁*y₁+x₂*y₂+x₃*y₃
@[simp] def normSq (x : Vec3) : ℤ := dot x x
@[simp] def lerayNum (k w : Vec3) : Vec3 :=
  add (scale (normSq k) w) (neg (scale (dot k w) k))
@[simp] def rawPair (k uk l ul : Vec3) : Vec3 :=
  add (scale (dot uk l) ul) (scale (dot ul k) uk)

/-! The following rational finite model expands exactly the coefficient of
the square-free monomial through all ordered inviscid Picard trees of depth
three.  It is only finite Fourier/Leray algebra. -/

abbrev RatVec3 := ℚ × ℚ × ℚ
@[simp] def qadd : RatVec3 → RatVec3 → RatVec3
  | (x₁,x₂,x₃), (y₁,y₂,y₃) => (x₁+y₁,x₂+y₂,x₃+y₃)
@[simp] def qscale (c : ℚ) : RatVec3 → RatVec3
  | (x,y,z) => (c*x,c*y,c*z)
@[simp] def qdot : RatVec3 → RatVec3 → ℚ
  | (x₁,x₂,x₃), (y₁,y₂,y₃) => x₁*y₁+x₂*y₂+x₃*y₃
@[simp] def qproj (k w : RatVec3) : RatVec3 :=
  qadd w (qscale (-(qdot k w / qdot k k)) k)
@[simp] def qsum : List RatVec3 → RatVec3
  | [] => (0,0,0)
  | x :: xs => qadd x (qsum xs)

structure QMode where
  k : RatVec3
  u : RatVec3

@[simp] def orderedQ (x y : QMode) : RatVec3 :=
  qproj (qadd x.k y.k) (qscale (qdot x.u y.k) y.u)

def pairCoeff (x y : QMode) : QMode where
  k := qadd x.k y.k
  u := qadd (orderedQ x y) (orderedQ y x)

def tripleCoeff (x y z : QMode) : QMode :=
  let xy := pairCoeff x y
  let xz := pairCoeff x z
  let yz := pairCoeff y z
  { k := qadd x.k (qadd y.k z.k)
    u := qscale (1/2) (qsum [
      orderedQ x yz, orderedQ yz x,
      orderedQ y xz, orderedQ xz y,
      orderedQ z xy, orderedQ xy z]) }

def quarticCoeff (a b c d : QMode) : QMode :=
  let bcd := tripleCoeff b c d
  let acd := tripleCoeff a c d
  let abd := tripleCoeff a b d
  let abc := tripleCoeff a b c
  let ab := pairCoeff a b
  let ac := pairCoeff a c
  let ad := pairCoeff a d
  let bc := pairCoeff b c
  let bd := pairCoeff b d
  let cd := pairCoeff c d
  { k := qadd a.k (qadd b.k (qadd c.k d.k))
    u := qscale (1/3) (qsum [
      orderedQ a bcd, orderedQ bcd a,
      orderedQ b acd, orderedQ acd b,
      orderedQ c abd, orderedQ abd c,
      orderedQ d abc, orderedQ abc d,
      orderedQ ab cd, orderedQ cd ab,
      orderedQ ac bd, orderedQ bd ac,
      orderedQ ad bc, orderedQ bc ad]) }

def modeA : QMode := ⟨(-27,-27,-18), (7129,7127,-21384)⟩
def modeB : QMode := ⟨(13,13,38), (-15049,-15047,10296)⟩
def modeC : QMode := ⟨(10,29,29), (-22968,3959,3961)⟩
def modeNegC : QMode := ⟨(-10,-29,-29), (-22968,3959,3961)⟩

theorem quartic_picard_frequency :
    (quarticCoeff modeA modeB modeC modeNegC).k = (-14,-14,20) := by
  norm_num [quarticCoeff, tripleCoeff, pairCoeff, modeA, modeB, modeC,
    modeNegC, orderedQ, qproj, qsum, qadd, qscale, qdot]

theorem quartic_picard_all_tree_coefficient :
    (quarticCoeff modeA modeB modeC modeNegC).u =
      (-29709287450407586552369503382070768 / 51741447392101,
       11805421958679668258158519494433904 / 155224342176303,
       -54125708274780163979264993456244880 / 155224342176303) := by
  norm_num [quarticCoeff, tripleCoeff, pairCoeff, modeA, modeB, modeC,
    modeNegC, orderedQ, qproj, qsum, qadd, qscale, qdot]

theorem quartic_picard_all_tree_nonzero :
    (quarticCoeff modeA modeB modeC modeNegC).u ≠ (0,0,0) := by
  rw [quartic_picard_all_tree_coefficient]
  norm_num

def q2 : Vec3 := (1,-1,0)
def ell2 : Vec3 := (-7,-7,10)
def a : Vec3 := (-27,-27,-18)
def b : Vec3 := (13,13,38)
def c : Vec3 := (10,29,29)
def s : Vec3 := (-17,2,11)
def r : Vec3 := (3,-16,9)
def lambda : Vec3 := (-14,-14,20)
def ua : Vec3 := (7129,7127,-21384)
def ub : Vec3 := (-15049,-15047,10296)
def uc : Vec3 := (-22968,3959,3961)

theorem carrier_geometry :
    add a c = s ∧ add b (neg c) = r ∧ add s r = lambda ∧
    lambda = scale 2 ell2 := by
  norm_num [a,b,c,s,r,lambda,ell2]

theorem carrier_transversality :
    dot a ua = 0 ∧ dot b ub = 0 ∧ dot c uc = 0 := by
  norm_num [a,b,c,ua,ub,uc]

theorem heat_detuning :
    normSq lambda - normSq s - normSq r = 32 := by
  norm_num [lambda,s,r]

theorem first_leray_numerators :
    lerayNum s (rawPair a ua c uc) =
      (-583483483944,1348048049112,-1146846847752) ∧
    lerayNum r (rawPair b ub (neg c) uc) =
      (-1620787455400,6706706712,552185519288) := by
  norm_num [lerayNum,rawPair,s,r,a,b,c,ua,ub,uc]

def Ns : Vec3 :=
  (-583483483944,1348048049112,-1146846847752)
def Nr : Vec3 :=
  (-1620787455400,6706706712,552185519288)

theorem quartic_return_nonzero :
    lerayNum lambda (rawPair s Ns r Nr) =
      scale (-4050316834212265142271787008) q2 := by
  norm_num [lerayNum,rawPair,lambda,s,r,Ns,Nr,q2]

theorem quartic_return_targets_q2 :
    lerayNum lambda (rawPair s Ns r Nr) ≠ (0,0,0) := by
  rw [quartic_return_nonzero]
  norm_num [scale,q2]

/-- Equal-shell geometry forces the exact quartic rectangle heat detuning. -/
theorem equal_shell_detuning_identity
    (ell h c : Vec3)
    (hc : normSq c = normSq ell + normSq h) :
    normSq (scale 2 ell) -
        normSq (add (add ell h) c) -
        normSq (add (add ell (neg h)) (neg c)) =
      -4 * dot h (add h c) := by
  rcases ell with ⟨e1, e2, e3⟩
  rcases h with ⟨h1, h2, h3⟩
  rcases c with ⟨c1, c2, c3⟩
  simp only [normSq, dot, scale, add, neg] at hc ⊢
  linear_combination -2 * hc

theorem conjugate_pair_rectangle (a b c : Vec3) :
    add (add a c) (add b (neg c)) = add a b := by
  rcases a with ⟨a1,a2,a3⟩
  rcases b with ⟨b1,b2,b3⟩
  rcases c with ⟨c1,c2,c3⟩
  simp only [add, neg, Prod.mk.injEq]
  constructor
  · ring
  constructor <;> ring

#print axioms quartic_picard_frequency
#print axioms quartic_picard_all_tree_coefficient
#print axioms quartic_picard_all_tree_nonzero
#print axioms carrier_geometry
#print axioms carrier_transversality
#print axioms heat_detuning
#print axioms first_leray_numerators
#print axioms quartic_return_nonzero
#print axioms quartic_return_targets_q2
#print axioms conjugate_pair_rectangle
#print axioms equal_shell_detuning_identity

end NSQuarticReturnFinite
