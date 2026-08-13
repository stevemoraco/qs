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

theorem conjugate_pair_rectangle (a b c : Vec3) :
    add (add a c) (add b (neg c)) = add a b := by
  rcases a with ⟨a1,a2,a3⟩
  rcases b with ⟨b1,b2,b3⟩
  rcases c with ⟨c1,c2,c3⟩
  simp [add,neg]

#print axioms carrier_geometry
#print axioms carrier_transversality
#print axioms heat_detuning
#print axioms first_leray_numerators
#print axioms quartic_return_nonzero
#print axioms quartic_return_targets_q2
#print axioms conjugate_pair_rectangle

end NSQuarticReturnFinite
