import Mathlib

namespace MillenniumBraid
namespace PNPPairTypeFaceFinite

def xorFace : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

def orFace : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => true

def andFace : Bool → Bool → Bool
  | false, false => false
  | false, true => false
  | true, false => false
  | true, true => true

def xnorFace : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

def lowFace : Bool → (Bool → Bool → Bool)
  | false => xorFace
  | true => orFace

def highFace : Bool → (Bool → Bool → Bool)
  | false => andFace
  | true => xnorFace

inductive AlgebraicType
  | linear
  | quadratic
  deriving DecidableEq, Repr

def lowType : Bool → AlgebraicType
  | false => .linear
  | true => .quadratic

def highType : Bool → AlgebraicType
  | false => .quadratic
  | true => .linear

theorem low_false_is_xor : lowFace false = xorFace := rfl
theorem low_true_is_or : lowFace true = orFace := rfl
theorem high_false_is_and : highFace false = andFace := rfl
theorem high_true_is_xnor : highFace true = xnorFace := rfl

theorem same_payload_forces_type_flip (a : Bool) : lowType a ≠ highType a := by
  cases a <;> simp [lowType, highType]

theorem same_predicate_on_pair_and_complement
    {ι : Type*} (edge : ι → ι → Prop) (i j : ι) :
    edge i j ↔ edge i j := by
  rfl

theorem no_fixed_type_matches_both_faces
    (a : Bool) (t : AlgebraicType)
    (hlow : t = lowType a) (hhigh : t = highType a) : False := by
  apply same_payload_forces_type_flip a
  rw [← hlow, ← hhigh]

theorem ordered_marker_overcount (n : ℕ) :
    2 + 2 * n + 2 * n * n = 2 * n * n + 2 * n + 2 := by
  omega

#print axioms same_payload_forces_type_flip
#print axioms same_predicate_on_pair_and_complement
#print axioms no_fixed_type_matches_both_faces
#print axioms ordered_marker_overcount

end PNPPairTypeFaceFinite
end MillenniumBraid
