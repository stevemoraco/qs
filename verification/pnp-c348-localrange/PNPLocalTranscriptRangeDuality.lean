import Mathlib

namespace Millennium.PNP.C348

abbrev Address (k : ℕ) := Fin k → Bool

structure Point (k : ℕ) where
  left : Fin k → Bool
  right : Fin k → Bool
  z : Bool
  deriving DecidableEq

/-- The private constant-zero fiber produced by the local restriction transcript. -/
def LocalFiber {k : ℕ} (b : Address k) (x : Point k) : Prop :=
  x.z = false ∧ ∀ i, x.left i = Bool.not (b i)

/-- The address-independent complementary flat on which every gadget accepts. -/
def CommonFlat {k : ℕ} (x : Point k) : Prop :=
  x.z = true ∧ ∀ i, x.right i = Bool.not (x.left i)

/-- Acceptance relation for
`z ∧ ∧ᵢ ((leftᵢ xor bᵢ) ∨ (rightᵢ xor bᵢ))`. -/
def Accepts {k : ℕ} (b : Address k) (x : Point k) : Prop :=
  x.z = true ∧ ∀ i, x.left i ≠ b i ∨ x.right i ≠ b i

def localPoint {k : ℕ} (b free : Address k) : Point k where
  left := fun i => Bool.not (b i)
  right := free
  z := false

def commonPoint {k : ℕ} (free : Address k) : Point k where
  left := free
  right := fun i => Bool.not (free i)
  z := true

theorem localPoint_mem {k : ℕ} (b free : Address k) :
    LocalFiber b (localPoint b free) := by
  simp [LocalFiber, localPoint]

theorem commonPoint_mem {k : ℕ} (free : Address k) :
    CommonFlat (commonPoint free) := by
  simp [CommonFlat, commonPoint]

theorem bool_complement_clause (a b : Bool) :
    a ≠ b ∨ Bool.not a ≠ b := by
  cases a <;> cases b <;> simp

/-- Every local transcript fiber is a rejection fiber for its gadget. -/
theorem localFiber_rejected {k : ℕ} {b : Address k} {x : Point k}
    (hx : LocalFiber b x) : ¬ Accepts b x := by
  intro hacc
  simpa [hx.1] using hacc.1

/-- Every gadget accepts every point of the same common complementary flat. -/
theorem commonFlat_accepted {k : ℕ} {x : Point k}
    (hx : CommonFlat x) : ∀ b : Address k, Accepts b x := by
  intro b
  refine ⟨hx.1, ?_⟩
  intro i
  have hr := hx.2 i
  cases hxi : x.left i <;> cases hbi : b i <;> simp_all

/-- Any choice of one point from every private local transcript fiber is injective
in the address. Hence its range contains all `2^k` addresses. -/
theorem local_selector_injective {k : ℕ}
    (choose : Address k → Point k)
    (hchoose : ∀ b, LocalFiber b (choose b)) :
    Function.Injective choose := by
  intro b c hbc
  funext i
  have hb := (hchoose b).2 i
  have hc := (hchoose c).2 i
  have hleft : (choose b).left i = (choose c).left i :=
    congrArg (fun x : Point k => x.left i) hbc
  have hnot : Bool.not (b i) = Bool.not (c i) :=
    hb.symm.trans (hleft.trans hc)
  cases hbi : b i <;> cases hci : c i <;> simp_all

theorem exact_address_card (k : ℕ) :
    Fintype.card (Address k) = 2 ^ k := by
  simp [Address]

/-- A target-negative common-flat point is a one-point false-positive core for
all addresses. -/
theorem one_point_common_core {k : ℕ}
    (target : Point k → Bool) (x : Point k)
    (hx : CommonFlat x) (hneg : target x = false) :
    ∀ b : Address k, Accepts b x ∧ target x = false := by
  intro b
  exact ⟨commonFlat_accepted hx b, hneg⟩

/-- Compact finite statement of the C348 local/global separation. -/
theorem local_range_vs_common_core {k : ℕ}
    (choose : Address k → Point k)
    (hchoose : ∀ b, LocalFiber b (choose b))
    (target : Point k → Bool) (x : Point k)
    (hx : CommonFlat x) (hneg : target x = false) :
    Function.Injective choose ∧
      Fintype.card (Address k) = 2 ^ k ∧
      (∀ b : Address k, Accepts b x ∧ target x = false) := by
  exact ⟨local_selector_injective choose hchoose,
    exact_address_card k, one_point_common_core target x hx hneg⟩

#print axioms localPoint_mem
#print axioms commonPoint_mem
#print axioms localFiber_rejected
#print axioms commonFlat_accepted
#print axioms local_selector_injective
#print axioms exact_address_card
#print axioms one_point_common_core
#print axioms local_range_vs_common_core

end Millennium.PNP.C348
