import Mathlib

namespace PNPEqualityPayloadCountingFinite

/-!
Finite cardinal shadow of the pair-separable MCSP equality-payload firewall.

The human theorem in `stevemoraco/RH` counts padded fan-in-two circuit
descriptions and proves that a diagonal-low/off-diagonal-high selector gadget
must inject every message into the low-circuit function class.

This file formalizes only the finite choice, injectivity, and description-card
spine. It does not define Boolean circuits, circuit semantics, restrictions,
MCSP, selector truth tables, crossing sequences, Turing machines, asymptotic
logarithms, or `P` versus `NP`.
-/

/-- An overcounted gate slot: one basis label and two wire labels. -/
def GateChoice (basis wires : ℕ) : Type :=
  Fin basis × Fin wires × Fin wires

/-- A padded `gates`-slot description together with one output-wire label. -/
def CircuitDescription (basis wires gates : ℕ) : Type :=
  (Fin gates → GateChoice basis wires) × Fin wires

/-- Exact cardinality of one overcounted gate slot. -/
theorem card_gateChoice (basis wires : ℕ) :
    Fintype.card (GateChoice basis wires) =
      basis * wires * wires := by
  simp [GateChoice, Nat.mul_assoc]

/-- Exact cardinality of the padded description space. -/
theorem card_circuitDescription (basis wires gates : ℕ) :
    Fintype.card (CircuitDescription basis wires gates) =
      (basis * wires * wires) ^ gates * wires := by
  simp [CircuitDescription, GateChoice, Nat.mul_assoc]

/-- If distinct messages encode distinct values and every encoded value has a
realizing description, one may choose realizing descriptions injectively. -/
theorem realized_injective_encoding_card_le
    {Message Value Description : Type*}
    [Fintype Message] [Fintype Description]
    (encode : Message → Value)
    (hencode : Function.Injective encode)
    (eval : Description → Value)
    (hrealized : ∀ x, ∃ d, eval d = encode x) :
    Fintype.card Message ≤ Fintype.card Description := by
  classical
  choose witness hwitness using hrealized
  have hwitness_injective : Function.Injective witness := by
    intro x y hxy
    apply hencode
    calc
      encode x = eval (witness x) := (hwitness x).symm
      _ = eval (witness y) := by rw [hxy]
      _ = encode y := hwitness y
  exact Fintype.card_le_of_injective witness hwitness_injective

/-- Exact diagonal acceptance and off-diagonal rejection force the component
encoder to be injective. -/
theorem diagonal_offDiagonal_forces_injective
    {Message Code Joined : Type*}
    (encode : Message → Code)
    (join : Code → Code → Joined)
    (low : Joined → Prop)
    (hdiagonal : ∀ x, low (join (encode x) (encode x)))
    (hoffDiagonal : ∀ {x y}, x ≠ y → ¬ low (join (encode x) (encode y))) :
    Function.Injective encode := by
  intro x y hsame
  by_contra hxy
  have hlow : low (join (encode x) (encode y)) := by
    simpa [hsame] using hdiagonal x
  exact (hoffDiagonal hxy) hlow

/-- An `m`-bit injective payload realized by padded descriptions obeys the
exact finite count `2^m ≤ (B W²)^s W`. -/
theorem binary_payload_le_description_count
    {m basis wires gates : ℕ}
    {Value : Type*}
    (encode : Fin (2 ^ m) → Value)
    (hencode : Function.Injective encode)
    (eval : CircuitDescription basis wires gates → Value)
    (hrealized : ∀ x, ∃ d, eval d = encode x) :
    2 ^ m ≤ (basis * wires * wires) ^ gates * wires := by
  have hcard := realized_injective_encoding_card_le
    encode hencode eval hrealized
  simpa [CircuitDescription, GateChoice, Nat.mul_assoc] using hcard

/-- Combined pair-separable form: diagonal/off-diagonal separation plus a
realizer for each component codeword yields the same payload ceiling. -/
theorem pair_separable_payload_le_description_count
    {m basis wires gates : ℕ}
    {Code Joined : Type*}
    (encode : Fin (2 ^ m) → Code)
    (join : Code → Code → Joined)
    (low : Joined → Prop)
    (hdiagonal : ∀ x, low (join (encode x) (encode x)))
    (hoffDiagonal : ∀ {x y}, x ≠ y → ¬ low (join (encode x) (encode y)))
    (eval : CircuitDescription basis wires gates → Code)
    (hrealized : ∀ x, ∃ d, eval d = encode x) :
    2 ^ m ≤ (basis * wires * wires) ^ gates * wires := by
  apply binary_payload_le_description_count encode
    (diagonal_offDiagonal_forces_injective
      encode join low hdiagonal hoffDiagonal)
    eval hrealized

/-- If the available description count is strictly below `2^m`, no realized
injective `m`-bit codebook exists. -/
theorem no_realized_payload_above_capacity
    {m basis wires gates : ℕ}
    {Value : Type*}
    (hcapacity :
      (basis * wires * wires) ^ gates * wires < 2 ^ m) :
    ¬ ∃ (encode : Fin (2 ^ m) → Value)
        (eval : CircuitDescription basis wires gates → Value),
        Function.Injective encode ∧
        (∀ x, ∃ d, eval d = encode x) := by
  rintro ⟨encode, eval, hencode, hrealized⟩
  have hbound := binary_payload_le_description_count
    encode hencode eval hrealized
  omega

/-- The same capacity contradiction rules out an exact pair-separable
realized codebook. -/
theorem no_pair_separable_payload_above_capacity
    {m basis wires gates : ℕ}
    {Code Joined : Type*}
    (hcapacity :
      (basis * wires * wires) ^ gates * wires < 2 ^ m) :
    ¬ ∃ (encode : Fin (2 ^ m) → Code)
        (join : Code → Code → Joined)
        (low : Joined → Prop)
        (eval : CircuitDescription basis wires gates → Code),
        (∀ x, low (join (encode x) (encode x))) ∧
        (∀ {x y}, x ≠ y → ¬ low (join (encode x) (encode y))) ∧
        (∀ x, ∃ d, eval d = encode x) := by
  rintro ⟨encode, join, low, eval, hdiagonal, hoffDiagonal, hrealized⟩
  have hbound := pair_separable_payload_le_description_count
    encode join low hdiagonal hoffDiagonal eval hrealized
  omega

#print axioms card_gateChoice
#print axioms card_circuitDescription
#print axioms realized_injective_encoding_card_le
#print axioms diagonal_offDiagonal_forces_injective
#print axioms binary_payload_le_description_count
#print axioms pair_separable_payload_le_description_count
#print axioms no_realized_payload_above_capacity
#print axioms no_pair_separable_payload_above_capacity

end PNPEqualityPayloadCountingFinite
