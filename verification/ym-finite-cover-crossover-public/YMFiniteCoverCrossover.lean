import Mathlib

/-!
# Yang--Mills finite-cover crossover: finite formal core

This file formalizes only the regulator-independent finite logic proposed in
`stevemoraco/RH#94`:

* componentwise propagation from one finite cover to the next;
* exact reachability through a finite chain of certified regions;
* the norm-ball enclosure criterion `e + L * r <= r'`;
* a two-coordinate counterexample showing that a projected certificate does
  not control an omitted tail coordinate.

It does **not** construct a Yang--Mills renormalization-group map, a polymer
norm, a reflection-positive blocking transformation, a continuum limit, or a
mass gap. Those remain external mathematical obligations.
-/

namespace YMFiniteCoverCrossover

open Set

/-- A recursion with the orientation used by a forward RG trajectory. -/
def forwardIterate {X : Type*} (F : X → X) : ℕ → X → X
  | 0 => id
  | n + 1 => fun x => F (forwardIterate F n x)

@[simp]
theorem forwardIterate_zero {X : Type*} (F : X → X) (x : X) :
    forwardIterate F 0 x = x := rfl

@[simp]
theorem forwardIterate_succ {X : Type*} (F : X → X) (n : ℕ) (x : X) :
    forwardIterate F (n + 1) x = F (forwardIterate F n x) := rfl

/-- If every member of one cover component maps into the union of the next
cover, then the union of all current components maps into that next union. -/
theorem componentwise_cover_step
    {X I J : Type*}
    (F : X → X) (B : I → Set X) (C : J → Set X)
    (hcomponent : ∀ i, MapsTo F (B i) (⋃ j, C j)) :
    MapsTo F (⋃ i, B i) (⋃ j, C j) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact hcomponent i hxi

/-- A sequence of exact one-step set inclusions gives exact finite-time
reachability. The theorem is finite in `N`; no compactness or limiting argument
is used. -/
theorem finite_chain_reachability
    {X : Type*}
    (F : X → X) (U : ℕ → Set X) (N : ℕ)
    (hstep : ∀ j, j < N → MapsTo F (U j) (U (j + 1))) :
    MapsTo (forwardIterate F N) (U 0) (U N) := by
  intro x hx
  induction N generalizing x with
  | zero =>
      simpa using hx
  | succ n ih =>
      have hx_n : forwardIterate F n x ∈ U n := by
        apply ih
        · intro j hj
          exact hstep j (Nat.lt_trans hj (Nat.lt_succ_self n))
        · exact hx
      have hx_next : F (forwardIterate F n x) ∈ U (n + 1) :=
        hstep n (Nat.lt_succ_self n) hx_n
      simpa using hx_next

/-- Adding an initial cover and a terminal basin inclusion turns the finite
chain into the exact certificate `F^N(K) subset G`. -/
theorem finite_chain_to_basin
    {X : Type*}
    (F : X → X) (U : ℕ → Set X) (N : ℕ) (K G : Set X)
    (hstart : K ⊆ U 0)
    (hstep : ∀ j, j < N → MapsTo F (U j) (U (j + 1)))
    (hterminal : U N ⊆ G) :
    MapsTo (forwardIterate F N) K G := by
  intro x hx
  exact hterminal (finite_chain_reachability F U N hstep (hstart hx))

/-- The advertised finite-cover certificate with one common finite index type.
Different cover cardinalities can be padded by empty regions. -/
theorem finite_cover_chain_to_basin
    {X : Type*} {m N : ℕ}
    (F : X → X) (B : ℕ → Fin m → Set X) (K G : Set X)
    (hstart : K ⊆ ⋃ i, B 0 i)
    (hstep : ∀ j, j < N → ∀ i, MapsTo F (B j i) (⋃ k, B (j + 1) k))
    (hterminal : (⋃ i, B N i) ⊆ G) :
    MapsTo (forwardIterate F N) K G := by
  apply finite_chain_to_basin F (fun j => ⋃ i, B j i) N K G hstart
  · intro j hj
    exact componentwise_cover_step F (B j) (B (j + 1)) (hstep j hj)
  · exact hterminal

section NormBall

variable {E : Type*} [NormedAddCommGroup E]

/-- A closed ball written in the exact norm-difference form used by the
validated-enclosure calculation. -/
def closedNormBall (c : E) (r : ℝ) : Set E :=
  {x | ‖x - c‖ ≤ r}

/-- Residual plus Lipschitz-radius control proves a one-step ball enclosure. -/
theorem ball_enclosure
    (F : E → E) {c c' : E} {r r' e L : ℝ}
    (hL : 0 ≤ L)
    (hresidual : ‖F c - c'‖ ≤ e)
    (hlocal : ∀ x ∈ closedNormBall c r,
      ‖F x - F c‖ ≤ L * ‖x - c‖)
    (hbudget : e + L * r ≤ r') :
    MapsTo F (closedNormBall c r) (closedNormBall c' r') := by
  intro x hx
  have hx' : ‖x - c‖ ≤ r := by
    simpa [closedNormBall] using hx
  have hscale : L * ‖x - c‖ ≤ L * r :=
    mul_le_mul_of_nonneg_left hx' hL
  have htriangle : ‖F x - c'‖ ≤ ‖F x - F c‖ + ‖F c - c'‖ := by
    calc
      ‖F x - c'‖ = ‖(F x - F c) + (F c - c')‖ := by
        congr 1
        abel
      _ ≤ ‖F x - F c‖ + ‖F c - c'‖ := norm_add_le _ _
  change ‖F x - c'‖ ≤ r'
  calc
    ‖F x - c'‖ ≤ ‖F x - F c‖ + ‖F c - c'‖ := htriangle
    _ ≤ L * ‖x - c‖ + e := add_le_add (hlocal x hx) hresidual
    _ ≤ L * r + e := add_le_add hscale (le_refl e)
    _ = e + L * r := by ring
    _ ≤ r' := hbudget

end NormBall


section CenteredCore

variable {A H : Type*} [NormedAddCommGroup H]

/-- A nonexpansive projection transports dense approximation to its fixed-point
subspace. In the Osterwalder--Schrader application, `j` is the reconstruction
map, `Q` is the orthogonal projection off the vacuum line, and `Q y = y`
expresses `y ∈ Ω⊥`.

The hypothesis is the epsilon formulation of density, so this finite theorem
does not depend on a separate topological totality API. -/
theorem contraction_transports_dense_approximation
    (j : A → H) (Q : H → H)
    (hdense : ∀ y : H, ∀ ε : ℝ, 0 < ε →
      ∃ a : A, ‖j a - y‖ < ε)
    (hnonexpansive : ∀ x y : H, ‖Q x - Q y‖ ≤ ‖x - y‖)
    {y : H} (hy : Q y = y) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖Q (j a) - y‖ < ε := by
  rcases hdense y ε hε with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  calc
    ‖Q (j a) - y‖ = ‖Q (j a) - Q y‖ := by rw [hy]
    _ ≤ ‖j a - y‖ := hnonexpansive (j a) y
    _ < ε := ha

end CenteredCore

section ProjectionFirewall

/-- A full two-coordinate flow whose retained coordinate looks perfectly
stable while the omitted coordinate doubles. -/
def fullFlow (z : ℚ × ℚ) : ℚ × ℚ :=
  (0, 2 * z.2)

/-- The deliberately lossy truncation retaining only the first coordinate. -/
def projectedCoordinate (z : ℚ × ℚ) : ℚ :=
  z.1

/-- The true endpoint basin depends on the omitted tail coordinate. -/
def fullBasin (z : ℚ × ℚ) : Prop :=
  |z.2| ≤ 1

/-- An initial state lying inside the full basin. -/
def tailWitness : ℚ × ℚ :=
  (0, 3 / 4)

/-- Every full state has the same apparently perfect projected endpoint. -/
theorem projected_flow_is_zero (z : ℚ × ℚ) :
    projectedCoordinate (fullFlow z) = 0 := rfl

/-- The chosen witness starts inside the true full-state basin. -/
theorem tailWitness_starts_in_basin :
    fullBasin tailWitness := by
  norm_num [fullBasin, tailWitness]

/-- One exact full step sends the omitted coordinate from `3/4` to `3/2`,
thereby leaving the true basin. -/
theorem tailWitness_exits_basin :
    ¬ fullBasin (fullFlow tailWitness) := by
  norm_num [fullBasin, fullFlow, tailWitness]

/-- Therefore a certificate stated only in the retained coordinate cannot imply
membership in the full endpoint basin. -/
theorem projected_certificate_not_sufficient :
    ¬ (∀ z : ℚ × ℚ,
      projectedCoordinate (fullFlow z) = 0 → fullBasin (fullFlow z)) := by
  intro h
  exact tailWitness_exits_basin (h tailWitness (projected_flow_is_zero tailWitness))

end ProjectionFirewall

#print axioms componentwise_cover_step
#print axioms finite_chain_reachability
#print axioms finite_chain_to_basin
#print axioms finite_cover_chain_to_basin
#print axioms ball_enclosure
#print axioms contraction_transports_dense_approximation
#print axioms projected_flow_is_zero
#print axioms tailWitness_starts_in_basin
#print axioms tailWitness_exits_basin
#print axioms projected_certificate_not_sufficient

end YMFiniteCoverCrossover
