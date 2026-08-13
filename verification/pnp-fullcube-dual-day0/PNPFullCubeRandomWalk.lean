import Mathlib

namespace PNPFullCubeRandomWalk

variable {α : Type*} [DecidableEq α]

/-- Parity of the number of occurrences of `x`, computed by toggling a bit. -/
def parity (x : α) : List α → Bool
  | [] => false
  | y :: ys => if y = x then !(parity x ys) else parity x ys

/-- The full parity endpoint of a word. -/
def endpoint (xs : List α) : α → Bool := fun x => parity x xs

/-- Swap `u` and `v` at their first occurrence, leaving the word unchanged
when neither symbol occurs. -/
def swapFirst (u v : α) : List α → List α
  | [] => []
  | x :: xs =>
      if x = u then v :: xs
      else if x = v then u :: xs
      else x :: swapFirst u v xs

@[simp] theorem swapFirst_length (u v : α) :
    ∀ xs : List α, (swapFirst u v xs).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxu : x = u
      · simp [swapFirst, hxu]
      · by_cases hxv : x = v
        · subst x
          simp [swapFirst, hxu]
        · simp [swapFirst, hxu, hxv, ih]

/-- The first-occurrence swap is an involution when the symbols differ. -/
theorem swapFirst_involutive {u v : α} (huv : u ≠ v) :
    Function.Involutive (swapFirst u v) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxu : x = u
      · subst x
        simp [swapFirst, huv.symm]
      · by_cases hxv : x = v
        · subst x
          simp [swapFirst, huv.symm]
        · simp [swapFirst, hxu, hxv, ih]

/-- Hence the first-occurrence swap is injective. -/
theorem swapFirst_injective {u v : α} (huv : u ≠ v) :
    Function.Injective (swapFirst u v) :=
  (swapFirst_involutive huv).injective

/-- If a symbol has odd parity, it occurs in the word. -/
theorem parity_true_mem {x : α} :
    ∀ {xs : List α}, parity x xs = true → x ∈ xs := by
  intro xs h
  induction xs with
  | nil => simp [parity] at h
  | cons y ys ih =>
      by_cases hyx : y = x
      · simp [hyx]
      · have htail : parity x ys = true := by
          simpa [parity, hyx] using h
        exact List.mem_cons_of_mem y (ih htail)

/-- Swapping the first `u`/`v` occurrence toggles the `u` parity. -/
theorem parity_swapFirst_left {u v : α} (huv : u ≠ v) :
    ∀ {xs : List α},
      (u ∈ xs ∨ v ∈ xs) →
      parity u (swapFirst u v xs) = !(parity u xs) := by
  intro xs hex
  induction xs with
  | nil => simp at hex
  | cons x xs ih =>
      by_cases hxu : x = u
      · subst x
        simp [swapFirst, parity, huv.symm]
      · by_cases hxv : x = v
        · subst x
          simp [swapFirst, parity, huv.symm]
        · have hux : u ≠ x := Ne.symm hxu
          have hvx : v ≠ x := Ne.symm hxv
          have htail : u ∈ xs ∨ v ∈ xs := by
            simpa [hxu, hux, hxv, hvx] using hex
          simp [swapFirst, parity, hxu, hxv, ih htail]

/-- Swapping the first `u`/`v` occurrence toggles the `v` parity. -/
theorem parity_swapFirst_right {u v : α} (huv : u ≠ v) :
    ∀ {xs : List α},
      (u ∈ xs ∨ v ∈ xs) →
      parity v (swapFirst u v xs) = !(parity v xs) := by
  intro xs hex
  induction xs with
  | nil => simp at hex
  | cons x xs ih =>
      by_cases hxu : x = u
      · subst x
        simp [swapFirst, parity, huv]
      · by_cases hxv : x = v
        · subst x
          simp [swapFirst, parity, huv, huv.symm]
        · have hux : u ≠ x := Ne.symm hxu
          have hvx : v ≠ x := Ne.symm hxv
          have htail : u ∈ xs ∨ v ∈ xs := by
            simpa [hxu, hux, hxv, hvx] using hex
          simp [swapFirst, parity, hxu, hxv, ih htail]

/-- Every other parity coordinate is unchanged. -/
theorem parity_swapFirst_other {u v x : α}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    ∀ xs : List α,
      parity x (swapFirst u v xs) = parity x xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases hyu : y = u
      · subst y
        simp [swapFirst, parity, hxu.symm, hxv.symm]
      · by_cases hyv : y = v
        · subst y
          simp [swapFirst, parity, hyu, hxu.symm, hxv.symm]
        · simp [swapFirst, parity, hyu, hyv, ih]

/-- Toggle exactly the two selected endpoint coordinates. -/
def togglePair (u v : α) (p : α → Bool) : α → Bool := fun x =>
  if x = u ∨ x = v then !(p x) else p x

/-- Exact endpoint transformation under the first-occurrence swap. -/
theorem endpoint_swapFirst {u v : α} (huv : u ≠ v)
    {xs : List α} (hex : u ∈ xs ∨ v ∈ xs) :
    endpoint (swapFirst u v xs) = togglePair u v (endpoint xs) := by
  funext x
  by_cases hxu : x = u
  · subst x
    simp [endpoint, togglePair, parity_swapFirst_left huv hex]
  · by_cases hxv : x = v
    · subst x
      simp [endpoint, togglePair, hxu, parity_swapFirst_right huv hex]
    · simp [endpoint, togglePair, hxu, hxv,
        parity_swapFirst_other hxu hxv xs]

/-- Fixed-length words with a prescribed parity endpoint. -/
def EndpointFiber (k : ℕ) (p : α → Bool) :=
  {xs : List α // xs.length = k ∧ endpoint xs = p}

/-- The first-occurrence swap maps a fiber with `p u = true` into the fiber
whose endpoint has the `u,v` coordinates toggled. -/
def fiberMap {u v : α} (huv : u ≠ v) {k : ℕ} {p : α → Bool}
    (hu : p u = true) :
    EndpointFiber (α := α) k p →
      EndpointFiber (α := α) k (togglePair u v p) := fun w => by
  have hpar : parity u w.1 = true := by
    have hfun := congrFun w.2.2 u
    simpa [endpoint, hu] using hfun
  have hmem : u ∈ w.1 := parity_true_mem hpar
  refine ⟨swapFirst u v w.1, ?_, ?_⟩
  · calc
      (swapFirst u v w.1).length = w.1.length := swapFirst_length u v w.1
      _ = k := w.2.1
  · calc
      endpoint (swapFirst u v w.1)
          = togglePair u v (endpoint w.1) :=
              endpoint_swapFirst huv (Or.inl hmem)
      _ = togglePair u v p := by rw [w.2.2]

/-- Kernel-level first-occurrence endpoint-fiber injection. -/
theorem fiberMap_injective {u v : α} (huv : u ≠ v)
    {k : ℕ} {p : α → Bool} (hu : p u = true) :
    Function.Injective (fiberMap (α := α) huv (k := k) (p := p) hu) := by
  intro a b hab
  apply Subtype.ext
  apply swapFirst_injective huv
  simpa [fiberMap] using congrArg Subtype.val hab

section Recurrence

/-- The exact coefficient identity in the two-step radial recurrence. -/
theorem coefficient_partition (q : ℝ) :
    (3 * q - 2) + (q - 1) * (q - 2) = q ^ 2 := by
  ring

/-- If the weight-three mass is bounded by the radial endpoint injection,
then the exact two-step recurrence contracts the weight-one mass. -/
theorem odd_slice_descent
    (q pOne pThree pNext : ℝ)
    (hq : 0 < q)
    (hrec : q ^ 2 * pNext = (3 * q - 2) * pOne + 6 * pThree)
    (hradial : 6 * pThree ≤ (q - 1) * (q - 2) * pOne) :
    pNext ≤ pOne := by
  have hmul : q ^ 2 * pNext ≤ q ^ 2 * pOne := by
    calc
      q ^ 2 * pNext = (3 * q - 2) * pOne + 6 * pThree := hrec
      _ ≤ (3 * q - 2) * pOne + (q - 1) * (q - 2) * pOne :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hradial ((3 * q - 2) * pOne)
      _ = q ^ 2 * pOne := by
        rw [← coefficient_partition q]
        ring
  nlinarith [sq_pos_of_pos hq]

/-- Exact three-step successful-word count identity. -/
theorem three_step_success_count (q : ℝ) :
    q + 3 * q * (q - 1) = q * (3 * q - 2) := by
  ring

/-- Repeated one-step descent bounds every later slice by the first. -/
theorem iterate_descent {p : ℕ → ℝ}
    (hstep : ∀ m, p (m + 1) ≤ p m) :
    ∀ m, p m ≤ p 0 := by
  intro m
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact le_trans (hstep m) ih

end Recurrence

end PNPFullCubeRandomWalk
