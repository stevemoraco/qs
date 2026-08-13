# BSD Agyemang dimension triangle — 2026-08-13

**📚 SOURCE-VERIFIED · 🟢 PROVED · 🔴 REFUTED foundational geometry · 🧱 OBSTRUCTION · 🔵 LEAN-SOURCE elsewhere · 🚧 MISSING valid higher-rank object**

## Source and assumptions

Source under audit: Paul Agyemang, *A Proof of the Birch and Swinnerton-Dyer Conjecture*, March 2026, DOI `10.13140/RG.2.2.27530.73928`.

The paper defines

`W_r = E ×_{X_0(N_E)} E ×_{X_0(N_E)} ... ×_{X_0(N_E)} E`

with `r` copies, calls `W_r` a complex `2r`-dimensional smooth projective Kuga–Sato variety, and defines the diagonal image of `E` as a codimension-`r` cycle `Z_r`.

## Proof: the three displayed dimension claims cannot coexist

A diagonal image of the elliptic curve `E` has complex dimension `1`.

If the paper's stated dimension `dim_C W_r = 2r` were correct, that diagonal would have codimension

`2r - 1`,

not `r` for any `r > 1`.

Conversely, the claimed codimension `r` of a one-dimensional diagonal forces

`dim_C W_r = r + 1`.

That is exactly the dimension one expects from the standard Kuga–Sato style repair: take an elliptic surface of complex dimension `2` over the modular curve of dimension `1`, then form its `r`-fold fibre power over the base. The dimension is

`2r - (r-1) = r+1`.

Thus the source's own stated `2r` dimension is incompatible with the codimension needed for `Z_r ∈ CH^r(W_r)`.

There is a still earlier type problem: the displayed fibre product of the fixed elliptic curve `E` over `X_0(N_E)` requires morphisms `E -> X_0(N_E)`. The standard modular parametrization goes in the opposite direction `X_0(N_E) -> E`; it does not type the written fibre product.

**🟢 PROVED:** for `r>1`, no object can simultaneously satisfy the source's displayed definition as written, its asserted complex dimension `2r`, and its claim that the one-dimensional diagonal has codimension `r`.

## Critic verdict

This is foundational, not a constant-factor issue. The Beilinson–Bloch height, arithmetic Siegel–Weil identity, higher Gross–Zagier formula, Euler-system class, and Iwasawa chain are all built on `W_r` and `Z_r`. Until those objects are replaced by a correctly typed Kuga–Sato fibre power and every degree/codimension/cohomology group is recomputed, the later formulas do not have their advertised domains.

The paper's separate statement that the class of `Z_r` lies in a `(-1)^r` complex-conjugation eigenspace also cannot imply null-homology by itself: an anti-invariant eigenspace can contain nonzero vectors. That is an independent obstruction already banked upstream.

## Lean status

`Stevemoraco/RH-Lean` contains `Millennium/BSD/KugaSatoObjectFirewall.lean`, formalizing finite dimension/codimension and eigenspace countermodels. **🔵 LEAN-SOURCE.** Its replay workflow at commit `f24b71808d1e2fa70acd0281716745e7a0d64659` failed, so this run does not promote it to **✅ LEAN-VERIFIED**.

## Exact remaining gap

**🧩 BRIDGE / 🚧 MISSING:** define the actual Kuga–Sato object over the modular curve, prove the diagonal/generalized Heegner cycle lies in the exact Chow group and is homologically trivial for the required projector, then establish the all-rank height formula, Euler-system norm relations, Selmer bounds, and both Iwasawa divisibilities without assuming BSD-equivalent input.

## Provenance

- ResearchGate source lines 787–905: Definition 2.1, `2r`-dimensional claim, fibre product, diagonal and codimension-`r` claim, and null-homology argument.
- Source lines 1107–1135 later again treat `W_r` as real dimension `4r`, reinforcing the `2r` complex-dimension claim.
- `Stevemoraco/RH-Lean` commit `6fac9ac5d6ff6aadb7c56c7a6330e680b930f50c`.
- failed replay run `31679246139`.

No BSD theorem is proved or disproved. FIVE-ALARM OFF.
