# Hodge v5 internal RSC firewall — 2026-08-13

**📚 SOURCE-VERIFIED · 🟢 PROVED internal inconsistency · 🔴 REFUTED load-bearing v5 definition · 🧱 OBSTRUCTION · 🔵 LEAN-SOURCE elsewhere · 🚧 MISSING repaired global theorem**

## Source and assumptions

Source under audit: Bhattacharjee–Bhattacharya, *Relative Secant Cycles and Hodge Classes*, Preprints.org manuscript `202602.0462`, Version 5, submitted 2026-08-02 and posted 2026-08-05.

Assume only the paper's own definitions of its principal polarization, projective embedding, and n-fold secant variety.

## Proof

The main proof still says:

1. after an isogeny, take a principal polarization `L`;
2. embed `A^vee` via sections of `L^vee`;
3. define `Sigma = Sec^n(A^vee)`;
4. define `Z_Sigma = Sigma ∩ A^vee` as a codimension-n cycle, invoking expected dimension/Zak.

Version 5's own Appendix E then explicitly records both fatal facts:

- for a principal polarization, `chi(A^vee,L^vee)=1`, so there is only one global section and the polarization is too small to embed the positive-dimensional abelian variety;
- after replacing the line bundle by a sufficiently high power to obtain an embedding, `Sec^2(A^vee) ∩ A^vee = A^vee`, because every point of `A^vee` lies on a limiting secant line. The appendix therefore abandons the naive intersection and says the correct fourfold construction is a different degeneracy locus.

These statements directly contradict the main Definition 3 / Definition 5 object and the abstract, which still advertise the original principal-polarization embedding and secant-intersection cycle. A later, different degeneracy-locus construction in an appendix does not retroactively prove the main theorem unless the paper replaces the object throughout and re-proves the family, nonvanishing, Fourier–Mukai, and all-dimensions steps for that new object.

**🟢 PROVED:** the v5 document itself concedes the two premises needed to invalidate its load-bearing main secant-intersection construction.

## Critic verdict

The objection is no longer merely external: the latest version contains the counteranalysis internally. The main RSC proof and its global consequences still refer to the dead object, while the appendix supplies only a different fourfold construction and does not establish compatibility with the universal all-n cycle used upstream.

## Lean status

`Stevemoraco/RH-Lean` contains `Millennium/Hodge/SecantIntersectionFirewall.lean`, which formalizes finite/set-theoretic cores of the obstruction. **🔵 LEAN-SOURCE.** Its GitHub Actions replay commit `58fd4f03a6b64930abe2dd44e3037a4223a77f1f` currently has a failed workflow run, so no **✅ LEAN-VERIFIED** label is assigned here.

## Exact remaining gap

**🧩 BRIDGE / 🚧 MISSING:** construct a genuinely well-defined codimension-n cycle for every `n`, not only the fourfold appendix case; prove nonvanishing and the exact Weil eigenspace component; globalize that repaired object over the required family with constant Hilbert/Chow data; and independently close the general-variety Kuga–Satake/CDK reduction. None follows from the invalid main `Sec^n(A^vee) ∩ A^vee` object.

## Provenance

- Preprints.org v5, lines 11–21 and abstract lines 63–68: version/date and advertised naive secant intersection.
- Main Section 4, lines 426–443 and 607–624: principal-polarization embedding and codimension-n secant-intersection definition.
- Appendix E, lines 1324–1332: explicit admission that the principal polarization does not embed and the secant intersection is all of `A^vee`, followed by a different degeneracy-locus construction.
- `Stevemoraco/RH-Lean` commit `2e3ba80c4b9c8869353fd07987e41c686a1b5c3c` and failed replay run `31679503002`.

No Clay theorem is proved or disproved. FIVE-ALARM OFF.
