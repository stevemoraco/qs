# Navier-Stokes threshold uniformity / diagonal gate

Date: 2026-08-14 UTC
Primary source: R. Shahmurov, arXiv:2606.07869v1, especially Thm. 14.10, Def. 15.1, Lem. 15.2, Thm. 27.3, Def. D.1, Thm. D.10, and B.8-B.10.

Status: abstract absorption theorem proved; prior diagonal verdict corrected; exact missing extraction theorem identified; FIVE-ALARM OFF.

## 1. Correction

`NS_THRESHOLD_TYPED_ZERO_FINAL_AUDIT_2026-08-13.md` correctly showed that a positive threshold does not imply exact typed zero and that the displayed cross-scale packing is insufficient. Its phrase "vanishing-threshold diagonal: killed as a parameter-only repair" is too strong if read as saying the endpoint strict bridge rejects a diagonal.

The source's Theorem 27.3 explicitly assumes a solution-generated, q/J/S-complete sequence with

    L_n -> 0,   V_chi[G_n] = 1,

and concludes a strict bridge `|T_chi[G_n]| <= vartheta + o(1)` with one `0 < vartheta < 1`, unless a coefficient-one saturator exists. Definition D.1 likewise requires typed zero componentwise **in the limit**.

Therefore a `tau_n -> 0` diagonal is compatible with the printed endpoint theorem if the pre-endpoint selection actually constructs normalized packets with typed components tending to zero and uniform compactness constants. What remains killed is the claim that merely sending the raw stopping threshold to zero automatically constructs such a sequence.

## 2. Absolute positive thresholds have a floor

Consider the abstract closed-packet recurrence

    x_{m+1} <= a x_m + b x_m^(1+sigma) + K tau,       (2.1)

with `0 <= a < 1`, `b,K,tau >= 0`, `sigma > 0`.

### NS-TAU-FLOOR-1

Choose `epsilon > 0` with `beta := a + b epsilon^sigma < 1`. If `0 <= x_m <= epsilon`, then

    x_n <= beta^n x_0 + K tau (1-beta^n)/(1-beta)
        <= beta^n x_0 + K tau/(1-beta).              (2.2)

Proof: `b x_m^(1+sigma) <= b epsilon^sigma x_m`, so (2.1) becomes the affine recurrence `x_{m+1} <= beta x_m + K tau`; iterate the geometric series.

Thus a fixed `tau > 0` gives only an `O(tau/(1-beta))` floor. It cannot justify indefinite geometric/Morrey decay to zero if inactive channels are controlled only by an absolute `O(tau)` estimate.

Consequently, the source's phrase "choose tau_ledger below the perturbative scale" cannot be uniform for every arbitrarily small positive score unless a stronger relative structural theorem is proved, e.g.

    Err_inactive(Q) <= C Qscore(Q)^(1+sigma),          (2.3)

or at least

    Err_inactive(Q) <= min(K tau, C Qscore(Q)^(1+sigma)). (2.4)

A fixed positive absolute threshold alone implies neither.

## 3. Narrow first-threshold salvage

There is still a one-crossing repair. If `beta < lambda < 1`, `x_m >= q_* > 0`, and

    K tau <= (lambda-beta) q_*,                        (3.1)

then (2.1) gives `x_{m+1} <= lambda x_m`.

So a fixed threshold can be absorbed relative to one fixed first-threshold level if `K` is uniform and `tau << q_*` quantitatively. This can contradict a first crossing; it does not by itself prove decay at all smaller scores.

The missing local theorem is therefore:

### NS-UNIFORM-SUBTHRESHOLD-ABSORPTION

Prove, uniformly in packet center, scale, lineage, and ledger threshold,

    Qscore(theta R) <= a Qscore(R) + b Qscore(R)^(1+sigma) + K tau_ledger,
    a < 1,                                             (3.2)

and identify a first-threshold normalization for which (3.1) holds. If the proof needs infinite decay rather than one-crossing exclusion, strengthen (3.2) to a relative/superlinear inactive-output estimate or decrease the threshold adaptively with the score.

The source states the order of constants in Section 15 but does not give this componentwise uniform analytic estimate.

## 4. Exact vanishing-threshold endpoint interface

To use Theorem 27.3 with `tau_n -> 0`, the selected packets must satisfy **after bridge normalization**:

1. every normalized typed component tends to zero;
2. visibility normalization does not amplify raw defects (raw `L <= tau_n` is not enough if the visibility scale also vanishes);
3. `A_G(G_n) <= C` with one threshold-independent constant;
4. q/J/S convergence and representation of every nonzero limiting source action;
5. detector/transfer tightness: no collar, macro, projection, cascade, or relaxed-defect loss before the limit;
6. a selection/exhaustion theorem that supplies such packets for arbitrarily small thresholds.

If these hold, the endpoint theorem already gives a uniform strict gap; no additional threshold-dependent bridge constant is required.

## 5. Current selection does not supply that interface

B.8 proves bounded overlap only at each fixed dyadic scale. B.9 then sums over scales by asserting that descendants are new threshold/ledger events. That freshness does not follow from B.8 or from finite total ledger mass: one finite atom can lie in arbitrarily many nested packets at different scales and fund each one.

A diagonal can be resurrected by a genuinely new cross-scale input: disjoint fresh charges, a Carleson packing estimate, or a strictly decreasing well-founded routing rank. The constants must be uniform enough as `tau -> 0` to yield the normalized compactness conditions above. A count growing like `1/tau` is not itself fatal; repeated charging of the same mass at infinitely many scales is.

## 6. General defect/gap criterion

For a future recurrence

    x' <= q(tau) x + r(tau),   q(tau) < 1,

its stationary floor is `r(tau)/(1-q(tau))`. Therefore `r(tau) -> 0` is insufficient if `q(tau) -> 1`; one needs

    r(tau) = o(1-q(tau)).                            (6.1)

Finite countermodel: `q_n = 1-1/n`, `r_n = 1/n`, `x = 1` gives equality and no contraction although `q_n < 1` and `r_n -> 0`.

For Shahmurov's printed Theorem 27.3 the intended endpoint gap is uniform once the master hypotheses hold. The immediate problem is supplying those hypotheses from the threshold algorithm.

## 7. Corrected verdict and next theorem

- fixed-threshold local absorption: viable at one first-threshold scale only if a uniform `K tau` theorem is proved;
- fixed-threshold full decay: not obtained from an absolute `O(tau)` defect; it stalls at an `O(tau)` floor;
- vanishing-threshold endpoint: compatible in principle with Theorem 27.3 / Appendix D;
- current extraction: unproved because normalized vanishing, denominator compactness, and cross-scale freshness are missing.

Highest-value threshold theorem:

### NS-TAU-UNIFORM-FRESH-ENDPOINT

For every `tau_n -> 0`, prove that either a selected positive output consumes a genuinely fresh cross-scale charge, or a first-threshold normalized packet sequence exists satisfying the six endpoint properties above.

A proof feeds directly into Theorem 27.3. A finite abstract countermodel under the source's displayed hypotheses would kill the threshold architecture at the correct interface.

## 8. Formalization / hostile scope

The affine recurrence and defect/gap countermodel are suitable for Lean, but no Lean/lake toolchain is available in the current execution environment, so no uncompiled Lean artifact is committed. Existing verified finite packing countermodels remain the formal provenance for the cross-scale obstruction.

These are abstract inequalities and a logical audit of arXiv:2606.07869v1. They do not prove the source's ledger terms satisfy `O(tau)`, do not construct the diagonal endpoint, and do not repair the separate superendpoint source, F^4/F^2 detector, source-dual carrier, or packing defects.

FIVE-ALARM OFF.
