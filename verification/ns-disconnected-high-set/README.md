# NS disconnected-high-set Lean firewall

This verifier checks only the finite scalar identity behind the two-slab
mean-oscillation lower bound:

```text
|1-m|+|-1-m|=2 for -1<=m<=1.
```

It does not define BMO, vorticity, Navier--Stokes, a regularity criterion, or
the Clay target. A successful workflow therefore verifies the arithmetic
firewall only.

The corresponding human proof places opposite constant directions on two
nearby disconnected high-set components. Their componentwise gradients are
zero, but every bounded extension has an order-one mean-oscillation floor.
This refutes a proposed geometric shortcut; it does not solve Navier--Stokes.

`TARGET_DELTA=0`

`FIVE_ALARM=NO`
