# johnson-lindenstrauss-lean
## WIP
A zero-`sorry` Lean 4 / mathlib formalization of the **Johnson–Lindenstrauss lemma**.

The probabilistic core is **chi-squared concentration**: the moment generating
function of a sum of squared standard Gaussians, combined with mathlib's Chernoff
bound, yields a two-sided tail bound. From there we obtain the distributional
norm-preservation guarantee of a Gaussian random projection, the JL embedding
existence theorem (via a union bound over pairs), and the inner-product
preservation corollary (via polarization) that underpins quantized
Johnson–Lindenstrauss schemes (QJL / TurboQuant).

## Layout

- `JL/SquaredGaussian.lean` — MGF of a squared standard Gaussian, `(1-2t)^(-1/2)`.
- `JL/ChiSquared.lean` — chi-squared MGF and two-sided tail bounds via Chernoff.
- `JL/Projection.lean` — the Gaussian projection `jlMap` and `E‖f x‖² = ‖x‖²`.
- `JL/NormPreservation.lean` — distributional JL norm-preservation bound.
- `JL/Lemma.lean` — the main `johnson_lindenstrauss` existence theorem.
- `JL/InnerProduct.lean` — inner-product preservation corollary.

## Building

```bash
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```
