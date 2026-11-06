# Hardin–Taylor Nearly Perfect Prediction — Lean 4 formalization

A formalization of the Hardin–Taylor "nearly perfect prediction" theorem
(Am. Math. Monthly 115 (2008), 91–96) in Lean 4 + Mathlib.

## The theorem

Assuming the axiom of choice, there is a prediction strategy that, given the
observed past `f ↾ (-∞, t)` of an arbitrary function `f : ℝ → ℝ`,

* predicts the present value `f(t)`, and
* predicts the immediate future — its predicted continuation agrees with `f`
  on some right-neighbourhood of `t` —

and both predictions fail only on **countable nowhere dense** sets of times
`t`. The strategy is *nearly perfect*.

* `hardin_taylor` — present value only;
* `hardin_taylor_full` — present value and immediate future.

**Construction.** Fix a well-order `r` on `ℝ → ℝ` (choice). Given the history
at `t`, let `g_t` be the `r`-minimal function agreeing with `f` before `t`;
predict `g_t(t)` and continue with `g_t` itself. At failure times `s < t` the
climb in `r` is strict (`g_s` and `g_t` differ: `g_t` already agrees with `f`
on `(s, t)`, while the failure at `s` produces a disagreement point there).
Hence the failure set embeds order-preservingly into the well-order `r`, so it
is a well-ordered subset of `ℝ` — and every such subset is countable and
nowhere dense.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain
`leanprover/lean4:v4.35.0`; Mathlib pinned in `lake-manifest.json`.

```sh
lake exe cache get            # fetch prebuilt Mathlib oleans (one-time)
lake build
lake env lean AxiomCheck.lean  # axiom audit
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every
theorem — no `sorryAx`, no `sorry` anywhere.

## Files

| File | Contents |
|------|----------|
| `Basic.lean` | histories and compatibility |
| `WellOrdered.lean` | well-ordered subsets of `ℝ` are countable and nowhere dense |
| `Predictor.lean` | the `r`-minimal candidate predictor |
| `Monotone.lean` | monotonicity and strict climb |
| `Exceptional.lean` | the present-value failure set |
| `Continuation.lean` | the future failure set; union of nowhere dense sets |
| `Main.lean` | `hardin_taylor`, `hardin_taylor_full` |

## References

* C. Hardin, A. Taylor. *A peculiar connection between the axiom of choice and
  predicting the future.* Am. Math. Monthly 115 (2008), 91–96.
* J. D. Hamkins. *The Nearly Perfect Prediction Theorem.* Notices AMS, March 2025.
* U. Yurtsever. *Does the Hardin–Taylor Predictor Actually Predict the Future?
  Yes; but Only in Retrospect.* arXiv:2608.13899.
