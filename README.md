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

## The proof, in plain English

The proof is pure well-ordering gymnastics — no statistics, no learning, no
regularity of `f` is assumed. `f` may be total chaos.

**1. Well-order the set of all functions.** By the well-ordering theorem
(this is where the axiom of choice enters) fix a well-order `r` on the set of
*all* functions `ℝ → ℝ`: every nonempty collection of functions has an
`r`-least member. The order `r` is an abstract yardstick — it says nothing
about how the functions look; it only lets us pick "the first candidate".

**2. The predictor** (`Predictor.lean`). Fix `f` and a time `t`. Call
`g : ℝ → ℝ` a *candidate at `t`* if `g` agrees with `f` on the whole past
`(-∞, t)`. The candidate set is never empty — `f` itself is a candidate. Let
`g_t` be the `r`-least candidate. The strategy: predict `f(t)` as `g_t(t)`,
and (full version) predict the future by the continuation `g_t` itself.
Intuition: among all worlds consistent with everything seen so far, bet on
the "first" one in `r`, and read off its value at `t`.

**3. The strategy uses only the past** (`Basic.lean`). If `f` and `g` agree
on `(-∞, t)`, their candidate sets at `t` are literally the same set, so the
`r`-least candidate — and hence the prediction — is the same. No peeking.

**4. Failure times strictly climb the well-order** (`Monotone.lean`). This is
the heart. Fix `f`; let `E` be the set of times where the present-value
prediction is wrong. Take two failure times `s < t` and compare `g_s`, `g_t`:

* `g_t` agrees with `f` on all of `(-∞, t)`, so in particular before `s`.
  Hence `g_t` is a candidate at `s`, and since `g_s` is the `r`-least one,
  `g_s` sits at or below `g_t` in `r`.
* But `g_s ≠ g_t`: at `s` the prediction failed, so `g_s(s) ≠ f(s)`, while
  `g_t(s) = f(s)` because `s < t`.
* Therefore `g_s` is *strictly* below `g_t` in `r`.

So `t ↦ g_t` is strictly increasing from `E` (in the ordinary order of `ℝ`)
into the well-order `r`. Consequently `E` is well-ordered by the ordinary
order: any nonempty subset `A ⊆ E` has a least element — take the member of
`A` whose candidate is `r`-least. The same argument covers the future
failures of the full version: if the continuation at `s` fails on every
right-neighbourhood of `s`, then for `s < t` the candidate `g_t` agrees with
`f` on the whole interval `(s, t)`, so `g_s ≠ g_t`, and the climb is strict
again.

**5. A well-ordered set of times is small** (`WellOrdered.lean`). Any subset
`E ⊆ ℝ` well-ordered by the ordinary order is countable and nowhere dense:

* *Successors exist.* Every element of `E` except possibly the largest has an
  immediate successor — the least element strictly above it — so `E` is a
  chain of points separated by open gaps `(x, next(x))` that contain no
  points of `E`.
* *Countable.* Put one rational number inside each gap. The gaps are pairwise
  disjoint, so distinct points give distinct rationals; `ℚ` is countable, so
  `E` is too (plus at most one extra point, the maximum).
* *Nowhere dense.* Each gap is also free of the *closure* of `E`: a point of
  the gap could be a limit of `E` only if `E` had points arbitrarily close
  inside the gap, and the gap is empty. So any interval that touches `E`
  contains a whole subinterval untouched by the closure of `E` — the closure
  contains no interval.

**6. Assemble** (`Exceptional.lean`, `Continuation.lean`, `Main.lean`). The
present-value failure set is well-ordered by step 4, hence countable and
nowhere dense by step 5. For the full theorem, the total failure set is the
union of the present-value failures and the continuation failures; each piece
is well-ordered by the climb argument, hence countable and nowhere dense, and
so is their finite union.

**Why this is surprising.** The past of an arbitrary function carries no
usable information about its future — yet a nearly perfect predictor exists.
The strategy does not learn: it bets on the `r`-minimal world consistent with
the observed past, and a mistake at time `s` is exactly the evidence that the
true world is not that bet, forcing the bet to strictly climb the well-order
at every later mistake. A well-order is steep: such a climb can happen only
along a well-ordered set of times, and those are tiny in `ℝ`. Everything is
non-constructive — `r` cannot be written down, which is precisely the
"peculiar connection between the axiom of choice and predicting the future"
of the paper's title.

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

## License

MIT — see [LICENSE](LICENSE).

## References

* C. Hardin, A. Taylor. *A peculiar connection between the axiom of choice and
  predicting the future.* Am. Math. Monthly 115 (2008), 91–96.
* J. D. Hamkins. *The Nearly Perfect Prediction Theorem.* Notices AMS, March 2025.
* U. Yurtsever. *Does the Hardin–Taylor Predictor Actually Predict the Future?
  Yes; but Only in Retrospect.* arXiv:2608.13899.
