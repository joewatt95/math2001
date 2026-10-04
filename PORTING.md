# Porting notes: Lean 4.3.0 to 4.33.1

This fork updates Heather Macbeth's [`math2001`](https://github.com/hrmacbeth/math2001) from Lean
4.3.0, which the book was written against, to Lean 4.33.1. The starting point was upstream
[PR #38](https://github.com/hrmacbeth/math2001/pull/38), which took the repository as far as Lean
4.22.0. The rest of the work covers the gap from 4.22 to 4.33.

4.33.1 was chosen because it was the latest stable release at the time, in September 2026, with
4.34.0 still at release candidate. Anyone bumping further should read the sections below first,
since several of the decisions recorded here were forced by upstream changes and will need
revisiting rather than repeating.

The aim throughout was to keep the course material reading the way *The Mechanics of Proof*
describes it. Where an upstream rename would have changed what a student types or how a chapter
teaches its subject, the old spelling was kept and the reason recorded below.

## What to expect from a build

`lake build Library` is the signal that the support code in [`Library`](Library) is healthy. It
should finish with no errors and no warnings at all.

`lake build` additionally builds the course material in [`Math2001`](Math2001). It should finish
with no errors, and with roughly 500 `declaration uses 'sorry'` warnings. Those are expected. Every
exercise in the book is a `sorry` waiting for a student, so the warnings are the exercises
themselves rather than a sign of breakage.

The first build needs the Mathlib cache, so run `lake exe cache get` before `lake build`.

CI in [`.github/workflows/lean_build.yml`](.github/workflows/lean_build.yml) builds the whole
project on Linux, macOS and Windows. Upstream built only `Library`, and only on Linux, through
hand-written steps that fetched a fixed elan release from a hardcoded URL and used
`actions/checkout@v2`. Both had aged badly by 4.33, so they were replaced with
`leanprover/lean-action`, which installs whatever [`lean-toolchain`](lean-toolchain) asks for,
notices the Mathlib dependency and fetches its cache, then builds. It needs no maintenance when the
toolchain moves.

The matrix costs nothing on a public repository, and it catches the project acquiring a platform
dependency, a path separator assumption being the likeliest. It proves little beyond that. GitHub
runners are clean and uniform, and the machines students arrive with are neither.

The failure that actually costs time is not a platform bug. A student opens the project in VS Code
before installing `elan` and fetching the cache, the extension provisions a Lean of its own, and
the editor and terminal end up compiling against different copies. CI never opens an editor, so no
run will catch it. The setup ordering in the README, and the recovery section after it, are what
address that.

## Dependencies

Mathlib tracks the toolchain automatically through `s!"v{Lean.versionString}"` in
[`lakefile.lean`](lakefile.lean), so bumping [`lean-toolchain`](lean-toolchain) is enough to move
both.

Only the two direct dependencies are pinned by tag. Mathlib in turn requires `batteries`,
`proofwidgets`, `importGraph`, `LeanSearchClient` and `plausible` from `main`, and `aesop` and `Qq`
from `master`, so `lake update` re-resolves those seven to whatever those branches point at on the
day it runs. The exact revisions that go with this toolchain are recorded in
[`lake-manifest.json`](lake-manifest.json), which is why setting up a clone uses
`lake exe cache get` rather than `lake update`. Reserve `lake update` for a deliberate bump, and
expect to rebuild and recheck afterwards.

Duper is pinned to `v4.33.0` rather than tracking the toolchain, because Duper has no `v4.33.1`
tag. Lean 4.33.1 is a kernel patch release over 4.33.0, so the `v4.33.0` tag compiles against this
toolchain without trouble. Duper is not optional. It is what the `exhaust` tactic runs on, and
`exhaust` is used throughout chapters 8 to 10.

The Gradescope autograder was dropped. Its `require`, the `import AutograderLib` lines, and the 85
`@[autograded n]` attributes in [`Math2001/Homework`](Math2001/Homework) are all commented out
rather than deleted, so re-enabling it is a matter of uncommenting them and repointing the
`require` at a current revision. The autograder has moved on considerably since 4.3.0 and now
pulls in `comparator` as a further dependency.

The Gitpod configuration was also removed. Students on this course install Lean locally,
since they go on to their own formalisation projects afterwards, so `.gitpod.yml` and the
`.docker/gitpod` image it referenced were dropped rather than left to rot unused.

## The largest single cause of breakage

Lean 4.23 tightened the module system so that imports no longer leak transitively. A file that
uses a tactic must now import the module defining it, even when some other import used to drag it
in. Most of the initial error count came from this, and the errors it produces are misleading. A
missing import for `ring` reports `unknown tactic` at the `ring` call site rather than anything
about imports, because the syntax still parses while the macro implementing it is absent.

Imports added for this reason:

| Module | Import added | Needed for |
| --- | --- | --- |
| [`Library/Theory/Division.lean`](Library/Theory/Division.lean) | `Mathlib.Tactic.Ring` | `ring` |
| [`Library/Theory/Prime.lean`](Library/Theory/Prime.lean) | `Mathlib.Tactic.Ring` | `ring` |
| [`Library/Theory/GCD.lean`](Library/Theory/GCD.lean) | `Mathlib.Tactic.Ring` | `ring` |
| [`Library/Tactic/Induction.lean`](Library/Tactic/Induction.lean) | `Mathlib.Tactic.Cases` | `induction'` |
| [`Library/Theory/NumberTheory.lean`](Library/Theory/NumberTheory.lean) | `Mathlib.Tactic.Cases` | `induction'` |
| [`Library/Tactic/Numbers/ModEq.lean`](Library/Tactic/Numbers/ModEq.lean) | `Mathlib.Tactic.Cases` | `cases'` |
| [`Library/Tactic/Rel.lean`](Library/Tactic/Rel.lean) | `Lean.Elab.Tactic.SolveByElim` | `SolveByElimConfig`, `processSyntax` |
| [`Library/Theory/InjectiveSurjective.lean`](Library/Theory/InjectiveSurjective.lean) | `Mathlib.Data.Nat.Notation` | the `ℕ` notation |

The `ℕ` case is worth singling out, because without the notation Lean silently auto-bound `ℕ` as
an implicit type variable rather than reporting an unknown identifier. The visible symptom was a
complaint that `OfNat ℕ 0` could not be synthesised.

## Renamed lemmas

| Was | Now | Where |
| --- | --- | --- |
| `Int.emod_add_ediv` | `Int.emod_add_mul_ediv` | [`Library/Tactic/ModCases.lean`](Library/Tactic/ModCases.lean) |
| `Int.fmod_add_fdiv` | `Int.fmod_add_mul_fdiv` | [`Library/Theory/GCD.lean`](Library/Theory/GCD.lean), [`Math2001/06_Induction/07_Euclidean_Algorithm.lean`](Math2001/06_Induction/07_Euclidean_Algorithm.lean) |
| `pow_eq_zero` | `eq_zero_of_pow_eq_zero` | [`Library/Tactic/Cancel.lean`](Library/Tactic/Cancel.lean) |
| `mul_le_mul_right'` | `Nat.mul_le_mul_right` | [`Library/Theory/Prime.lean`](Library/Theory/Prime.lean) |
| `Nat.le_step` | `Nat.le_succ_of_le` | [`Library/Tactic/Induction.lean`](Library/Tactic/Induction.lean) |
| `_root_.not_imp` | `Classical.not_imp` | [`Math2001/05_Logic/03_Negation_Algorithm.lean`](Math2001/05_Logic/03_Negation_Algorithm.lean) |

Chapter 6 defines its own `fmod`, `fdiv` and `fmod_add_fdiv` as course material, and those are
untouched. Only the uses of the identically named core lemmas were renamed.

## Metaprogramming that moved

`SolveByElim` migrated from Mathlib into Lean core. The names `SolveByElimConfig` and
`processSyntax` survived unchanged, so [`Library/Tactic/Rel.lean`](Library/Tactic/Rel.lean) needed
only the new import.

`abelNFTarget` no longer exists. The discharger in
[`Library/Tactic/Addarith.lean`](Library/Tactic/Addarith.lean) now calls the `abel_nf` tactic
through `evalTactic`, wrapped in the same `try` as the steps around it, since `abel_nf` reports an
error when it changes nothing.

## Syntax changes in the course files

Mathlib now declares `ring` as `macro (name := ring) "ring" : tactic`, which has exactly the same
shape as the override in [`Library/Config/Ring.lean`](Library/Config/Ring.lean). Two identical
parsers for one token produce an ambiguity that resolves to `unknown tactic`. The override is now
written with `macro_rules` against the existing syntax, matching the `conv` line beside it.

`(· : ℕ) ∣ ·` no longer means what it did. The parenthesis now closes the lambda, so the term
elaborates as `((fun x => x) : ℕ)` and the relation falls apart. The seventeen affected examples in
[`Math2001/10_Relations/01_Introduction.lean`](Math2001/10_Relations/01_Introduction.lean) now
ascribe the whole relation instead, as in `((· ∣ ·) : ℕ → ℕ → Prop)`.

`push_neg` reports an error when it makes no progress, where it used to succeed quietly. Uses of
the form `split_ifs with h1 h2 <;> push_neg at *` are now guarded with `try`, since some branches
have nothing to push.

Two proofs needed adjusting because definitional unfolding changed. `Int.ModEq.pow` in
[`Library/Theory/ModEq/Lemmas.lean`](Library/Theory/ModEq/Lemmas.lean) now rewrites with `pow_zero`
and `pow_succ` explicitly rather than relying on `a ^ 0` reducing to `1`. The `pascal` example in
[`Math2001/06_Induction/05_Pascal.lean`](Math2001/06_Induction/05_Pascal.lean) lost its opening
`calc` step, because `field_simp` followed by `norm_cast` now leaves the goal in the associated
form that step used to produce.

## Deprecated vocabulary that was kept on purpose

Chapter 10 is built on `Reflexive`, `Symmetric`, `AntiSymmetric` and `Transitive`, all of which
Mathlib deprecates in favour of `Std.Refl`, `Std.Symm`, `Std.Antisymm` and `IsTrans`. The
replacements are type classes, while the deprecated names are plain definitions. Unfolding one
with `dsimp [Reflexive]` is the method the chapter teaches, and a type class cannot be unfolded
that way, so migrating would mean rewriting the chapter rather than renaming anything. The linter
is switched off instead, by `linter.deprecated := false` inside `math2001_init` in
[`Library/Basic.lean`](Library/Basic.lean). That reaches the course files only, because `Library`
never calls `math2001_init`, so deprecations in the support code stay visible.

`push_neg` needed different treatment. Mathlib emits its deprecation with a bare `logWarning` that
no linter option controls. `Library/Basic.lean` therefore defines `push_neg` as an alias for
`push Not`, copied from the implementation Mathlib's own deprecation message recommends for
projects that want to keep the name, along with a matching `#push_neg` command standing for
`#push Not => e`. Both are exact aliases, so chapter 5 still reads as the book writes it.

## The `exhaust` tactic

[`Library/Tactic/Exhaust.lean`](Library/Tactic/Exhaust.lean) carries its own detailed notes. Two
points matter most.

`exhaust` falls back to `sorry` when Duper cannot close the goal. This is deliberate. Several
exercises are stated with `sorry` standing in for an answer the student has yet to supply, as in
`example : {1, 2} ∩ {3} = sorry`, and no prover can discharge those. Failing hard would turn every
untouched exercise into a red build error. The fallback keeps the build green while Lean still
reports `declaration uses 'sorry'`, so an admitted goal always reads as an incomplete proof.

Anyone changing this should confirm the fallback never hides a real proof. Two checks establish
that. A provable `exhaust` goal depends only on `[propext, Classical.choice, Quot.sound]` under
`#print axioms`, while an admitted one depends on `[sorryAx]`. Separately, of the declarations
across the six `exhaust`-using files that warn about `sorry`, all but one contain a literal `sorry`
in their own source. The exception is `example : b ∘ a = c` in
[`Math2001/08_Functions/03_Composition.lean`](Math2001/08_Functions/03_Composition.lean), which is
admitted only because the `def c` above it is itself an unfilled exercise.

The `preprocessing := no_preprocessing` setting is also load-bearing, and unrelated to the
fallback. Duper's `lean-auto` monomorphization path emits a proof term the kernel rejects on the
`Int.ModEq` example in
[`Math2001/09_Sets/02_Set_Operations.lean`](Math2001/09_Sets/02_Set_Operations.lean). That failure
arrives after the tactic block has already succeeded, so no `first` alternative and no `sorry`
fallback can catch it.
