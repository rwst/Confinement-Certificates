/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Lake
open Lake DSL

package "lean-code" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/-- `leanprover/comparator`, pinned to a tag; it builds against this project's toolchain.
Provides the `comparator` executable and, transitively, `lean4export`; both are built by
`lake build comparator lean4export` and used by the `test` driver below. -/
require comparator from git
  "https://github.com/leanprover/comparator" @ "v4.33.0-rc1"


lean_lib ForMathlib where
  globs := #[.submodules `ForMathlib]

lean_lib FLP where
  globs := #[.submodules `FLP]

lean_lib Z32 where
  globs := #[.submodules `Z32]


/-- The trusted statement of record: the certified theorems stated against Mathlib alone,
with `sorry` proofs.  Consumed by `comparator`, never imported by the development.

One module suffices here: the only definition the certified statements mention is `FLP.ZSet`,
a plain non-recursive `def`, so there is no generated matcher whose sharing would have to
mirror the development's module structure. -/
lean_lib Challenge where

/-- The development, re-exported for `comparator` to compare against `Challenge`. -/
lean_lib Solution where

/-- `Solution` plus `Z32.UnionRecord`, the one module whose kernel check is expensive (about
100 seconds and 12 gigabytes).  `comparator.json` names this module rather than `Solution`,
because the union record of Theorem 7.12 is among the statements it certifies. -/
lean_lib SolutionRecord where

/-! ## `lake test`: certify the challenge/solution pair with `leanprover/comparator`

`lake test` runs comparator on `comparator.json`, checking that the solution module proves
the exact statements of `Challenge`, within the axioms the config permits, and that the
resulting environment is re-accepted by the Lean kernel.

Comparator needs three binaries.  `lake build comparator lean4export` produces two of
them; `landrun` must be installed once by hand (Go, Linux/Landlock only).  Each is
overridable via `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN`.
See `README.md`.
-/

/-- The comparator config run by `lake test`, unless overridden by `lake test -- <cfg>…`.

One config certifies every statement of `Challenge`, against `SolutionRecord`.  That module
carries `Z32.UnionRecord`, whose kernel check alone costs about 100 seconds and 12 gigabytes,
so the run wants a machine with about 16 GB of memory. -/
def comparatorConfigs : Array String := #["comparator.json"]

/-- Resolve a binary: `$envVar` if set, else the first candidate path that exists, else
whatever `PATH` yields.  `none` if it cannot be found at all. -/
def findBinary (envVar name : String) (candidates : Array System.FilePath) :
    IO (Option String) := do
  if let some path ← IO.getEnv envVar then
    return some path
  for candidate in candidates do
    if ← candidate.pathExists then
      return some (← IO.FS.realPath candidate).toString
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  let path := out.stdout.trimAscii.toString
  return if out.exitCode == 0 && !path.isEmpty then some path else none

@[test_driver]
script test (args) do
  let ws ← getWorkspace
  let root := ws.dir
  let packages := root / ".lake" / "packages"

  let comparator? ← findBinary "COMPARATOR_BIN" "comparator"
    #[packages / "comparator" / ".lake" / "build" / "bin" / "comparator"]
  let lean4export? ← findBinary "COMPARATOR_LEAN4EXPORT" "lean4export"
    #[packages / "lean4export" / ".lake" / "build" / "bin" / "lean4export"]
  let landrun? ← findBinary "COMPARATOR_LANDRUN" "landrun" #[]

  let some comparator := comparator?
    | IO.eprintln "lake test: `comparator` not found. Run `lake build comparator lean4export`."
      return 1
  let some lean4export := lean4export?
    | IO.eprintln "lake test: `lean4export` not found. Run `lake build comparator lean4export`."
      return 1
  let some landrun := landrun?
    | IO.eprintln "lake test: `landrun` not found; comparator sandboxes every build with it."
      IO.eprintln "Install it once (Linux only — it uses Landlock):"
      IO.eprintln "  git clone https://github.com/Zouuup/landrun && cd landrun"
      IO.eprintln "  go build -o ~/.local/bin/landrun cmd/landrun/main.go"
      IO.eprintln "Then re-run, or point COMPARATOR_LANDRUN at the binary."
      return 1

  -- Reproduce `lake env` for the child: comparator shells out to `lake`, `lean` and
  -- `lean4export`, all of which need LEAN_PATH and the toolchain on PATH.
  let env := ws.augmentedEnvVars ++ #[
    ("COMPARATOR_LEAN4EXPORT", some lean4export),
    ("COMPARATOR_LANDRUN", some landrun)]

  let configs := if args.isEmpty then comparatorConfigs else args.toArray
  for config in configs do
    IO.println s!"\n=== comparator {config} ==="
    let child ← IO.Process.spawn { cmd := comparator, args := #[config], env, cwd := root }
    let rc ← child.wait
    if rc != 0 then
      IO.eprintln s!"lake test: comparator rejected {config}"
      return rc
  return 0

