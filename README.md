# Symmetric collision rank

A Lean formalization of a conditional upper bound of two on symmetric fixed-tree
collision rank, with a specialization to an axiomatized Sturmian group.
Built on Lean **4.32.1** and Mathlib **v4.32.1**.

## Statements

The central relative theorem in namespace `CollisionRank` is

```lean
theorem relative_symmetric_rank_at_most_two {G : Type u} [Group G]
    (I : ExternalInputs G) : SymmetricCollisionRankAtMost G 2
```

[main.lean](main.lean) contains the seven public statements and their English
descriptions. [definitions.lean](definitions.lean) specifies the definitions
and conventions used in those statements.

T01–T05 depend only on `propext`, `Classical.choice`, and `Quot.sound`.
T06 applies the bound to `SturmianGroup` using A01–A05 from
[axioms.lean](axioms.lean). T07 also uses A06–A07 to obtain a group with this
bound and `¬ InSG G`. The named carrier and the predicate `InSG` are opaque
inputs; the applications depend on the stated external assumptions.

The following sources describe the intended mathematical inputs. In Lean,
these inputs remain explicit assumptions.

| Axioms | External input | Source |
|---|---|---|
| A04 | Local finiteness of half-line stabilizers | [Topological full groups](https://arxiv.org/pdf/1105.0719), Definition 2.1 and Theorem 2.2(2) |
| A05 | Arbitrarily high powers in the specified Sturmian language | [Sturmian repetitions](https://arxiv.org/pdf/1411.5474), Section 3; [Powers in Sturmian sequences](https://doi.org/10.1016/S0195-6698(03)00026-X) |
| A06–A07 | The class SAG and the nonmembership result | [Topological full groups](https://arxiv.org/pdf/1105.0719), definition of SAG and Proposition 2.4 |

## Verification performed

The reference and implementation are compiled separately. The reference imports
`main → axioms → definitions → Mathlib`; the implementation is `CollisionRank.Main`
and never imports the reference. The seven `sorry` bodies in `main.lean` are
intentional placeholders for the reference statements, so their warnings are
expected. They are excluded from the implementation.

- **Build and axiom audit.** `lake build` checked the project sources using the
  pinned dependency caches. [Audit.lean](proofs/verification/Audit.lean) checked
  all 379 implementation declarations, including unused and private helpers:
  exactly seven project axioms, with no `sorryAx` dependencies. It also fixes
  each main theorem's exact axiom dependencies with guarded `#print axioms`
  commands. Any change to those dependencies fails the build, even if the new
  axiom is permitted for another theorem. Result: `GLOBAL_AXIOM_AUDIT_PASS`.
- **[Comparator](https://github.com/leanprover/comparator).** Checked the seven
  theorem statements against their implementations, together with the definitions
  they use and the types of permitted axioms. It enforced the allowlist in
  [comparator.json](proofs/verification/comparator.json) and replayed the exported
  proof dependencies through Lean's kernel. Result: `Your solution is okay!`.
- **[nanoda](https://github.com/ammkrn/nanoda_lib).** The independent Rust kernel,
  version 0.4.13 without patches, accepted the same solution export. It runs
  inside Comparator with `enable_nanoda: true`; both kernels must accept.
  Result: `Nanoda kernel accepts the solution`.

These checks establish the Lean results under the listed assumptions. The
public reference and checking configuration are trusted inputs; correspondence
with the English descriptions and validity of the external assumptions require
mathematical review.

## Reproduce the checks

Run from the project root on macOS or Linux, with Lean/Lake, Git, a C toolchain,
and Rust/Cargo installed. Lean, Mathlib, Comparator, and lean4export revisions
are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

Prepare the verification tools once:

```sh
lake exe cache get
lake build comparator lean4export

git clone https://github.com/ammkrn/nanoda_lib.git .lake/nanoda
git -C .lake/nanoda checkout --detach 418320295890faed83a96fd97907b12a3b6728c2
cargo build --release --locked --manifest-path .lake/nanoda/Cargo.toml
```

Omit `git clone` when reusing the checkout. If the Mathlib cache download fails,
try `lake exe cache get --cache-from=legacy`. Tools and build products stay in `.lake/`.

Run the build, axiom audit, comparison, and both kernels:

```sh
lake build

export COMPARATOR_NANODA="$PWD/.lake/nanoda/target/release/nanoda_bin"
export COMPARATOR_LANDRUN="$PWD/.lake/packages/Comparator/scripts/fake-landrun.sh"
lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" exec comparator proofs/verification/comparator.json'
```

Both `lake build` and Comparator must exit with code zero. The build ends with
`Build completed successfully`; the audit and checker verdicts are listed above.

The `LEAN_PATH` prefix avoids a `main.lean`/`Main.lean` collision on
case-insensitive filesystems. The default command uses Comparator's portable
Landrun shim, which provides no OS sandbox and assumes trusted local sources.
On Linux, `COMPARATOR_LANDRUN` can instead point to a configured
[Landrun](https://github.com/Zouuup/landrun) executable.

To check for `sorryAx`, undeclared axioms, and changed theorem dependencies
separately after building:

```sh
lake env lean proofs/verification/Audit.lean
```

This reruns the same audit included in `lake build`.

## Project structure

```text
SymmetricCollisionRank/
├── main.lean                 seven public theorem statements
├── definitions.lean          23 public definitions
├── axioms.lean               seven external assumptions
├── README.md
├── lean-toolchain            Lean version
├── lakefile.toml             build targets and verification dependencies
├── lake-manifest.json        pinned dependency revisions
└── proofs/
    ├── CollisionRank/
    │   ├── Collision.lean    trees, products, collisions, and the abstract core
    │   ├── Orbit.lean        symbolic coordinates and permutations
    │   ├── Periodic.lean     periodic-window certificates and bounds
    │   ├── Symmetric.lean    symmetric chains and the rank bound
    │   ├── Axioms.lean       implementation copy of the external assumptions
    │   ├── Main.lean         final proofs and specializations
    │   └── Regression.lean   a concrete period-four model
    └── verification/
        ├── Audit.lean        axiom audit and exact theorem dependencies
        └── comparator.json  comparison targets and permitted axioms
```
