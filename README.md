# Gödelian Recursive Incompleteness — Lean 4 Phase 1 verification

This is the **public, minimal verification companion** to Adrian Diamond's research manuscript,
*Gödelian Recursive Incompleteness: Dynamics, Extension, and Invariants of Formal Systems* (2026).

## Precisely what is verified

The Lean project contains **six selected supporting theorems** in two modules:

| Source file | Theorem | Mathematical scope |
|---|---|---|
| `AADCertification/ConcreteTransport.lean` | `proof_transport` | Proof transport in an explicitly defined Hilbert implication calculus |
| same | `redundant_axiom` | Redundant axiom adjunction |
| same | `adjoin_congruence` | Derivability preserved under certified axiom replacement |
| same | `appending_tautology_changes_nothing` | A concrete redundant-tautology example |
| `AADCertification/AbstractInvariance.lean` | `ctxEq_iff_provEq` | Equivalence under stated abstract framework assumptions |
| same | `indefinite_contextual_invariance` | Conditional finite-stage invariance under stated framework assumptions |

The four highlighted concrete theorems have no Lean axioms in their printed dependencies.
The two highlighted abstract theorems use standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`).

**Important limitation:** These are supporting structural results, **not** a Lean formalization of
Peano arithmetic or of the manuscript's Gödelian non-descent, infinite-chain, arbitrary-delay,
or contextual-consistency arithmetic theorems. The `Framework` fields explicitly *assume* the
relevant arithmetic obligations; those fields are not proofs of the obligations in PA.

This public repository contains only Phase 1. No experimental Phase 2 code or private
development history is included.

## Reproduce the checks

The toolchain is pinned to Lean `v4.23.0`, with no Mathlib dependency.

```bash
lake build
bash run_checks.sh
```

The GitHub **Actions** tab runs the same project checks after changes to `main`.
A green run confirms the checked Lean declarations in this repository; it does not mean
that the entire mathematical manuscript has been machine-verified or independently refereed.

## Source and attribution

Research manuscript: Adrian Diamond, AAD Systems (2026).
This repository deliberately has no open-source license yet. Public visibility permits
inspection, but it is not a grant of unrestricted reuse. Licensing may be specified later.
