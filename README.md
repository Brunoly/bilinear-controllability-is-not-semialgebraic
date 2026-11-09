# Controllability of planar discrete-time bilinear systems is not semialgebraic

Proof that the set of controllable pairs for planar discrete-time bilinear systems is not semialgebraic. This repository also contains its Lean 4 formalization.

## Problem

For real $2\times2$ matrices $A,B$, consider the discrete-time plant

```math
x_{k+1}=(A+u_kB)x_k,\qquad u_k\in\mathbb{R}.
```

A pair $(A,B)$ is globally controllable if every nonzero state in
$\mathbb{R}^2$ can be steered to every nonzero target state in a positive
finite number of steps.

Can global controllability be characterized by a fixed finite combination of polynomial equalities and inequalities in the entries of $A,B$?

## Result

The set of controllable pairs is not semialgebraic, which means that no
fixed finite combination of polynomial equalities and inequalities in the
entries of $A,B$ can exactly characterize controllability. We also prove a
stronger result: this remains true even if the criterion only needs to work
for rational matrix entries. The polynomials may have arbitrary real coefficients.

## Proof and Lean formalization

[nonsemialgebraicity.md](docs/nonsemialgebraicity.md) contains the
written proof. The Lean formalization is in `BilinearSystems/`:
[definitions](BilinearSystems/Definitions.lean) and
[main theorems](BilinearSystems/PublicTheorems.lean).

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/Statements.lean
```

AI use: We used GPT-6 Astra Pro to find the proofs, and formalized the results in Lean using Astra and GPT Sol.

Bruno Yamamoto. Code: [Apache-2.0](LICENSE). Text: [CC BY 4.0](LICENSE-CC-BY-4.0).
