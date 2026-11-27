# Lean 4 + Mathlib Formalization: Structural and Spectral Theory of the Černý Conjecture

A modular library in **Lean 4 (v4.36.0) + Mathlib (v4.36.0)** formalizing the structural,
combinatorial, and spectral theory of the Černý conjecture, with **zero `sorry`**,
**zero `native_decide`**, and **only the standard Lean axioms**
(`propext`, `Classical.choice`, `Quot.sound`).

## Module Structure (12 Modules + Root)

| # | File | Main Content | Status |
|---|------|--------------|--------|
| 0 | `Cerny/Defs.lean` | Definition of `Aut Q α`, `eval`, `image`, `preimage`, `IsSyncWord`, `IsSync`, `StronglyConnected` | Built |
| 1 | `Cerny/Reduction.lean` | Reduction to the strongly connected case (`cerny_reduction_to_strongly_connected`), including $n=1$ | Built |
| 2 | `Cerny/CernyLowerBound.lean` | Extremal family $C_n$ and optimality of $(n-1)^2$ (`cerny_lower_bound`) | Built |
| 3 | `Cerny/Monotonic.lean` | Monotonic automata over a circular order (`monotonic_cerny_bound`) | Built |
| 4 | `Cerny/PinFrankl.lean` | Pin–Frankl cubic bound $\frac{n(n^2-1)}{6}$ without exterior algebra (`pin_frankl_bound`) | Built |
| 5 | `Cerny/KrylovEulerian.lean` | Krylov lemma and Kari's theorem for Eulerian automata $(n-1)^2$ (`kari_eulerian_bound`) | Built |
| 6 | `Cerny/Aperiodic.lean` | Aperiodic automata with the improved bound $\lceil \frac{3}{4}(n-1)^2 \rceil$ (`aperiodic_bound`) | Built |
| 7 | `Cerny/WeightedPrimeCycle.lean` | Multi-cluster initial step lemma and weights over prime cycles | Built |
| 8 | `Cerny/BalancedPermutations.lean` | Permutation-balanced automata family (`prime_order_balanced_cerny`, `coprime_step_balanced_cerny`) | Built |
| 9 | `Cerny/CircularDubuc.lean` | Annular cancellation by pure recurrence (`annular_cancellation`) and `span_orbit_mod_subspace` | Built |
| 10 | `Cerny/OneClusterAnnular.lean` | Full composite one-cluster theorem (`one_cluster_cerny_bound`) and Dubuc's circular theorem (`dubuc_circular_bound`) | Built |
| 11 | `Cerny/Counterexamples.lean` | 5 verified counterexamples on the *two-cluster* frontier via bitmask certificates and `decide` | Built |
| — | `Cerny.lean` | Root module importing all 12 modules | Built |

## Main Verified Theorems

- `Aut.cerny_reduction_to_strongly_connected`
- `CernyLowerBound.cerny_lower_bound`
- `Monotonic.monotonic_cerny_bound`
- `PinFrankl.pin_frankl_bound`
- `KrylovEulerian.kari_eulerian_bound`
- `Aperiodic.aperiodic_bound`
- `BalancedPermutations.prime_order_balanced_cerny`
- `BalancedPermutations.coprime_step_balanced_cerny`
- `Cerny.OneClusterAnnular.dubuc_circular_bound`
- `Cerny.OneClusterAnnular.one_cluster_cerny_bound`
- `Cerny.Counterexamples.two_cluster_34_counterexample`
- `Cerny.Counterexamples.balanced_124_counterexample`
- `Cerny.Counterexamples.balanced_16_counterexample`
- `Cerny.Counterexamples.balanced_16_step2_counterexample`
- `Cerny.Counterexamples.multi_cluster_trees_counterexample`

## Building

```powershell
lake build
```

## Axiom Audit

The file `Cerny/AxiomCheck.lean` prints, via `#print axioms`, the axiomatic
dependencies of every main theorem. The CI workflow (`lean_action_ci.yml`) runs
this report and fails if any axiom outside `[propext, Classical.choice, Quot.sound]`
appears.

```powershell
lake env lean Cerny/AxiomCheck.lean
```
