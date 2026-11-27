# Formalização em Lean 4 + Mathlib: Teoria Estrutural e Espectral da Conjectura de Černý

Biblioteca modular em **Lean 4 (v4.36.0) + Mathlib (v4.36.0)** formalizando a teoria estrutural, combinatória e espectral da Conjectura de Černý, com **zero `sorry`**, **zero `native_decide`** e **apenas os axiomas padrão do Lean** (`propext`, `Classical.choice`, `Quot.sound`).

## Estrutura de Módulos (12 Módulos + Raiz)

| # | Arquivo | Conteúdo Principal | Status |
|---|---|---|---|
| 0 | `Cerny/Defs.lean` | Definição de `Aut Q α`, `eval`, `image`, `preimage`, `IsSyncWord`, `IsSync`, `StronglyConnected` | Compilado |
| 1 | `Cerny/Reduction.lean` | Redução ao caso fortemente conexo (`cerny_reduction_to_strongly_connected`), inclusive $n=1$ | Compilado |
| 2 | `Cerny/CernyLowerBound.lean` | Família extrema $C_n$ e otimalidade $(n-1)^2$ (`cerny_lower_bound`) | Compilado |
| 3 | `Cerny/Monotonic.lean` | Autômatos monotônicos sobre ordem circular (`monotonic_cerny_bound`) | Compilado |
| 4 | `Cerny/PinFrankl.lean` | Limite cúbico de Pin–Frankl $\frac{n(n^2-1)}{6}$ sem álgebra exterior (`pin_frankl_bound`) | Compilado |
| 5 | `Cerny/KrylovEulerian.lean` | Lema de Krylov e Teorema de Kari para Eulerianos $(n-1)^2$ (`kari_eulerian_bound`) | Compilado |
| 6 | `Cerny/Aperiodic.lean` | Autômatos aperiódicos com limite aprimorado $\lceil \frac{3}{4}(n-1)^2 \rceil$ (`aperiodic_bound`) | Compilado |
| 7 | `Cerny/WeightedPrimeCycle.lean` | Lema de passo inicial multi-cluster e pesos sobre ciclos primos | Compilado |
| 8 | `Cerny/BalancedPermutations.lean` | Família de autômatos balanceados por permutação (`prime_order_balanced_cerny`, `coprime_step_balanced_cerny`) | Compilado |
| 9 | `Cerny/CircularDubuc.lean` | Cancelamento anular por recorrência pura (`annular_cancellation`) e `span_orbit_mod_subspace` | Compilado |
| 10 | `Cerny/OneClusterAnnular.lean` | Teorema completo de *one-cluster* composto (`one_cluster_cerny_bound`) e Teorema Circular de Dubuc (`dubuc_circular_bound`) | Compilado |
| 11 | `Cerny/Counterexamples.lean` | 5 contraexemplos verificados na fronteira *two-cluster* via certificados de bitmask e `decide` | Compilado |
| — | `Cerny.lean` | Módulo raiz importando todos os 12 módulos | Compilado |

## Teoremas Principais Verificados

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

## Como Compilar

```powershell
lake build
```

