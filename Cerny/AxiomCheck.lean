import Cerny

/-!
# Axiom audit

`#print axioms` on every main theorem of the library. The expected output
for each theorem is exactly `[propext, Classical.choice, Quot.sound]`.
The CI workflow `lean_action_ci.yml` turns this report into an automated
audit seal: any additional axiom makes the check fail.
-/

#print axioms Aut.cerny_reduction_to_strongly_connected
#print axioms CernyLowerBound.cerny_lower_bound
#print axioms Monotonic.monotonic_cerny_bound
#print axioms PinFrankl.pin_frankl_bound
#print axioms KrylovEulerian.kari_eulerian_bound
#print axioms Aperiodic.aperiodic_bound
#print axioms BalancedPermutations.prime_order_balanced_cerny
#print axioms BalancedPermutations.coprime_step_balanced_cerny
#print axioms Cerny.OneClusterAnnular.one_cluster_cerny_bound
#print axioms Cerny.OneClusterAnnular.dubuc_circular_bound
#print axioms BalancedPermutations.antisymmetric_balanced_cerny
#print axioms BalancedPermutations.balanced_cerny_of_annihilator_and_pos_multiple
#print axioms BalancedPermutations.phi4_high_dim_balanced_cerny
#print axioms BalancedPermutations.phi6_high_dim_balanced_cerny
#print axioms WeightedPrimeCycle.one_cluster_prime_bound
#print axioms Cerny.OneClusterAnnular.one_cluster_steinberg_bound
#print axioms Cerny.Counterexamples.two_cluster_34_counterexample
#print axioms Cerny.Counterexamples.balanced_124_counterexample
#print axioms Cerny.Counterexamples.balanced_16_counterexample
#print axioms Cerny.Counterexamples.balanced_16_step2_counterexample
#print axioms Cerny.Counterexamples.multi_cluster_trees_counterexample
