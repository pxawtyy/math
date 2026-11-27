import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Cerny.Defs
import Cerny.Linear
import Cerny.CircularDubuc
import Cerny.KrylovEulerian

/-!
# Balanced Permutations: Unified Master Theorems (Versions A & B)

This module proves the full-strength multi-cycle balanced permutation theorems over `ℚ`
(for arbitrary composite `n = |Q|` and arbitrary number of cycles of `a`):

1. `master_balanced_version_A` (Theorem 11.6): strictly positive annihilator `c₀, ..., c_D > 0`
   on `K₀'` implies `(n + D - d₀)`-extensibility.
2. `master_balanced_version_B` (Theorem 12.1): nonnegative annihilator `c_j ≥ 0, c₀ > 0`
   on `K₀'` implies `(n + D - 1)`-extensibility.
3. `IsCycleBalanced`: true multi-cycle balance (`|(orbit a q) · b⁻¹| = |orbit a q|` for all `b, q`).
4. `prime_order_balanced_cerny` (Corollary 11.7): full Černý bound `(n - 1)^2` for EVERY
   cycle-balanced permutation `a` of prime order `p` (arbitrary number of 1-cycles and p-cycles,
   including all involutions `p = 2`!).
5. `coprime_step_balanced_cerny` (Theorem 12.2): full Černý bound `(n - 1)^2` for arbitrary
   composite order `m` when some letter has a single collision of coprime step `gcd(s, m) = 1`.
6. `antisymmetric_balanced_cerny` (Corollary 11.9): `R A [a] (ρ A [b]) = -ρ A [b]` implies `(n - 1)^2`.
7. `phi6_l1_norm_ge_four` (Lemma 12.3): `‖v‖₁ ≥ 4` for nonzero integer vectors in `ker Φ₆`.
-/

namespace BalancedPermutations

open KrylovEulerian

section RightAction
variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Right-action pushforward operator `(R A w x) q = ∑_{p · w = q} x p` on `Q → ℚ`.
This is the specialization of `Cerny.Linear.rowAct` to `ℚ`. -/
abbrev R (A : Aut Q α) (w : List α) : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) :=
  Cerny.Linear.rowAct ℚ A w

@[simp]
lemma R_nil (A : Aut Q α) : R A [] = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact Cerny.Linear.rowAct_nil ℚ A f

lemma R_append (A : Aut Q α) (u v : List α) :
    R A (u ++ v) = R A v ∘ₗ R A u := by
  apply LinearMap.ext
  intro f
  exact Cerny.Linear.rowAct_append ℚ A u v f

lemma R_cons (A : Aut Q α) (a : α) (w : List α) :
    R A (a :: w) = R A w ∘ₗ R A [a] := by
  rw [← List.singleton_append, R_append]

lemma R_replicate_eq_pow (A : Aut Q α) (a : α) (j : ℕ) :
    (R A [a]) ^ j = R A (List.replicate j a) := by
  induction j with
  | zero => simp [R_nil]; rfl
  | succ j ih =>
    rw [pow_succ', ih, List.replicate_succ', R_append]
    rfl

lemma R_replicate_eq_iterate (A : Aut Q α) (a : α) (j : ℕ) (x : Q → ℚ) :
    R A (List.replicate j a) x = ((R A [a])^[j]) x :=
  Cerny.Linear.rowAct_eq_iterate ℚ A a j x

/-- Zero-sum hyperplane `K₀ Q = ker (sumLin Q)` of dimension `n - 1`. -/
abbrev K₀ (Q : Type*) [Fintype Q] : Submodule ℚ (Q → ℚ) :=
  LinearMap.ker (sumLin Q)

lemma sumLin_R (A : Aut Q α) (w : List α) (x : Q → ℚ) :
    sumLin Q (R A w x) = sumLin Q x := by
  change (∑ q : Q, (Cerny.Linear.rowAct ℚ A w x) q) = ∑ q : Q, x q
  exact Cerny.Linear.sum_rowAct ℚ A w x

/-- Defect row vector `ρ A w = R A w 1 - 1 ∈ K₀ Q`. -/
def ρ (A : Aut Q α) (w : List α) : Q → ℚ :=
  fun q => ((A.preimage {q} w).card : ℚ) - 1

lemma ρ_eq_R_ones_sub (A : Aut Q α) (w : List α) :
    ρ A w = R A w (fun _ => 1) - (fun _ => 1) := by
  ext q
  simp only [ρ, Pi.sub_apply]
  rw [show (R A w) (fun _ => (1 : ℚ)) q = ((A.preimage {q} w).card : ℚ) from
    Cerny.Linear.rowAct_one_apply ℚ A w q]

lemma ρ_mem_K0 (A : Aut Q α) (w : List α) : ρ A w ∈ K₀ Q := by
  rw [LinearMap.mem_ker, ρ_eq_R_ones_sub, map_sub, sumLin_R, sub_self]

lemma R_ones_eq_ones_of_bij (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) :
    R A [a] (fun _ => 1) = (fun _ => 1) :=
  Cerny.Linear.rowAct_ones_eq_ones_of_bij ℚ A hbij

lemma ρ_a_eq_zero_of_bij (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) :
    ρ A [a] = 0 := by
  rw [ρ_eq_R_ones_sub, R_ones_eq_ones_of_bij A hbij, sub_self]

lemma ρ_cons_a_of_bij (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (w : List α) :
    ρ A (a :: w) = ρ A w := by
  rw [ρ_eq_R_ones_sub, R_cons, LinearMap.comp_apply, R_ones_eq_ones_of_bij A hbij,
      ← ρ_eq_R_ones_sub]

lemma ρ_append_single (A : Aut Q α) (w : List α) (σ : α) :
    R A [σ] (ρ A w) = ρ A (w ++ [σ]) - ρ A [σ] := by
  rw [ρ_eq_R_ones_sub, ρ_eq_R_ones_sub, ρ_eq_R_ones_sub, map_sub, ← LinearMap.comp_apply,
      ← R_append]
  abel

lemma ρ_append_replicate_a (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (w : List α) (j : ℕ) :
    R A (List.replicate j a) (ρ A w) = ρ A (w ++ List.replicate j a) := by
  induction j with
  | zero => simp [R_nil]
  | succ j ih =>
    rw [List.replicate_succ', R_append, LinearMap.comp_apply, ih, ρ_append_single,
        ρ_a_eq_zero_of_bij A hbij, sub_zero, List.append_assoc]

lemma sum_ρ_subset (A : Aut Q α) (w : List α) (S : Finset Q) :
    ∑ q ∈ S, ρ A w q = ((A.preimage S w).card : ℚ) - (S.card : ℚ) := by
  simp only [ρ, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hpart : ∑ q ∈ S, (A.preimage {q} w).card = (A.preimage S w).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext p; simp [Aut.mem_preimage]
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpx hpy
      simp only [Aut.mem_preimage, Finset.mem_singleton] at hpx hpy
      exact hxy (hpx.symm.trans hpy)
  exact_mod_cast hpart

/-- Dot product of a row vector `x ∈ K₀ Q` with the indicator of `S`. -/
def evalSubset (S : Finset Q) : (Q → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ q ∈ S, x q
  map_add' x y := Finset.sum_add_distrib
  map_smul' c x := by simp [Finset.mul_sum]

lemma evalSubset_ρ (A : Aut Q α) (w : List α) (S : Finset Q) :
    evalSubset S (ρ A w) = ((A.preimage S w).card : ℚ) - (S.card : ℚ) :=
  sum_ρ_subset A w S

/-- The right-Krylov base subspace `K₀' A a = span { ρ(b · a^j) | b ≠ a, j : ℕ } ≤ K₀ Q`. -/
def K₀' (A : Aut Q α) (a : α) : Submodule ℚ (Q → ℚ) :=
  Submodule.span ℚ {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ x = ρ A (b :: List.replicate j a)}

lemma K₀'_le_K0 (A : Aut Q α) (a : α) : K₀' A a ≤ K₀ Q := by
  rw [K₀', Submodule.span_le]
  rintro _ ⟨b, j, _, rfl⟩
  exact ρ_mem_K0 A _

lemma ρ_single_mem_K₀' (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) (σ : α) :
    ρ A [σ] ∈ K₀' A a := by
  by_cases hσ : σ = a
  · subst hσ; rw [ρ_a_eq_zero_of_bij A hbij]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨σ, 0, hσ, by simp⟩

lemma K₀'_R_a_inv (A : Aut Q α) {a : α}
    (hbij : Function.Bijective (fun q => A.step q a)) {x : Q → ℚ} (hx : x ∈ K₀' A a) :
    R A [a] x ∈ K₀' A a := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨b, j, hba, rfl⟩
    rw [ρ_append_single, ρ_a_eq_zero_of_bij A hbij, sub_zero]
    have hrew : (b :: List.replicate j a) ++ [a] = b :: List.replicate (j + 1) a := by
      rw [List.cons_append, ← List.replicate_succ']
    rw [hrew]
    exact Submodule.subset_span ⟨b, j + 1, hba, rfl⟩
  | zero => simp
  | add _ _ _ _ ih1 ih2 => rw [map_add]; exact Submodule.add_mem _ ih1 ih2
  | smul c _ _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

/-- If `A` is synchronizing, `a` is bijective and `2 ≤ |Q|`, then some letter `b ≠ a`
has nonzero defect `ρ A [b]`. -/
lemma exists_defect_letter_of_isSync [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (a : α) (hbij : Function.Bijective (fun q => A.step q a))
    (hn2 : 2 ≤ Fintype.card Q) : ∃ b : α, b ≠ a ∧ ρ A [b] ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := A.exists_nonbijective_letter hsync hn2
  refine ⟨b, ?_, ?_⟩
  · intro hba
    subst hba
    exact hb hbij
  · intro hρ0
    apply hb
    have hsurj : Function.Surjective (fun q => A.step q b) := by
      intro q
      have hq := congrFun hρ0 q
      simp only [ρ, Pi.zero_apply, sub_eq_zero] at hq
      have hcard : (A.preimage {q} [b]).card = 1 := by exact_mod_cast hq
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (A.preimage {q} [b]).card)
      exact ⟨p, by simpa [Aut.mem_preimage] using hp⟩
    exact Finite.surjective_iff_bijective.mp hsurj

/-- The right-Krylov subspace `K₀' A a` is nontrivial for a synchronizing automaton
with at least two states and a bijective letter `a`. -/
lemma K₀'_ne_bot_of_isSync [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (a : α) (hbij : Function.Bijective (fun q => A.step q a))
    (hn2 : 2 ≤ Fintype.card Q) : K₀' A a ≠ ⊥ := by
  intro hbot
  obtain ⟨b, hba, hρ⟩ := exists_defect_letter_of_isSync A hsync a hbij hn2
  have hmem : ρ A [b] ∈ K₀' A a := Submodule.subset_span ⟨b, 0, hba, by simp⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hρ hmem

lemma one_le_finrank_K₀'_of_isSync [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (a : α) (hbij : Function.Bijective (fun q => A.step q a))
    (hn2 : 2 ≤ Fintype.card Q) : 1 ≤ Module.finrank ℚ (K₀' A a) := by
  have hne := K₀'_ne_bot_of_isSync A hsync a hbij hn2
  have hlt := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hne)
  rw [finrank_bot] at hlt
  omega

/-- Quotient-free Cayley–Hamilton over `ℚ`: inside an `T`-invariant subspace `W` of dimension `d`,
every orbit `(T^[k]) x` lies in `span { (T^[j]) x | j < d }`. This is the specialization of
`Cerny.CircularDubuc.span_orbit_mod_subspace` to the quotient by `⊥`. -/
lemma span_orbit_le_finrank_Q {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (T : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hTW : ∀ x ∈ W, T x ∈ W)
    (x : V) (hx : x ∈ W) (k : ℕ) :
    (T^[k]) x ∈ Submodule.span ℚ {y | ∃ j < Module.finrank ℚ W, y = (T^[j]) x} := by
  have hbot : ∀ y ∈ (⊥ : Submodule ℚ V), T y ∈ (⊥ : Submodule ℚ V) := by
    intro y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy]
    simp
  have h := Cerny.CircularDubuc.span_orbit_mod_subspace T (⊥ : Submodule ℚ V) W bot_le
    hbot hTW x hx k
  simpa [finrank_bot] using h

end RightAction

section MasterTheorems
variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Helper: given `(n - 1)`-extensibility or `n`-extensibility for all `1 ≤ |S| < n`,
assemble a synchronizing word of length `≤ (n - 1)^2` from `1 + (n - 2) * n`. -/
lemma cerny_of_n_extensible [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (hext : ∀ S : Finset Q, 1 ≤ S.card → S.card < Fintype.card Q →
      ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let n := Fintype.card Q
  have hn_pos : 1 ≤ n := Fintype.card_pos
  by_cases hn1 : n = 1
  · haveI : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨[], Aut.isSyncWord_nil_of_subsingleton A, by simp⟩
  have hn2 : 2 ≤ n := by omega
  -- Step 1: some letter `b₀` is not injective, giving `|{c₀} · b₀⁻¹| ≥ 2` in length `1`
  have hinit : ∃ c₀ : Q, ∃ b₀ : α, 2 ≤ (A.preimage {c₀} [b₀]).card :=
    A.exists_collision_letter_of_isSync hsync (by simpa [n] using hn2)
  obtain ⟨c₀, b₀, hc₀_card⟩ := hinit
  let S₁ := A.preimage {c₀} [b₀]
  have hgrow : ∀ d : ℕ, ∀ S : Finset Q, ∀ v : List α,
      S.card + d = n → 2 ≤ S.card → S ⊆ A.preimage {c₀} v →
      v.length ≤ 1 + (S.card - 2) * n →
      ∃ w : List α, A.preimage {c₀} w = Finset.univ ∧ w.length ≤ 1 + (n - 2) * n := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro S v hd hS2 hSv hv_len
      by_cases hd0 : d = 0
      · subst hd0
        have hS_univ : S = Finset.univ := Finset.eq_univ_of_card S (by omega)
        rw [hS_univ] at hSv
        refine ⟨v, Finset.eq_univ_iff_forall.mpr fun q => hSv (Finset.mem_univ q), ?_⟩
        rwa [show S.card = n by omega] at hv_len
      · obtain ⟨u, hu_len, hu_gt⟩ := hext S (by omega) (by omega)
        let S' := A.preimage S u
        have hS'_pre : S' ⊆ A.preimage {c₀} (u ++ v) := by
          rw [← Aut.preimage_append]; exact A.preimage_mono hSv u
        have hd' : S'.card + (n - S'.card) = n := by
          have := Finset.card_le_univ S'; dsimp only [S', n] at *; omega
        have hlen' : (u ++ v).length ≤ 1 + (S'.card - 2) * n := by
          rw [List.length_append]
          have hmul1 : (S.card - 2) * n + n = (S.card - 1) * n := by
            have : S.card - 2 + 1 = S.card - 1 := by omega
            calc (S.card - 2) * n + n = (S.card - 2 + 1) * n := by ring
              _ = (S.card - 1) * n := by rw [this]
          have hmul2 : (S.card - 1) * n ≤ (S'.card - 2) * n := Nat.mul_le_mul_right n (by dsimp only [S'] at *; omega)
          dsimp only [S', n] at hu_len hmul1 hmul2 hv_len ⊢
          omega
        exact ih (n - S'.card) (by dsimp only [S', n] at *; omega) S' (u ++ v) hd'
          (by dsimp only [S'] at *; omega) hS'_pre hlen'
  obtain ⟨w, hw_pre, hw_len⟩ :=
    hgrow (n - S₁.card) S₁ [b₀] (by have := Finset.card_le_univ S₁; omega) hc₀_card
      (Finset.Subset.refl _) (by simp)
  refine ⟨w, (Aut.isSyncWord_iff_preimage_univ A).mpr ⟨c₀, hw_pre⟩, ?_⟩
  have harith : 1 + (n - 2) * n = (n - 1) ^ 2 := by zify [hn2, hn_pos]; ring
  exact le_trans hw_len (le_of_eq harith)

/-- Core shared step for Master Theorems A and B:
Given `a` bijective and `J : ℕ` such that `{ρ(b · a^j) | b ≠ a, j ≤ J}` spans `K₀' A a`,
there exist `t ≤ n - 1 - dim K₀'`, `b ≠ a`, `j* ≤ J`, and `|u| ≤ t` such that
`|S · u⁻¹| = |S|` and `|S · (b · a^{j*} · u)⁻¹| ≠ |S|`. -/
private lemma right_krylov_detect [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (J : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    {S : Finset Q} (hS_pos : 1 ≤ S.card) (hS_lt : S.card < Fintype.card Q) :
    ∃ (b : α) (j_star : ℕ) (u : List α),
      b ≠ a ∧ j_star ≤ J ∧ u.length ≤ Fintype.card Q - 1 - Module.finrank ℚ (K₀' A a) ∧
      (A.preimage S u).card = S.card ∧
      (A.preimage S (b :: List.replicate j_star a ++ u)).card ≠ S.card := by
  classical
  let n := Fintype.card Q
  let d₀ := Module.finrank ℚ (K₀' A a)
  let K : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
    Submodule.span ℚ {x | ∃ (b : α) (j : ℕ) (u : List α),
      b ≠ a ∧ j ≤ J ∧ u.length ≤ t ∧ x = ρ A (b :: List.replicate j a ++ u)}
  have hK0 : K 0 = K₀' A a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, j, u, hba, _, hu0, rfl⟩
      have hnil : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil, List.append_nil]; exact Submodule.subset_span ⟨b, j, hba, rfl⟩
    · refine hspan.trans (Submodule.span_mono ?_)
      rintro _ ⟨b, j, hba, hjJ, rfl⟩
      exact ⟨b, j, [], hba, hjJ, by simp, by simp⟩
  have hK_mono : ∀ t, K t ≤ K (t + 1) := fun t =>
    Submodule.span_mono (by rintro _ ⟨b, j, u, h1, h2, h3, rfl⟩; exact ⟨b, j, u, h1, h2, by omega, rfl⟩)
  have hK_le_K0 : ∀ t, K t ≤ K₀ Q := fun t => by
    rw [Submodule.span_le]; rintro _ ⟨_, _, _, _, _, _, rfl⟩; exact ρ_mem_K0 A _
  have hK_step : ∀ t (σ : α) (x : Q → ℚ), x ∈ K t → R A [σ] x ∈ K (t + 1) := by
    intro t σ x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨b, j, u, hba, hjJ, hut, rfl⟩
      rw [ρ_append_single]
      refine Submodule.sub_mem _ ?_ ?_
      · refine Submodule.subset_span ⟨b, j, u ++ [σ], hba, hjJ, by simp; omega, ?_⟩
        rw [List.append_assoc]
      · have h0 : ρ A [σ] ∈ K 0 := by rw [hK0]; exact ρ_single_mem_K₀' A hbij σ
        have hle : K 0 ≤ K (t + 1) := by
          clear h0
          induction (t + 1) with
          | zero => exact le_rfl
          | succ m ihm => exact ihm.trans (hK_mono m)
        exact hle h0
    | zero => simp
    | add _ _ _ _ ih1 ih2 => rw [map_add]; exact Submodule.add_mem _ ih1 ih2
    | smul c _ _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih
  -- Every word `u` of length `≤ t` (`t ≥ 1`) satisfies `ρ A u ∈ K (t - 1)`
  have hρ_short : ∀ (t : ℕ) (ht : 1 ≤ t) (u : List α), u.length ≤ t → ρ A u ∈ K (t - 1) := by
    intro t ht u hu
    induction u with
    | nil =>
      have : ρ A [] = 0 := by ext q; simp [ρ, Aut.preimage_nil]
      rw [this]; exact Submodule.zero_mem _
    | cons σ rest ih =>
      by_cases hσ : σ = a
      · subst hσ; rw [ρ_cons_a_of_bij A hbij]; exact ih (by simp at hu; omega)
      · refine Submodule.subset_span ⟨σ, 0, rest, hσ, Nat.zero_le J, by simp at hu; omega, ?_⟩
        simp
  -- Show `¬ (K (n - 1 - d₀) ≤ ker (evalSubset S))`
  let E_S := LinearMap.ker (evalSubset S)
  have hK_not_ker : ¬ (K (n - 1 - d₀) ≤ E_S) := by
    intro hle_ES
    have hd₀_le : d₀ ≤ n - 1 := by
      have h1 := Submodule.finrank_mono (K₀'_le_K0 A a)
      rw [finrank_ker_sumLin] at h1
      exact h1
    -- Either `K r = K (r + 1)` for some `r < n - 1 - d₀`, or `K (n - 1 - d₀) = K₀ Q`
    have hK_all_ρ : ∀ w : List α, ρ A w ∈ K (n - 1 - d₀) := by
      by_cases hstab : ∃ r < n - 1 - d₀, K r = K (r + 1)
      · obtain ⟨r, hr_lt, hr_eq⟩ := hstab
        have hinv : ∀ (σ : α) (x : Q → ℚ), x ∈ K r → R A [σ] x ∈ K r :=
          fun σ x hx => hr_eq ▸ hK_step r σ x hx
        have hKr_le : K r ≤ K (n - 1 - d₀) := by
          have hrec : ∀ m, r ≤ m → K r ≤ K m := by
            intro m hm
            induction m with
            | zero =>
              have hr0 : r = 0 := by omega
              rw [hr0]
            | succ m ihm =>
              rcases eq_or_lt_of_le hm with rfl | hlt
              · exact le_rfl
              · exact (ihm (by omega)).trans (hK_mono m)
          exact hrec (n - 1 - d₀) (le_of_lt hr_lt)
        intro w
        apply hKr_le
        induction w using List.reverseRecOn with
        | nil =>
          have : ρ A [] = 0 := by ext q; simp [ρ, Aut.preimage_nil]
          rw [this]; exact Submodule.zero_mem _
        | append_singleton w σ ihw =>
          have h1 := hinv σ _ ihw
          rw [ρ_append_single] at h1
          have hσ_in : ρ A [σ] ∈ K r := by
            have h0 : ρ A [σ] ∈ K 0 := by rw [hK0]; exact ρ_single_mem_K₀' A hbij σ
            have h0r : K 0 ≤ K r := by
              clear h0 hr_lt hr_eq hinv hKr_le ihw h1
              induction r with
              | zero => exact le_rfl
              | succ m ihm => exact ihm.trans (hK_mono m)
            exact h0r h0
          simpa using Submodule.add_mem (K r) h1 hσ_in
      · push_neg at hstab
        have hgrow : ∀ m ≤ n - 1 - d₀, d₀ + m ≤ Module.finrank ℚ (K m) := by
          intro m hm
          induction m with
          | zero => rw [hK0, add_zero]
          | succ m ihm =>
            have hlt := Submodule.finrank_lt_finrank_of_lt
              (lt_of_le_of_ne (hK_mono m) (hstab m (by omega)))
            have := ihm (by omega)
            omega
        have htop : K (n - 1 - d₀) = K₀ Q := by
          apply Submodule.eq_of_le_of_finrank_eq (hK_le_K0 _)
          have hge := hgrow (n - 1 - d₀) le_rfl
          have hle := Submodule.finrank_mono (hK_le_K0 (n - 1 - d₀))
          rw [finrank_ker_sumLin] at hle ⊢
          omega
        intro w; rw [htop]; exact ρ_mem_K0 A w
    -- Contradict using a synchronizing word `w₀`
    obtain ⟨w₀, hw₀⟩ := hsync
    rw [Aut.isSyncWord_iff_exists_eval_eq] at hw₀
    obtain ⟨c_star, hc_star⟩ := hw₀
    have h0 : evalSubset S (ρ A w₀) = 0 := hle_ES (hK_all_ρ w₀)
    rw [evalSubset_ρ] at h0
    by_cases hc : c_star ∈ S
    · have hpre : A.preimage S w₀ = Finset.univ := by ext q; simp [hc_star q, hc]
      rw [hpre, Finset.card_univ] at h0
      have : (n : ℚ) = (S.card : ℚ) := by linarith
      have : n = S.card := Nat.cast_injective this
      omega
    · have hpre : A.preimage S w₀ = ∅ := by ext q; simp [hc_star q, hc]
      rw [hpre, Finset.card_empty] at h0
      simp only [Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero] at h0
      omega
  -- Choose minimal `t ≤ n - 1 - d₀` such that `¬ (K t ≤ E_S)`
  have hex_t : ∃ t, ¬ (K t ≤ E_S) := ⟨n - 1 - d₀, hK_not_ker⟩
  let t := Nat.find hex_t
  have ht_le : t ≤ n - 1 - d₀ := Nat.find_min' hex_t hK_not_ker
  have ht_not : ¬ (K t ≤ E_S) := Nat.find_spec hex_t
  -- Extract a generator of `K t` outside `E_S`
  have hex_gen : ∃ (b : α) (j_star : ℕ) (u : List α),
      b ≠ a ∧ j_star ≤ J ∧ u.length ≤ t ∧ evalSubset S (ρ A (b :: List.replicate j_star a ++ u)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply ht_not
    rw [Submodule.span_le]
    rintro _ ⟨b, j, u, h1, h2, h3, rfl⟩
    exact hall b j u h1 h2 h3
  obtain ⟨b, j_star, u, hba, hjJ, hut, hne0⟩ := hex_gen
  refine ⟨b, j_star, u, hba, hjJ, le_trans hut ht_le, ?_, ?_⟩
  · by_cases ht0 : t = 0
    · have hnil : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hnil, Aut.preimage_nil]
    · have hprev : K (t - 1) ≤ E_S := by
        by_contra hnot; exact Nat.find_min hex_t (by omega : t - 1 < t) hnot
      have h0 : evalSubset S (ρ A u) = 0 := hprev (hρ_short t (by omega) u hut)
      rw [evalSubset_ρ, sub_eq_zero] at h0
      exact Nat.cast_injective h0
  · intro heq
    apply hne0
    rw [evalSubset_ρ, heq, sub_self]

/-- Any degree-`g` (`g ≥ 1`) polynomial with nonzero leading coefficient annihilating `K₀' A a`
forces `{ρ(b · a^j) | b ≠ a, j ≤ g - 1}` to span `K₀' A a`. -/
lemma K₀'_span_of_annihilator (A : Aut Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (g : ℕ) (hg : 1 ≤ g) (p : Fin (g + 1) → ℚ) (hp_top : p (Fin.last g) ≠ 0)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (g + 1), p j • R A (List.replicate j.1 a) x = 0) :
    K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ g - 1 ∧ x = ρ A (b :: List.replicate j a)} := by
  let W := Submodule.span ℚ
    {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ g - 1 ∧ x = ρ A (b :: List.replicate j a)}
  have hrec : ∀ (b : α) (hba : b ≠ a) (r : ℕ), ρ A (b :: List.replicate r a) ∈ W := by
    intro b hba r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      by_cases hrg : r ≤ g - 1
      · exact Submodule.subset_span ⟨b, r, hba, hrg, rfl⟩
      · have hx_mem : ρ A (b :: List.replicate (r - g) a) ∈ K₀' A a :=
          Submodule.subset_span ⟨b, r - g, hba, rfl⟩
        have h0 := hann _ hx_mem
        rw [Fin.sum_univ_castSucc] at h0
        have hlast_eq : R A (List.replicate g a) (ρ A (b :: List.replicate (r - g) a)) =
            ρ A (b :: List.replicate r a) := by
          rw [ρ_append_replicate_a A hbij, List.cons_append, ← List.replicate_add,
              Nat.sub_add_cancel (by omega)]
        rw [Fin.val_last, hlast_eq] at h0
        have hsolve : ρ A (b :: List.replicate r a) =
            -(p (Fin.last g))⁻¹ •
              ∑ j : Fin g, p j.castSucc •
                R A (List.replicate j.1 a) (ρ A (b :: List.replicate (r - g) a)) := by
          have h1 : p (Fin.last g) • ρ A (b :: List.replicate r a) =
              - ∑ j : Fin g, p j.castSucc •
                  R A (List.replicate j.1 a) (ρ A (b :: List.replicate (r - g) a)) :=
            eq_neg_of_add_eq_zero_right h0
          calc ρ A (b :: List.replicate r a)
              = (p (Fin.last g))⁻¹ • (p (Fin.last g) • ρ A (b :: List.replicate r a)) := by
                  rw [smul_smul, inv_mul_cancel₀ hp_top, one_smul]
            _ = _ := by rw [h1, smul_neg, neg_smul]
        rw [hsolve]
        refine Submodule.smul_mem W _ (Submodule.sum_mem W fun j _ => Submodule.smul_mem W _ ?_)
        rw [ρ_append_replicate_a A hbij, List.cons_append, ← List.replicate_add]
        exact ih (r - g + j.1) (by omega)
  rw [K₀', Submodule.span_le]
  rintro _ ⟨b, r, hba, rfl⟩
  exact hrec b hba r

/-- **Master Theorem (Version A — Theorem 11.6):**
If `a` is a bijection on `Q` and `c : Fin (D + 1) → ℚ` (`D ≥ 1`) has **strictly positive**
coefficients summing to `1` such that `∑ j, c j • R A (a^j) x = 0` for all `x ∈ K₀' A a`,
then every `S` (`1 ≤ |S| < n`) is `(n + D - dim K₀')`-extensible! -/
theorem master_balanced_version_A [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (D : ℕ) (hD : 1 ≤ D) (c : Fin (D + 1) → ℚ)
    (hc_pos : ∀ j, 0 < c j) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    {S : Finset Q} (hS_pos : 1 ≤ S.card) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α,
      w.length ≤ Fintype.card Q + D - Module.finrank ℚ (K₀' A a) ∧
      S.card < (A.preimage S w).card := by
  -- 1. `{ρ(b · a^j) | b ≠ a, j ≤ D}` already spans `K₀' A a` (using `c D > 0`)
  have hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ D ∧ x = ρ A (b :: List.replicate j a)} :=
    (K₀'_span_of_annihilator A a hbij D hD c (ne_of_gt (hc_pos (Fin.last D))) hann).trans
      (Submodule.span_mono (by rintro _ ⟨b, j, hba, hj, rfl⟩; exact ⟨b, j, hba, by omega, rfl⟩))
  -- 2. Apply `right_krylov_detect`
  obtain ⟨b, j_star, u, hba, hj_le, hu_len, hu_eq, hne⟩ :=
    right_krylov_detect A hsync a hbij D hspan hS_pos hS_lt
  -- 3. Weighted average `∑ j, c j * |S · (b · a^j · u)⁻¹| = |S · u⁻¹| = |S|`
  have havg : ∑ j : Fin (D + 1), c j * ((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) =
      (S.card : ℚ) := by
    have h0 := congrArg (fun v => evalSubset S (R A u v)) (hann (ρ A [b]) (ρ_single_mem_K₀' A hbij b))
    simp only [map_zero, map_sum, map_smul, smul_eq_mul] at h0
    have hterm : ∀ j : Fin (D + 1),
        evalSubset S (R A u (R A (List.replicate j.1 a) (ρ A [b]))) =
          ((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) - ((A.preimage S u).card : ℚ) := by
      intro j
      rw [ρ_append_replicate_a A hbij, List.singleton_append, ρ_eq_R_ones_sub, map_sub,
          ← LinearMap.comp_apply, ← R_append]
      have h1 : R A (b :: List.replicate j.1 a ++ u) (fun _ => 1) - R A u (fun _ => 1) =
          ρ A (b :: List.replicate j.1 a ++ u) - ρ A u := by
        rw [ρ_eq_R_ones_sub, ρ_eq_R_ones_sub]; abel
      rw [h1, map_sub, evalSubset_ρ, evalSubset_ρ]
      ring
    simp_rw [hterm, hu_eq, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc_sum, one_mul] at h0
    linarith
  -- 4. Since `c j > 0` for all `j` and `j_star` differs from `S.card`, some `j_pos` exceeds `S.card`!
  have hgt_ex : ∃ j : Fin (D + 1), S.card < (A.preimage S (b :: List.replicate j.1 a ++ u)).card := by
    by_contra hle_all
    push_neg at hle_all
    have hterm_le : ∀ j ∈ (Finset.univ : Finset (Fin (D + 1))),
        c j * ((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) ≤ c j * (S.card : ℚ) := by
      intro j _
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hle_all j)) (le_of_lt (hc_pos j))
    have hsum_eq : ∑ j : Fin (D + 1), c j * ((A.preimage S (b :: List.replicate j.1 a ++ u)).card : ℚ) =
        ∑ j : Fin (D + 1), c j * (S.card : ℚ) := by
      rw [havg, ← Finset.sum_mul, hc_sum, one_mul]
    have hall_eq := (Finset.sum_eq_sum_iff_of_le hterm_le).mp hsum_eq
    have hj_eq := hall_eq ⟨j_star, Nat.lt_succ_of_le hj_le⟩ (Finset.mem_univ _)
    have hcast : ((A.preimage S (b :: List.replicate j_star a ++ u)).card : ℚ) = (S.card : ℚ) :=
      mul_left_cancel₀ (ne_of_gt (hc_pos ⟨j_star, Nat.lt_succ_of_le hj_le⟩)) hj_eq
    exact hne (Nat.cast_injective hcast)
  obtain ⟨j_pos, hj_gt⟩ := hgt_ex
  refine ⟨b :: List.replicate j_pos.1 a ++ u, ?_, hj_gt⟩
  simp only [List.length_append, List.length_cons, List.length_replicate]
  have hd0_le : Module.finrank ℚ (K₀' A a) ≤ Fintype.card Q - 1 := by
    have h1 := Submodule.finrank_mono (K₀'_le_K0 A a)
    rw [finrank_ker_sumLin] at h1; exact h1
  omega

/-- **Strengthened Master Theorem (Version B with span bound `J`):**
If `a` is a bijection on `Q`, `{ρ(b · a^j) | b ≠ a, j ≤ J}` spans `K₀' A a`, and
`c : Fin (D + 1) → ℚ` has nonnegative coefficients with `c 0 > 0` and `∑ j, c j = 1`
annihilating `K₀' A a`, then every `S` (`1 ≤ |S| < n`) is `(n + D + J - dim K₀')`-extensible. -/
theorem master_balanced_version_B_span [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (J D : ℕ)
    (hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ J ∧ x = ρ A (b :: List.replicate j a)})
    (c : Fin (D + 1) → ℚ)
    (hc_nonneg : ∀ j, 0 ≤ c j) (hc0_pos : 0 < c 0) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    {S : Finset Q} (hS_pos : 1 ≤ S.card) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α,
      w.length ≤ Fintype.card Q + D + J - Module.finrank ℚ (K₀' A a) ∧
      S.card < (A.preimage S w).card := by
  obtain ⟨b, j_star, u, hba, hj_le, hu_len, hu_eq, hne⟩ :=
    right_krylov_detect A hsync a hbij J hspan hS_pos hS_lt
  have havg : ∑ j : Fin (D + 1),
      c j * ((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) = (S.card : ℚ) := by
    have hmem : ρ A (b :: List.replicate j_star a) ∈ K₀' A a :=
      Submodule.subset_span ⟨b, j_star, hba, rfl⟩
    have h0 := congrArg (fun v => evalSubset S (R A u v)) (hann _ hmem)
    simp only [map_zero, map_sum, map_smul, smul_eq_mul] at h0
    have hterm : ∀ j : Fin (D + 1),
        evalSubset S (R A u (R A (List.replicate j.1 a) (ρ A (b :: List.replicate j_star a)))) =
          ((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) -
            ((A.preimage S u).card : ℚ) := by
      intro j
      rw [ρ_append_replicate_a A hbij, List.cons_append, ← List.replicate_add, ρ_eq_R_ones_sub,
          map_sub, ← LinearMap.comp_apply, ← R_append]
      have h1 : R A (b :: List.replicate (j_star + j.1) a ++ u) (fun _ => 1) - R A u (fun _ => 1) =
          ρ A (b :: List.replicate (j_star + j.1) a ++ u) - ρ A u := by
        rw [ρ_eq_R_ones_sub, ρ_eq_R_ones_sub]; abel
      rw [h1, map_sub, evalSubset_ρ, evalSubset_ρ]; ring
    simp_rw [hterm, hu_eq, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc_sum, one_mul] at h0
    linarith
  have hgt_ex : ∃ j : Fin (D + 1),
      S.card < (A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card := by
    by_contra hle_all
    push_neg at hle_all
    have hterm_le : ∀ j ∈ (Finset.univ : Finset (Fin (D + 1))),
        c j * ((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) ≤
          c j * (S.card : ℚ) :=
      fun j _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hle_all j)) (hc_nonneg j)
    have hsum_eq : ∑ j : Fin (D + 1),
          c j * ((A.preimage S (b :: List.replicate (j_star + j.1) a ++ u)).card : ℚ) =
        ∑ j : Fin (D + 1), c j * (S.card : ℚ) := by
      rw [havg, ← Finset.sum_mul, hc_sum, one_mul]
    have h0_eq := (Finset.sum_eq_sum_iff_of_le hterm_le).mp hsum_eq 0 (Finset.mem_univ 0)
    have hcast : ((A.preimage S (b :: List.replicate (j_star + 0) a ++ u)).card : ℚ) = (S.card : ℚ) :=
      mul_left_cancel₀ (ne_of_gt hc0_pos) h0_eq
    rw [add_zero] at hcast
    exact hne (Nat.cast_injective hcast)
  obtain ⟨j_pos, hj_gt⟩ := hgt_ex
  refine ⟨b :: List.replicate (j_star + j_pos.1) a ++ u, ?_, hj_gt⟩
  simp only [List.length_append, List.length_cons, List.length_replicate]
  have hd0_le : Module.finrank ℚ (K₀' A a) ≤ Fintype.card Q - 1 := by
    have h1 := Submodule.finrank_mono (K₀'_le_K0 A a)
    rw [finrank_ker_sumLin] at h1; exact h1
  omega

/-- **Master Theorem (Version B — Theorem 12.1):**
Corollary of `master_balanced_version_B_span` with `J = dim K₀' - 1`. -/
theorem master_balanced_version_B [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (D : ℕ) (c : Fin (D + 1) → ℚ)
    (hc_nonneg : ∀ j, 0 ≤ c j) (hc0_pos : 0 < c 0) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    {S : Finset Q} (hS_pos : 1 ≤ S.card) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α,
      w.length ≤ Fintype.card Q + D - 1 ∧
      S.card < (A.preimage S w).card := by
  let d₀ := Module.finrank ℚ (K₀' A a)
  have hd₀_pos : 1 ≤ d₀ :=
    one_le_finrank_K₀'_of_isSync A hsync a hbij (by omega : 2 ≤ Fintype.card Q)
  have hspan : K₀' A a ≤ Submodule.span ℚ
      {x | ∃ (b : α) (j : ℕ), b ≠ a ∧ j ≤ d₀ - 1 ∧ x = ρ A (b :: List.replicate j a)} := by
    rw [K₀', Submodule.span_le]
    rintro _ ⟨b, r, hba, rfl⟩
    have hmem := span_orbit_le_finrank_Q (R A [a]) (K₀' A a)
      (fun x hx => K₀'_R_a_inv A hbij hx) (ρ A [b]) (ρ_single_mem_K₀' A hbij b) r
    rw [← R_replicate_eq_iterate, ρ_append_replicate_a A hbij, List.singleton_append] at hmem
    refine (Submodule.span_mono ?_) hmem
    rintro _ ⟨j, hj, rfl⟩
    rw [← R_replicate_eq_iterate, ρ_append_replicate_a A hbij, List.singleton_append]
    exact ⟨b, j, hba, by omega, rfl⟩
  obtain ⟨w, hw_len, hw_gt⟩ :=
    master_balanced_version_B_span A hsync a hbij (d₀ - 1) D hspan c hc_nonneg hc0_pos hc_sum
      hann hS_pos hS_lt
  exact ⟨w, by dsimp only [d₀] at hd₀_pos hw_len; omega, hw_gt⟩

end MasterTheorems

section MultiCycleCorollaries
variable {Q α : Type*} [Fintype Q] [DecidableEq Q]

/-- Orbit of `q` under a permutation letter `a`. -/
noncomputable def orbit (A : Aut Q α) (a : α) (q : Q) : Finset Q :=
  open scoped Classical in
  Finset.univ.filter (fun r => ∃ k : ℕ, A.eval q (List.replicate k a) = r)

/-- **True Multi-Cycle Balance Definition:** `a` is a bijection on `Q` (with arbitrary number
of disjoint cycles `C₁, ..., Cᵣ`) and every letter `b` preserves the preimage cardinality
of every cycle of `a`: `|(orbit A a q) · b⁻¹| = |orbit A a q|`. -/
def IsCycleBalanced (A : Aut Q α) (a : α) : Prop :=
  Function.Bijective (fun q => A.step q a) ∧
  ∀ (b : α) (q : Q), (A.preimage (orbit A a q) [b]).card = (orbit A a q).card

/-- If `a` has order `L ≥ 1` (`∀ q, eval q (replicate L a) = q`) and `A` is cycle-balanced for `a`,
then `∑ j < L, R A (a^j) x = 0` for all `x ∈ K₀' A a`. -/
lemma sum_orbit_annihilates_K₀' (A : Aut Q α) (a : α) (L : ℕ) (hL : 1 ≤ L)
    (hord : ∀ q : Q, A.eval q (List.replicate L a) = q)
    (hbal : IsCycleBalanced A a) :
    ∀ x ∈ K₀' A a, ∑ j : Fin L, ((1 : ℚ) / (L : ℚ)) • R A (List.replicate j.1 a) x = 0 := by
  classical
  have hL0 : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcomm : ∀ (j k : ℕ) (x : Q → ℚ),
      R A (List.replicate j a) (R A (List.replicate k a) x) =
        R A (List.replicate k a) (R A (List.replicate j a) x) := by
    intro j k x
    rw [← LinearMap.comp_apply, ← R_append, ← List.replicate_add, add_comm,
        List.replicate_add, R_append, LinearMap.comp_apply]
  -- It suffices to prove `∑ j : Fin L, R A (a^j) (ρ A [b]) = 0` for each `b ≠ a`!
  have hgen : ∀ b : α, ∑ j : Fin L, R A (List.replicate j.1 a) (ρ A [b]) = 0 := by
    intro b
    ext q
    simp only [Finset.sum_apply, Pi.zero_apply, R, Cerny.Linear.rowAct, LinearMap.coe_mk,
      AddHom.coe_mk]
    have hbij_j : ∀ j : ℕ, Function.Bijective (fun p => A.eval p (List.replicate j a)) := by
      intro j; induction j with
      | zero => exact Function.bijective_id
      | succ j ih => exact ih.comp hbal.1
    have horb_eq : ∀ p : Q, (∃ j : Fin L, A.eval p (List.replicate j.1 a) = q) ↔ p ∈ orbit A a q := by
      intro p
      simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨L - j.1, ?_⟩
        rw [← hj, ← Aut.eval_append, ← List.replicate_add, Nat.add_sub_cancel' (le_of_lt j.2)]
        exact hord p
      · rintro ⟨k, hk⟩
        have hkm : A.eval q (List.replicate (k % L) a) = p := by
          have hdiv : k = (k / L) * L + k % L := (Nat.div_add_mod' k L).symm
          have hmul : ∀ t : ℕ, ∀ x : Q, A.eval x (List.replicate (t * L) a) = x := by
            intro t x; induction t with
            | zero => simp
            | succ t iht => rw [Nat.succ_mul, List.replicate_add, Aut.eval_append, iht, hord]
          rw [← hk]
          conv_rhs => rw [hdiv]; rw [List.replicate_add, Aut.eval_append, hmul]
        have hlt : (L - k % L) % L < L := Nat.mod_lt _ (by omega)
        refine ⟨⟨(L - k % L) % L, hlt⟩, ?_⟩
        rw [← hkm, ← Aut.eval_append, ← List.replicate_add]
        by_cases h0 : k % L = 0
        · simp [h0]
        · have hsub : (L - k % L) % L = L - k % L := Nat.mod_eq_of_lt (by omega)
          have hk_lt : k % L < L := Nat.mod_lt k (by omega)
          simp only [hsub, Nat.add_sub_cancel' (le_of_lt hk_lt)]
          exact hord q
    -- Count how many `j : Fin L` satisfy `eval p (a^j) = q`: it is constant for every `p ∈ orbit A a q`!
    let cnt : Q → ℕ := fun p => (Finset.univ.filter (fun j : Fin L => A.eval p (List.replicate j.1 a) = q)).card
    have hcnt_const : ∀ p ∈ orbit A a q, cnt p = cnt q := by
      intro p hp
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hp).2
      let e : Fin L ≃ Fin L :=
        { toFun := fun j => ⟨(j.1 + k) % L, Nat.mod_lt _ (by omega)⟩
          invFun := fun j => ⟨(j.1 + (L - k % L)) % L, Nat.mod_lt _ (by omega)⟩
          left_inv := fun j => Fin.ext (by
            dsimp
            have hklt : k % L < L := Nat.mod_lt k (by omega)
            rw [Nat.mod_add_mod, add_assoc, Nat.add_mod j.1, Nat.add_mod k]
            have hL_mod : (k % L + (L - k % L) % L) % L = 0 := by
              have h1 : (k % L + (L - k % L) % L) % L = (k % L + (L - k % L)) % L := by
                simp [Nat.add_mod]
              rw [h1, show k % L + (L - k % L) = L by omega, Nat.mod_self]
            rw [hL_mod, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt j.2])
          right_inv := fun j => Fin.ext (by
            dsimp
            have hklt : k % L < L := Nat.mod_lt k (by omega)
            rw [Nat.mod_add_mod, add_assoc, Nat.add_mod j.1, Nat.add_mod (L - k % L)]
            have hL_mod : ((L - k % L) % L + k % L) % L = 0 := by
              rw [Nat.mod_add_mod, show L - k % L + k % L = L by omega, Nat.mod_self]
            rw [hL_mod, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt j.2]) }
      dsimp only [cnt]
      refine Finset.card_bij (fun j _ => e j) ?_ (fun _ _ _ _ h => e.injective h) ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        have hmul : ∀ t : ℕ, ∀ x : Q, A.eval x (List.replicate (t * L) a) = x := by
          intro t x; induction t with
          | zero => simp
          | succ t iht => rw [Nat.succ_mul, List.replicate_add, Aut.eval_append, iht, hord]
        have hmod : ∀ m : ℕ, ∀ x : Q, A.eval x (List.replicate (m % L) a) = A.eval x (List.replicate m a) := by
          intro m x
          have hdiv : m = (m / L) * L + m % L := (Nat.div_add_mod' m L).symm
          conv_rhs => rw [hdiv, List.replicate_add, Aut.eval_append, hmul]
        dsimp [e]
        rw [hmod, add_comm, List.replicate_add, Aut.eval_append, hk, hj]
      · intro j' hj'
        refine ⟨e.symm j', ?_, e.apply_symm_apply j'⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
        have hmul : ∀ t : ℕ, ∀ x : Q, A.eval x (List.replicate (t * L) a) = x := by
          intro t x; induction t with
          | zero => simp
          | succ t iht => rw [Nat.succ_mul, List.replicate_add, Aut.eval_append, iht, hord]
        have hmod : ∀ m : ℕ, ∀ x : Q, A.eval x (List.replicate (m % L) a) = A.eval x (List.replicate m a) := by
          intro m x
          have hdiv : m = (m / L) * L + m % L := (Nat.div_add_mod' m L).symm
          conv_rhs => rw [hdiv, List.replicate_add, Aut.eval_append, hmul]
        rw [← hk, ← Aut.eval_append, ← List.replicate_add]
        dsimp [e]
        rw [← hmod (k + (j'.1 + (L - k % L)) % L)]
        have hsum_mod : (k + (j'.1 + (L - k % L)) % L) % L = j'.1 := by
          have hklt : k % L < L := Nat.mod_lt k (by omega)
          have hjlt : j'.1 < L := j'.2
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [show k + (j'.1 + (L - k % L)) = j'.1 + (k + (L - k % L)) by omega]
          rw [Nat.add_mod j'.1, Nat.add_mod k]
          have hL_mod : (k % L + (L - k % L) % L) % L = 0 := by
            have h1 : (k % L + (L - k % L) % L) % L = (k % L + (L - k % L)) % L := by
              simp [Nat.add_mod]
            rw [h1, show k % L + (L - k % L) = L by omega, Nat.mod_self]
          rw [hL_mod, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hjlt]
        rw [hsum_mod, hj']
    -- Swap sums and pull out `cnt q`!
    calc ∑ j : Fin L, ∑ p : Q, (if A.eval p (List.replicate j.1 a) = q then ρ A [b] p else 0)
        = ∑ p : Q, ∑ j : Fin L, (if A.eval p (List.replicate j.1 a) = q then ρ A [b] p else 0) :=
          Finset.sum_comm
      _ = ∑ p : Q, (cnt p : ℚ) * ρ A [b] p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ p ∈ orbit A a q, (cnt q : ℚ) * ρ A [b] p := by
          rw [← Finset.sum_subset (Finset.subset_univ (orbit A a q))]
          · exact Finset.sum_congr rfl fun p hp => by rw [hcnt_const p hp]
          · intro p _ hp_not
            have hc0 : cnt p = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro j _ hj; exact hp_not ((horb_eq p).mp ⟨j, hj⟩)
            simp [hc0]
      _ = (cnt q : ℚ) * ∑ p ∈ orbit A a q, ρ A [b] p := by rw [← Finset.mul_sum]
      _ = 0 := by rw [sum_ρ_subset, hbal.2 b q, sub_self, mul_zero]
  intro x hx
  rw [← Finset.smul_sum]
  suffices h0 : ∑ j : Fin L, R A (List.replicate j.1 a) x = 0 by rw [h0, smul_zero]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨b, k, _, rfl⟩
    rw [← List.singleton_append, ← ρ_append_replicate_a A hbal.1]
    simp_rw [hcomm _ k]
    rw [← map_sum, hgen b, map_zero]
  | zero => simp
  | add _ _ _ _ ih1 ih2 => simp only [map_add, Finset.sum_add_distrib, ih1, ih2, add_zero]
  | smul c _ _ ih => simp only [map_smul, ← Finset.smul_sum, ih, smul_zero]

/-- **Corollary 11.7 (ALL Prime-Order Cycle-Balanced Permutations — Arbitrary Composite `n`!):**
Every synchronizing automaton that is cycle-balanced for ANY permutation `a` of prime order `p`
(arbitrary number of 1-cycles and `p`-cycles, including ALL involutions `p = 2`!) satisfies
`rt(A) ≤ (n - 1)^2`. -/
theorem prime_order_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (p : ℕ) (hp : Nat.Prime p)
    (hord : ∀ q : Q, A.eval q (List.replicate p a) = q)
    (hbal : IsCycleBalanced A a) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hp_pos : 1 ≤ p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  apply cerny_of_n_extensible A hsync
  intro S hS_pos hS_lt
  -- Step 1: `p - 1 ≤ dim K₀' A a` via irreducibility of `Φ_p` over `ℚ`
  have hdim_ge : p - 1 ≤ Module.finrank ℚ (K₀' A a) := by
    -- Find `b₀ ≠ a` with `ρ A [b₀] ≠ 0`
    have hex_b₀ : ∃ b₀ : α, b₀ ≠ a ∧ ρ A [b₀] ≠ 0 :=
      exists_defect_letter_of_isSync A hsync a hbal.1 (by omega : 2 ≤ Fintype.card Q)
    obtain ⟨b₀, hb₀a, hρ_ne⟩ := hex_b₀
    let Ra : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) := R A [a]
    let v₀ : Q → ℚ := ρ A [b₀]
    have hann_v₀ : ∑ j ∈ Finset.range p, (Ra ^ j) v₀ = 0 := by
      have h0 := sum_orbit_annihilates_K₀' A a p hp_pos hord hbal v₀ (ρ_single_mem_K₀' A hbal.1 b₀)
      rw [← Finset.smul_sum, smul_eq_zero] at h0
      have h1 : (1 : ℚ) / (p : ℚ) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero)
      have hsum0 := h0.resolve_left h1
      rw [← Fin.sum_univ_eq_sum_range (fun j => (Ra ^ j) v₀)]
      refine (Finset.sum_congr rfl fun j _ => by rw [R_replicate_eq_pow]).trans hsum0
    have hli : LinearIndependent ℚ (fun j : Fin (p - 1) => (Ra ^ j.1) v₀) := by
      rw [Fintype.linearIndependent_iff]
      intro coeff hcoeff
      let g : Polynomial ℚ := ∑ j : Fin (p - 1), Polynomial.C (coeff j) * Polynomial.X ^ j.1
      have hdeg_g : g.natDegree < (Polynomial.cyclotomic p ℚ).natDegree := by
        rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]
        by_cases hg0 : g = 0
        · rw [hg0, Polynomial.natDegree_zero]; omega
        · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
          apply (Finset.sup_le fun j _ => ?_).trans_lt (by omega : p - 2 < p - 1)
          calc (Polynomial.C (coeff j) * Polynomial.X ^ j.1).natDegree
              ≤ (Polynomial.C (coeff j)).natDegree + (Polynomial.X ^ j.1).natDegree :=
                Polynomial.natDegree_mul_le
            _ = 0 + j.1 := by simp
            _ ≤ p - 2 := by omega
      have hΦ_eval : Polynomial.aeval Ra (Polynomial.cyclotomic p ℚ) v₀ = 0 := by
        have : Fact (Nat.Prime p) := ⟨hp⟩
        rw [Polynomial.cyclotomic_prime ℚ p, map_sum]
        simp only [map_pow, Polynomial.aeval_X, LinearMap.coe_sum, Finset.sum_apply]
        exact hann_v₀
      have hg_eval : Polynomial.aeval Ra g v₀ = 0 := by
        simp only [g, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
          ← Algebra.smul_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
        exact hcoeff
      let I : Ideal (Polynomial ℚ) :=
        { carrier := {P | Polynomial.aeval Ra P v₀ = 0}
          zero_mem' := by simp
          add_mem' := fun {P₁ P₂} h₁ h₂ => by
            simp only [Set.mem_ofPred_eq, map_add, LinearMap.add_apply] at *
            rw [h₁, h₂, add_zero]
          smul_mem' := fun P₁ {P₂} h₂ => by
            simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
            change (Polynomial.aeval Ra P₁) ((Polynomial.aeval Ra P₂) v₀) = 0
            rw [h₂, map_zero] }
      have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
        Polynomial.cyclotomic.irreducible_rat hp.pos
      have hdvd : Polynomial.cyclotomic p ℚ ∣ g := by
        by_contra hndvd
        obtain ⟨a₁, b₁, hab⟩ := (hirr.coprime_iff_not_dvd.mpr hndvd).symm
        have h1_mem : (1 : Polynomial ℚ) ∈ I := by
          rw [← hab]; exact I.add_mem (I.smul_mem a₁ hg_eval) (I.smul_mem b₁ hΦ_eval)
        simp [I, hρ_ne, v₀] at h1_mem
      have hg_zero : g = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg_g
      intro j
      have hcs : ∀ (s : Finset (Fin (p - 1))) (F : Fin (p - 1) → Polynomial ℚ) (k : ℕ),
          (∑ i ∈ s, F i).coeff k = ∑ i ∈ s, (F i).coeff k := by
        intro s F k
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]
      have hcj := congrArg (fun P : Polynomial ℚ => P.coeff j.1) hg_zero
      simp only [g, hcs, Polynomial.coeff_zero] at hcj
      rw [Finset.sum_eq_single j] at hcj
      · simpa [Polynomial.coeff_C_mul_X_pow] using hcj
      · intro k _ hkj
        have hne : j.1 ≠ k.1 := fun h => hkj (Fin.ext h.symm)
        simp [Polynomial.coeff_C_mul_X_pow, hne]
      · intro hj_abs; exact absurd (Finset.mem_univ j) hj_abs
    have hsub : Submodule.span ℚ (Set.range (fun j : Fin (p - 1) => (Ra ^ j.1) v₀)) ≤ K₀' A a := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      dsimp only [Ra, v₀]
      rw [R_replicate_eq_pow, ρ_append_replicate_a A hbal.1, List.singleton_append]
      exact Submodule.subset_span ⟨b₀, j.1, hb₀a, rfl⟩
    calc p - 1 = Fintype.card (Fin (p - 1)) := (Fintype.card_fin _).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j : Fin (p - 1) => (Ra ^ j.1) v₀))) :=
          (finrank_span_eq_card hli).symm
      _ ≤ Module.finrank ℚ (K₀' A a) := Submodule.finrank_mono hsub
  -- Step 2: Apply Master Theorem Version A with `D = p - 1` and `c j = 1 / p > 0`!
  let c : Fin ((p - 1) + 1) → ℚ := fun _ => (1 : ℚ) / (p : ℚ)
  have hc_pos : ∀ j, 0 < c j := fun _ => div_pos one_pos (Nat.cast_pos.mpr hp.pos)
  have hc_sum : ∑ j : Fin ((p - 1) + 1), c j = 1 := by
    simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (p - 1) + 1 = p by omega]
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp
  have hann : ∀ x ∈ K₀' A a,
      ∑ j : Fin ((p - 1) + 1), c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    have h0 := sum_orbit_annihilates_K₀' A a p hp_pos hord hbal x hx
    have heq : (p - 1) + 1 = p := by omega
    refine (Fintype.sum_equiv (finCongr heq) _ _ fun _ => rfl).trans h0
  obtain ⟨w, hw_len, hw_gt⟩ :=
    master_balanced_version_A A hsync a hbal.1 (p - 1) (by omega) c hc_pos hc_sum hann hS_pos hS_lt
  exact ⟨w, by omega, hw_gt⟩

/-- **Theorem 12.2 (Composite Order `m` with a Coprime-Step Collision — No Primality!):**
If `A` is cycle-balanced for a permutation `a` of **arbitrary composite order `m ≥ 2`**,
and some letter `b₀ ≠ a` has defect `ρ A [b₀] = e_{c₀} - e_{c₀ · a^s}` on an `m`-cycle
containing `c₀` with `Nat.Coprime s m`, then `rt(A) ≤ (n - 1)^2`! -/
theorem coprime_step_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (m : ℕ) (hm : 2 ≤ m)
    (hord : ∀ q : Q, A.eval q (List.replicate m a) = q)
    (hbal : IsCycleBalanced A a)
    (b₀ : α) (hb₀a : b₀ ≠ a) (c₀ : Q) (s : ℕ) (hcop : Nat.Coprime s m)
    (hcyc_inj : Set.InjOn (fun j : ℕ => A.eval c₀ (List.replicate j a)) (Finset.range m : Set ℕ))
    (hρ_b₀ : ρ A [b₀] = (fun q => (if q = c₀ then (1 : ℚ) else 0) -
      (if q = A.eval c₀ (List.replicate s a) then 1 else 0))) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  have hm_pos : 1 ≤ m := by omega
  apply cerny_of_n_extensible A hsync
  intro S hS_pos hS_lt
  -- Step 1: Telescoping sums produce `m - 1` linearly independent vectors `e_{c₀} - e_{c₀ · a^(k*s)} ∈ K₀'`!
  have hdim_ge : m - 1 ≤ Module.finrank ℚ (K₀' A a) := by
    let pt : ℕ → Q := fun k => A.eval c₀ (List.replicate k a)
    have hpt_mod : ∀ k : ℕ, pt (k % m) = pt k := by
      intro k
      have hdiv : k = (k / m) * m + k % m := (Nat.div_add_mod' k m).symm
      have hmul : ∀ t : ℕ, ∀ x : Q, A.eval x (List.replicate (t * m) a) = x := by
        intro t x; induction t with
        | zero => simp
        | succ t iht => rw [Nat.succ_mul, List.replicate_add, Aut.eval_append, iht, hord]
      dsimp only [pt]
      conv_rhs => rw [hdiv, List.replicate_add, Aut.eval_append, hmul]
    have hR_delta : ∀ (j : ℕ) (x : Q),
        R A (List.replicate j a) (fun q => if q = x then (1 : ℚ) else 0) =
          (fun q => if q = A.eval x (List.replicate j a) then 1 else 0) := by
      intro j x; ext q
      simp only [R, Cerny.Linear.rowAct_apply]
      rw [Finset.sum_eq_single x]
      · simp [eq_comm]
      · intro p _ hpx; simp [hpx]
      · intro h; exact absurd (Finset.mem_univ x) h
    have hstep_vec : ∀ k : ℕ,
        (fun q => (if q = pt 0 then (1 : ℚ) else 0) - (if q = pt (k * s) then 1 else 0)) ∈ K₀' A a := by
      intro k
      induction k with
      | zero =>
        rw [show (fun q => (if q = pt 0 then (1 : ℚ) else 0) -
              if q = pt (0 * s) then 1 else 0) = 0 by ext q; simp]
        exact Submodule.zero_mem _
      | succ k ih =>
        have hshift : ρ A (b₀ :: List.replicate (k * s) a) =
            (fun q => (if q = pt (k * s) then (1 : ℚ) else 0) -
              (if q = pt ((k + 1) * s) then 1 else 0)) := by
          rw [← List.singleton_append, ← ρ_append_replicate_a A hbal.1, hρ_b₀]
          change (R A (List.replicate (k * s) a))
              ((fun q => if q = c₀ then (1 : ℚ) else 0) -
               (fun q => if q = A.eval c₀ (List.replicate s a) then (1 : ℚ) else 0)) = _
          rw [map_sub, hR_delta, hR_delta]
          ext q
          simp only [Pi.sub_apply, pt, ← Aut.eval_append, ← List.replicate_add]
          rw [show s + k * s = (k + 1) * s by ring]
        have hmem_s : ρ A (b₀ :: List.replicate (k * s) a) ∈ K₀' A a :=
          Submodule.subset_span ⟨b₀, k * s, hb₀a, rfl⟩
        have hadd := Submodule.add_mem (K₀' A a) ih (hshift ▸ hmem_s)
        convert hadd using 1
        ext q; simp only [Pi.add_apply]; ring
    let gen : Fin (m - 1) → (Q → ℚ) := fun k =>
      fun q => (if q = pt 0 then (1 : ℚ) else 0) - (if q = pt ((k.1 + 1) * s) then 1 else 0)
    have hpt_inj : ∀ k₁ k₂ : Fin (m - 1), pt ((k₁.1 + 1) * s) = pt ((k₂.1 + 1) * s) → k₁ = k₂ := by
      intro k₁ k₂ hEq
      conv_lhs at hEq => rw [← hpt_mod]
      conv_rhs at hEq => rw [← hpt_mod]
      have hmod := hcyc_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hm_pos)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hm_pos))) hEq
      have hmeq : (k₁.1 + 1) ≡ (k₂.1 + 1) [MOD m] :=
        Nat.ModEq.cancel_right_of_coprime hcop.symm hmod
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmeq
      exact Fin.ext (by omega)
    have hpt_ne0 : ∀ k : Fin (m - 1), pt ((k.1 + 1) * s) ≠ pt 0 := by
      intro k hEq
      rw [← hpt_mod] at hEq
      have hmod := hcyc_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hm_pos)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hm_pos)) hEq
      have hmeq : (k.1 + 1) * s ≡ 0 * s [MOD m] := by simpa [Nat.ModEq] using hmod
      have h0 := Nat.ModEq.cancel_right_of_coprime hcop.symm hmeq
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at h0
      omega
    have hli : LinearIndependent ℚ gen := by
      rw [Fintype.linearIndependent_iff]
      intro coeff hcoeff k
      have hval := congrFun hcoeff (pt ((k.1 + 1) * s))
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, gen] at hval
      rw [Finset.sum_eq_single k] at hval
      · simp only [hpt_ne0 k, ↓reduceIte, zero_sub, mul_neg, mul_one, neg_eq_zero] at hval
        exact hval
      · intro j _ hjk
        have hne : pt ((k.1 + 1) * s) ≠ pt ((j.1 + 1) * s) := fun h => hjk (hpt_inj k j h).symm
        simp [hpt_ne0 k, hne]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hsub : Submodule.span ℚ (Set.range gen) ≤ K₀' A a := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hstep_vec (k.1 + 1)
    calc m - 1 = Fintype.card (Fin (m - 1)) := (Fintype.card_fin _).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range gen)) := (finrank_span_eq_card hli).symm
      _ ≤ Module.finrank ℚ (K₀' A a) := Submodule.finrank_mono hsub
  -- Step 2: Master Theorem Version A with `D = m - 1`, `c j = 1 / m > 0`
  let c : Fin ((m - 1) + 1) → ℚ := fun _ => (1 : ℚ) / (m : ℚ)
  have hc_pos : ∀ j, 0 < c j := fun _ => div_pos one_pos (Nat.cast_pos.mpr hm_pos)
  have hc_sum : ∑ j : Fin ((m - 1) + 1), c j = 1 := by
    simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (m - 1) + 1 = m by omega]
    have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hann : ∀ x ∈ K₀' A a,
      ∑ j : Fin ((m - 1) + 1), c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    have h0 := sum_orbit_annihilates_K₀' A a m hm_pos hord hbal x hx
    exact (Fintype.sum_equiv (finCongr (by omega : (m - 1) + 1 = m)) _ _ fun _ => rfl).trans h0
  obtain ⟨w, hw_len, hw_gt⟩ :=
    master_balanced_version_A A hsync a hbal.1 (m - 1) (by omega) c hc_pos hc_sum hann hS_pos hS_lt
  exact ⟨w, by omega, hw_gt⟩

/-- **Corollary 11.9 (Antisymmetric Defect — `R A [a] (ρ A [b]) = -ρ A [b]`):**
Works for ANY bijective `a` (even composite order!) whenever every letter satisfies
`R A [a] (ρ A [b]) = -ρ A [b]` (annihilated by `P(X) = (1/2)(1 + X)`, `D = 1 ≤ d₀`). -/
theorem antisymmetric_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hanti : ∀ b : α, b ≠ a → R A [a] (ρ A [b]) = -ρ A [b]) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  apply cerny_of_n_extensible A hsync
  intro S hS_pos hS_lt
  have hanti_all : ∀ x ∈ K₀' A a, R A [a] x = -x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨b, j, hba, rfl⟩
      rw [show b :: List.replicate j a = [b] ++ List.replicate j a from rfl,
          ← ρ_append_replicate_a A hbij]
      induction j with
      | zero => simp [R_nil, hanti b hba]
      | succ j ih =>
        rw [List.replicate_succ', R_append, LinearMap.comp_apply, ih, map_neg, ih]
    | zero => simp
    | add _ _ _ _ ih1 ih2 => rw [map_add, ih1, ih2, neg_add]
    | smul c _ _ ih => rw [map_smul, ih, smul_neg]
  have hd₀_pos : 1 ≤ Module.finrank ℚ (K₀' A a) :=
    one_le_finrank_K₀'_of_isSync A hsync a hbij (by omega : 2 ≤ Fintype.card Q)
  let c : Fin 2 → ℚ := fun _ => (1 : ℚ) / 2
  have hc_pos : ∀ j : Fin 2, 0 < c j := fun _ => by norm_num [c]
  have hc_sum : ∑ j : Fin 2, c j = 1 := by simp [Fin.sum_univ_two, c]
  have hann : ∀ x ∈ K₀' A a, ∑ j : Fin 2, c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, List.replicate_zero, R_nil, LinearMap.id_apply,
               Fin.val_one, List.replicate_one, hanti_all x hx, c, smul_neg, add_neg_cancel]
  obtain ⟨w, hw_len, hw_gt⟩ :=
    master_balanced_version_A A hsync a hbij 1 le_rfl c hc_pos hc_sum hann hS_pos hS_lt
  exact ⟨w, by omega, hw_gt⟩

/-- **Lemma 12.3 (`Φ₆` `L¹`-norm lower bound):** every nonzero integer vector `v : Fin 6 → ℤ`
annihilated by `Φ₆(S) = S² - S + I` satisfies `‖v‖₁ ≥ 4` (so no rank-`(n - 1)` letter can be
pure in `Φ₆`). -/
theorem phi6_l1_norm_ge_four (v : Fin 6 → ℤ) (hv : v ≠ 0)
    (hker : ∀ i : Fin 6,
      v i - v ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩ +
        v ⟨(i.val + 2) % 6, Nat.mod_lt _ (by decide)⟩ = 0) :
    4 ≤ ∑ i : Fin 6, (v i).natAbs := by
  have h0 := hker ⟨0, by decide⟩
  have h1 := hker ⟨1, by decide⟩
  have h2 := hker ⟨2, by decide⟩
  have h3 := hker ⟨3, by decide⟩
  have h4 := hker ⟨4, by decide⟩
  have h5 := hker ⟨5, by decide⟩
  change v 0 - v 1 + v 2 = 0 at h0
  change v 1 - v 2 + v 3 = 0 at h1
  change v 2 - v 3 + v 4 = 0 at h2
  change v 3 - v 4 + v 5 = 0 at h3
  change v 4 - v 5 + v 0 = 0 at h4
  change v 5 - v 0 + v 1 = 0 at h5
  have hv1 : v 1 = v 0 + v 2 := by omega
  have hv3 : v 3 = -v 0 := by omega
  have hv4 : v 4 = -(v 0 + v 2) := by omega
  have hv5 : v 5 = -v 2 := by omega
  have hne02 : v 0 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra hboth
    push_neg at hboth
    apply hv; ext i
    fin_cases i <;> simp [hv1, hv3, hv4, hv5, hboth.1, hboth.2]
  have hsum : ∑ i : Fin 6, (v i).natAbs =
      2 * ((v 0).natAbs + (v 2).natAbs + (v 0 + v 2).natAbs) := by
    rw [Fin.sum_univ_six]
    change (v 0).natAbs + (v 1).natAbs + (v 2).natAbs + (v 3).natAbs + (v 4).natAbs +
      (v 5).natAbs = 2 * ((v 0).natAbs + (v 2).natAbs + (v 0 + v 2).natAbs)
    rw [hv1, hv3, hv4, hv5, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_neg]
    omega
  rw [hsum]
  have htri : 2 ≤ (v 0).natAbs + (v 2).natAbs + (v 0 + v 2).natAbs := by
    rcases hne02 with h0ne | h2ne <;> omega
  omega

/-- **Composite-Order Černý Theorem via Degree-`g` Annihilator + Nonnegative Multiple:**
If `K₀' A a` is annihilated by a polynomial `p` of degree `g ≥ 1` (possibly with negative
coefficients, e.g. `Φ_d`) and by a nonnegative probability polynomial `c` of degree `D`
with `c 0 > 0`, and `D + g - 1 ≤ dim K₀' A a`, then `A` satisfies Černý's bound `(n - 1)^2`. -/
theorem balanced_cerny_of_annihilator_and_pos_multiple [Nonempty Q]
    (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (g D : ℕ) (hg : 1 ≤ g)
    (p : Fin (g + 1) → ℚ) (hp_top : p (Fin.last g) ≠ 0)
    (hann_p : ∀ x ∈ K₀' A a, ∑ j : Fin (g + 1), p j • R A (List.replicate j.1 a) x = 0)
    (c : Fin (D + 1) → ℚ)
    (hc_nonneg : ∀ j, 0 ≤ c j) (hc0_pos : 0 < c 0) (hc_sum : ∑ j : Fin (D + 1), c j = 1)
    (hann_c : ∀ x ∈ K₀' A a, ∑ j : Fin (D + 1), c j • R A (List.replicate j.1 a) x = 0)
    (hdim : D + g - 1 ≤ Module.finrank ℚ (K₀' A a)) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  apply cerny_of_n_extensible A hsync
  intro S hS_pos hS_lt
  have hspan := K₀'_span_of_annihilator A a hbij g hg p hp_top hann_p
  obtain ⟨w, hw_len, hw_gt⟩ :=
    master_balanced_version_B_span A hsync a hbij (g - 1) D hspan c hc_nonneg hc0_pos hc_sum
      hann_c hS_pos hS_lt
  exact ⟨w, by omega, hw_gt⟩

/-- **New Corollary (`Φ₄` with `dim K₀' ≥ 3`):**
Complements Counterexample 2 (`ex2`, where `K₀' ⊆ ker Φ₄` has `dim = 2` and min extension `n + 1`):
as soon as `dim K₀' ≥ 3`, `n`-extensibility and Černý's bound `(n - 1)^2` hold unconditionally. -/
theorem phi4_high_dim_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hphi4 : ∀ x ∈ K₀' A a, R A (List.replicate 2 a) x + x = 0)
    (hdim : 3 ≤ Module.finrank ℚ (K₀' A a)) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let p : Fin 3 → ℚ := fun j => if j.1 = 1 then 0 else 1
  have hp0 : p 0 = 1 := by simp [p]
  have hp1 : p 1 = 0 := by simp [p]
  have hp2 : p 2 = 1 := by simp [p]
  have hp_top : p (Fin.last 2) ≠ 0 := by
    rw [show Fin.last 2 = (2 : Fin 3) from rfl, hp2]; norm_num
  have hann_p : ∀ x ∈ K₀' A a, ∑ j : Fin 3, p j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    rw [Fin.sum_univ_three, hp0, hp1, hp2]
    simp only [Fin.val_zero, Fin.val_two, List.replicate_zero, R_nil, LinearMap.id_apply,
      one_smul, zero_smul, add_zero]
    rw [add_comm]
    exact hphi4 x hx
  let c : Fin 3 → ℚ := fun j => if j.1 = 1 then 0 else (1 : ℚ) / 2
  have hc0 : c 0 = 1 / 2 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c]
  have hc2 : c 2 = 1 / 2 := by simp [c]
  have hc_nonneg : ∀ j : Fin 3, 0 ≤ c j := by intro j; fin_cases j <;> norm_num [c]
  have hc0_pos : 0 < c 0 := by rw [hc0]; norm_num
  have hc_sum : ∑ j : Fin 3, c j = 1 := by rw [Fin.sum_univ_three, hc0, hc1, hc2]; norm_num
  have hann_c : ∀ x ∈ K₀' A a, ∑ j : Fin 3, c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    rw [Fin.sum_univ_three, hc0, hc1, hc2]
    simp only [Fin.val_zero, Fin.val_two, List.replicate_zero, R_nil, LinearMap.id_apply,
      zero_smul, add_zero]
    rw [← smul_add, add_comm, hphi4 x hx, smul_zero]
  exact balanced_cerny_of_annihilator_and_pos_multiple A hsync a hbij 2 2 (by omega)
    p hp_top hann_p c hc_nonneg hc0_pos hc_sum hann_c (by omega)

/-- **New Corollary (`Φ₆` with `dim K₀' ≥ 4`):**
Complements Counterexample 3 (`ex3`, where `K₀' ⊆ ker Φ₆` has `dim = 2` and min extension `n + 1`):
using `p = Φ₆` (`g = 2`) and `c = (1/2)(1 + X^3)` (`D = 3`), whenever `dim K₀' ≥ 4`,
`n`-extensibility and Černý's bound `(n - 1)^2` hold unconditionally. -/
theorem phi6_high_dim_balanced_cerny [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (hphi6 : ∀ x ∈ K₀' A a, R A (List.replicate 2 a) x - R A [a] x + x = 0)
    (hdim : 4 ≤ Module.finrank ℚ (K₀' A a)) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let p : Fin 3 → ℚ := fun j => if j.1 = 1 then -1 else 1
  have hp0 : p 0 = 1 := by simp [p]
  have hp1 : p 1 = -1 := by simp [p]
  have hp2 : p 2 = 1 := by simp [p]
  have hp_top : p (Fin.last 2) ≠ 0 := by
    rw [show Fin.last 2 = (2 : Fin 3) from rfl, hp2]; norm_num
  have hann_p : ∀ x ∈ K₀' A a, ∑ j : Fin 3, p j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    rw [Fin.sum_univ_three, hp0, hp1, hp2]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, List.replicate_zero, List.replicate_one,
      R_nil, LinearMap.id_apply, one_smul, neg_smul]
    have hrew : x + -(R A [a] x) + R A (List.replicate 2 a) x =
        R A (List.replicate 2 a) x - R A [a] x + x := by abel
    rw [hrew]
    exact hphi6 x hx
  let c : Fin 4 → ℚ := fun j => if j.1 = 0 ∨ j.1 = 3 then (1 : ℚ) / 2 else 0
  have hc0 : c 0 = 1 / 2 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c]
  have hc2 : c 2 = 0 := by simp [c]
  have hc3 : c 3 = 1 / 2 := by simp [c]
  have hc_nonneg : ∀ j : Fin 4, 0 ≤ c j := by intro j; fin_cases j <;> norm_num [c]
  have hc0_pos : 0 < c 0 := by rw [hc0]; norm_num
  have hc_sum : ∑ j : Fin 4, c j = 1 := by
    rw [Fin.sum_univ_four, hc0, hc1, hc2, hc3]; norm_num
  have hann_c : ∀ x ∈ K₀' A a, ∑ j : Fin 4, c j • R A (List.replicate j.1 a) x = 0 := by
    intro x hx
    have h1 := hphi6 x hx
    have h2 := hphi6 (R A [a] x) (K₀'_R_a_inv A hbij hx)
    have hr3 : R A (List.replicate 2 a) (R A [a] x) = R A (List.replicate 3 a) x := by
      rw [← LinearMap.comp_apply, ← R_append]; rfl
    have hr2 : R A [a] (R A [a] x) = R A (List.replicate 2 a) x := by
      rw [← LinearMap.comp_apply, ← R_append]; rfl
    rw [hr3, hr2] at h2
    have hcube : R A (List.replicate 3 a) x + x = 0 := by
      have hadd := congrArg₂ (· + ·) h2 h1
      rw [add_zero] at hadd
      have hrew : (R A (List.replicate 3 a) x - R A (List.replicate 2 a) x + R A [a] x) +
          (R A (List.replicate 2 a) x - R A [a] x + x) = R A (List.replicate 3 a) x + x := by abel
      rwa [hrew] at hadd
    rw [Fin.sum_univ_four, hc0, hc1, hc2, hc3]
    simp only [Fin.val_zero, show (3 : Fin 4).val = 3 from rfl, List.replicate_zero,
      R_nil, LinearMap.id_apply, zero_smul, add_zero]
    rw [← smul_add, add_comm, hcube, smul_zero]
  exact balanced_cerny_of_annihilator_and_pos_multiple A hsync a hbij 2 3 (by omega)
    p hp_top hann_p c hc_nonneg hc0_pos hc_sum hann_c (by omega)

end MultiCycleCorollaries

end BalancedPermutations
