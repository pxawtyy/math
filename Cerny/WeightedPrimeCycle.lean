import Cerny.Defs
import Cerny.KrylovEulerian
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted Averaging, Multi-Cluster Initial Step, and Prime One-Cluster Bound

This module defines the cycle states `cycleStates A a` and cycle level `cycleLevel A a`
for any letter `a : α`, and proves:
1. `multi_cluster_initial_step`: for any synchronizing automaton and any letter `a` with
   `c = |cycleStates A a| ≥ 2`, there exist `c₀ ∈ C` and `w₁` of length `≤ n - c + 1`
   such that `|(A.preimage {c₀} (w₁ ++ a^ℓ)) ∩ C| ≥ 2`.
2. `one_cluster_cycle_double_count`: double-counting averaging identity over a single cycle.
3. `one_cluster_prime_bound`: Steinberg's bound `(p - 1)(n - 1) + p * ℓ ≤ (n - 1)^2`
   for synchronizing one-cluster automata with prime cycle length `p` (purely over `ℚ`).
-/

namespace WeightedPrimeCycle

section CycleStructure
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

private lemma image_replicate_antitone (a : α) (k : ℕ) :
    A.image Finset.univ (List.replicate (k + 1) a) ⊆
      A.image Finset.univ (List.replicate k a) := by
  rw [List.replicate_succ, ← List.singleton_append, Aut.image_append]
  exact A.image_mono (Finset.subset_univ _) (List.replicate k a)

private lemma cycleLevel_exists [Nonempty Q] (a : α) :
    ∃ k : ℕ, (A.image Finset.univ (List.replicate (k + 1) a)).card =
      (A.image Finset.univ (List.replicate k a)).card := by
  by_contra hno
  push_neg at hno
  have hdec : ∀ k, (A.image Finset.univ (List.replicate k a)).card ≤ Fintype.card Q - k := by
    intro k
    induction k with
    | zero => simp [Finset.card_univ]
    | succ k ih =>
      have hlt : (A.image Finset.univ (List.replicate (k + 1) a)).card <
          (A.image Finset.univ (List.replicate k a)).card := by
        have hle := Finset.card_le_card (image_replicate_antitone A a k)
        exact lt_of_le_of_ne hle (hno k)
      omega
  have h1 := hdec (Fintype.card Q)
  have hne : (A.image Finset.univ (List.replicate (Fintype.card Q) a)).Nonempty :=
    A.image_nonempty Finset.univ_nonempty _
  have hpos := hne.card_pos
  omega

/-- Cycle level `ℓ` of letter `a`: smallest `k` where `|im(a^(k+1))| = |im(a^k)|`. -/
noncomputable def cycleLevel [Nonempty Q] (a : α) : ℕ :=
  Nat.find (cycleLevel_exists A a)

/-- Cycle states `C` of letter `a`: `im(a^ℓ)`. -/
noncomputable def cycleStates [Nonempty Q] (a : α) : Finset Q :=
  A.image Finset.univ (List.replicate (cycleLevel A a) a)

lemma cycleStates_nonempty [Nonempty Q] (a : α) : (cycleStates A a).Nonempty :=
  A.image_nonempty Finset.univ_nonempty _

lemma cycleLevel_le [Nonempty Q] (a : α) :
    cycleLevel A a ≤ Fintype.card Q - (cycleStates A a).card := by
  have hdec : ∀ k ≤ cycleLevel A a,
      (A.image Finset.univ (List.replicate k a)).card + k ≤ Fintype.card Q := by
    intro k hk
    induction k with
    | zero => simp [Finset.card_univ]
    | succ k ih =>
      have hne := Nat.find_min (cycleLevel_exists A a) (by omega : k < cycleLevel A a)
      have hle := Finset.card_le_card (image_replicate_antitone A a k)
      have hlt : (A.image Finset.univ (List.replicate (k + 1) a)).card <
          (A.image Finset.univ (List.replicate k a)).card := lt_of_le_of_ne hle hne
      have ih' := ih (by omega)
      omega
  have := hdec (cycleLevel A a) le_rfl
  change (cycleStates A a).card + cycleLevel A a ≤ Fintype.card Q at this
  omega

lemma image_cycleStates_a [Nonempty Q] (a : α) :
    A.image (cycleStates A a) [a] = cycleStates A a := by
  unfold cycleStates
  rw [← Aut.image_append, ← List.replicate_succ']
  apply Finset.eq_of_subset_of_card_le (image_replicate_antitone A a (cycleLevel A a))
  exact le_of_eq (Nat.find_spec (cycleLevel_exists A a)).symm

lemma step_a_mem_cycleStates [Nonempty Q] (a : α) {q : Q} (hq : q ∈ cycleStates A a) :
    A.step q a ∈ cycleStates A a := by
  rw [← image_cycleStates_a A a]
  exact Finset.mem_image_of_mem _ hq

lemma eval_replicate_mem_cycleStates [Nonempty Q] (a : α) (q : Q) (j : ℕ) :
    A.eval q (List.replicate (cycleLevel A a + j) a) ∈ cycleStates A a := by
  rw [add_comm, List.replicate_add, Aut.eval_append]
  have h0 : A.eval (A.eval q (List.replicate j a)) (List.replicate (cycleLevel A a) a) ∈
      A.image Finset.univ (List.replicate (cycleLevel A a) a) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  exact h0

lemma eval_append_replicate_mem_cycleStates [Nonempty Q] (a : α) (q : Q) (w : List α) :
    A.eval q (w ++ List.replicate (cycleLevel A a) a) ∈ cycleStates A a := by
  rw [Aut.eval_append]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma eval_cycleLevel_bijOn [Nonempty Q] (a : α) :
    Set.BijOn (fun q => A.eval q (List.replicate (cycleLevel A a) a))
      (cycleStates A a) (cycleStates A a) := by
  have hstep_inj : Set.InjOn (fun q => A.step q a) (cycleStates A a) := by
    apply Finset.injOn_of_card_image_eq
    exact congrArg Finset.card (image_cycleStates_a A a)
  have hstep_bij : Set.BijOn (fun q => A.step q a) (cycleStates A a) (cycleStates A a) := by
    refine ⟨fun q hq => step_a_mem_cycleStates A a hq, hstep_inj, ?_⟩
    intro q hq
    rw [← image_cycleStates_a A a] at hq
    rcases (Aut.mem_image A).mp hq with ⟨p, hp, hpq⟩
    exact ⟨p, hp, hpq⟩
  have hrep_bij : ∀ k : ℕ, Set.BijOn (fun q => A.eval q (List.replicate k a))
      (cycleStates A a) (cycleStates A a) := by
    intro k
    induction k with
    | zero =>
      simp only [List.replicate_zero, Aut.eval_nil]
      exact Set.bijOn_id _
    | succ k ih =>
      simp only [List.replicate_succ, Aut.eval_cons]
      exact ih.comp hstep_bij
  exact hrep_bij (cycleLevel A a)

end CycleStructure

section InitialStep
open KrylovEulerian
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Multi-cluster initial step (for any synchronizing automaton and any letter `a`
with `c = |cycleStates A a| ≥ 2`): there exist `c₀ ∈ C` and `w₁` of length `≤ n - c + 1`
such that `|(A.preimage {c₀} (w₁ ++ a^ℓ)) ∩ C| ≥ 2`. -/
theorem multi_cluster_initial_step [Nonempty Q] (hsync : A.IsSync) (a : α)
    (hc : 2 ≤ (cycleStates A a).card) :
    ∃ c₀ ∈ cycleStates A a, ∃ w₁ : List α,
      w₁.length ≤ Fintype.card Q - (cycleStates A a).card + 1 ∧
      2 ≤ (A.preimage {c₀} (w₁ ++ List.replicate (cycleLevel A a) a) ∩ cycleStates A a).card := by
  classical
  let C := cycleStates A a
  let ℓ := cycleLevel A a
  let n := Fintype.card Q
  let c := C.card
  let σ_C : (Q → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun f => ∑ q ∈ C, f q
      map_add' := fun f g => Finset.sum_add_distrib
      map_smul' := fun k f => by simp [Finset.mul_sum] }
  let H_C := LinearMap.ker σ_C
  have hfinrank_HC : Module.finrank ℚ H_C = n - 1 := by
    have hsurj : LinearMap.range σ_C = ⊤ := by
      rw [eq_top_iff]
      intro y _
      refine ⟨fun _ => y / (c : ℚ), ?_⟩
      simp only [σ_C, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_const, nsmul_eq_mul]
      have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp only [c, C]; omega)
      change (c : ℚ) * (y / (c : ℚ)) = y
      field_simp
    have hrk := LinearMap.finrank_range_add_finrank_ker σ_C
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_self ℚ] at hrk
    dsimp only [n, H_C] at *
    omega
  let e : Q → (Q → ℚ) := fun c₀ =>
    pullbackLin A (List.replicate ℓ a) (fun q => if q = c₀ then 1 else 0)
  let ones : Q → ℚ := fun _ => 1
  let v₀ : Q → (Q → ℚ) := fun c₀ => e c₀ - ((1 : ℚ) / (c : ℚ)) • ones
  have hsum_e_pt : ∀ q : Q, ∑ c₀ ∈ C, e c₀ q = 1 := by
    intro q
    simp only [e, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hmem : A.eval q (List.replicate ℓ a) ∈ C :=
      eval_replicate_mem_cycleStates A a q 0
    rw [Finset.sum_ite_eq]
    simp [hmem]
  have hbij := eval_cycleLevel_bijOn A a
  have hinv_ex : ∀ c₀ ∈ C, ∃ q ∈ C, A.eval q (List.replicate ℓ a) = c₀ :=
    fun c₀ hc₀ => hbij.surjOn hc₀
  have hv₀_mem_HC : ∀ c₀ ∈ C, v₀ c₀ ∈ H_C := by
    intro c₀ hc₀
    rw [LinearMap.mem_ker]
    simp only [σ_C, v₀, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, ones, mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsum_ec₀ : ∑ q ∈ C, e c₀ q = 1 := by
      obtain ⟨q₀, hq₀C, hq₀_eq⟩ := hinv_ex c₀ hc₀
      rw [Finset.sum_eq_single q₀]
      · simp [e, pullbackLin, Cerny.Linear.pullbackLin, hq₀_eq]
      · intro q hqC hqq₀
        simp only [e, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right_iff]
        intro heq
        exact absurd (hbij.injOn hqC hq₀C (heq.trans hq₀_eq.symm)) hqq₀
      · intro hq₀_nC; exact absurd hq₀C hq₀_nC
    rw [hsum_ec₀]
    have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp only [c, C]; omega)
    change 1 - (c : ℚ) * (1 / (c : ℚ)) = 0
    field_simp
    ring
  let V : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
    Submodule.span ℚ {f | ∃ w : List α, w.length ≤ t ∧ ∃ c₀ ∈ C, f = pullbackLin A w (v₀ c₀)}
  have hV0_finrank : c - 1 ≤ Module.finrank ℚ (V 0) := by
    obtain ⟨c_ref, hc_ref⟩ := cycleStates_nonempty A a
    let C' := C.erase c_ref
    have hC'_card : C'.card = c - 1 := Finset.card_erase_of_mem hc_ref
    have hli : LinearIndependent ℚ (fun x : ↥C' => v₀ x.1) := by
      rw [Fintype.linearIndependent_iff]
      intro α hα
      obtain ⟨q_ref, hq_refC, hq_ref_eq⟩ := hinv_ex c_ref hc_ref
      have hsum_α : ∑ x : ↥C', α x = 0 := by
        have hpt := congrFun hα q_ref
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v₀,
          Pi.sub_apply, ones, mul_one] at hpt
        have he_zero : ∀ x : ↥C', e x.1 q_ref = 0 := fun x => by
          simp only [e, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, hq_ref_eq, ite_eq_right_iff]
          intro h
          have hx_ne : x.1 ≠ c_ref := (Finset.mem_erase.mp x.2).1
          exact absurd h.symm hx_ne
        simp only [he_zero, zero_sub, mul_neg, Finset.sum_neg_distrib, neg_eq_zero,
          ← Finset.sum_mul] at hpt
        have hc0 : (1 : ℚ) / (c : ℚ) ≠ 0 := by
          have : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp only [c, C]; omega)
          exact one_div_ne_zero this
        exact (mul_eq_zero.mp hpt).resolve_right hc0
      intro x
      obtain ⟨qx, hqxC, hqx_eq⟩ := hinv_ex x.1 (Finset.erase_subset _ _ x.2)
      have hpt := congrFun hα qx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v₀,
        Pi.sub_apply, ones, mul_one] at hpt
      have hsplit : ∑ y : ↥C', α y * (e y.1 qx - 1 / (c : ℚ)) =
          (∑ y : ↥C', α y * e y.1 qx) - (∑ y : ↥C', α y) * (1 / (c : ℚ)) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hsplit, hsum_α, zero_mul, sub_zero] at hpt
      rw [Finset.sum_eq_single x] at hpt
      · simp only [e, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, hqx_eq, ↓reduceIte,
          mul_one] at hpt
        exact hpt
      · intro y _ hyx
        simp only [e, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, hqx_eq]
        have hne : x.1 ≠ y.1 := fun h => hyx (Subtype.ext h.symm)
        simp [hne]
      · intro hx_abs; exact absurd (Finset.mem_univ x) hx_abs
    have hspan_le : Submodule.span ℚ (Set.range (fun x : ↥C' => v₀ x.1)) ≤ V 0 := by
      rw [Submodule.span_le]
      rintro f ⟨x, rfl⟩
      apply Submodule.subset_span
      exact ⟨[], by simp, x.1, Finset.erase_subset _ _ x.2, by simp [pullbackLin_nil]⟩
    calc c - 1 = Fintype.card ↥C' := by rw [Fintype.card_coe, hC'_card]
      _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (fun x : ↥C' => v₀ x.1))) := by
          rw [finrank_span_eq_card hli]
      _ ≤ Module.finrank ℚ (V 0) := Submodule.finrank_mono hspan_le
  by_contra hno
  push_neg at hno
  have hsum_pre_eq : ∀ w : List α,
      ∑ c₀ ∈ C, (A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card = C.card := by
    intro w
    have hcard_one : ∀ q ∈ C, ∑ c₀ ∈ C, (if A.eval q (w ++ List.replicate ℓ a) = c₀ then 1 else 0) = 1 := by
      intro q _
      have hmem : A.eval q (w ++ List.replicate ℓ a) ∈ C :=
        eval_append_replicate_mem_cycleStates A a q w
      rw [Finset.sum_ite_eq]
      simp only [hmem, ↓reduceIte]
    calc ∑ c₀ ∈ C, (A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card
        = ∑ c₀ ∈ C, ∑ q ∈ C, if A.eval q (w ++ List.replicate ℓ a) = c₀ then 1 else 0 := by
          refine Finset.sum_congr rfl fun c₀ _ => ?_
          rw [← Finset.card_filter]
          congr 1
          ext q
          simp [Aut.mem_preimage, and_comm]
      _ = ∑ q ∈ C, ∑ c₀ ∈ C, if A.eval q (w ++ List.replicate ℓ a) = c₀ then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ _q ∈ C, 1 := Finset.sum_congr rfl hcard_one
      _ = C.card := by simp
  have hall_eq_one : ∀ (w : List α) (hw : w.length ≤ n - c + 1) (c₀ : Q), c₀ ∈ C →
      (A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card = 1 := by
    intro w hw c₀ hc₀
    have hle_all : ∀ x ∈ C, (A.preimage {x} (w ++ List.replicate ℓ a) ∩ C).card ≤ 1 := by
      intro x hx
      have := hno x hx w hw
      dsimp only [ℓ, C]
      omega
    have hsum_le : ∑ x ∈ C, (A.preimage {x} (w ++ List.replicate ℓ a) ∩ C).card ≤ ∑ _x ∈ C, 1 :=
      Finset.sum_le_sum hle_all
    have hsum_eq : ∑ x ∈ C, (A.preimage {x} (w ++ List.replicate ℓ a) ∩ C).card = ∑ _x ∈ C, 1 := by
      rw [hsum_pre_eq w]; simp
    exact (Finset.sum_eq_sum_iff_of_le hle_all).mp hsum_eq c₀ hc₀
  have hsum_pull : ∀ (w : List α) (c₀ : Q),
      σ_C (pullbackLin A w (v₀ c₀)) =
        ((A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card : ℚ) - 1 := by
    intro w c₀
    simp only [σ_C, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, v₀, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, ones, mul_one, e, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    have hpre : ∑ q ∈ C, (if A.eval (A.eval q w) (List.replicate ℓ a) = c₀ then (1 : ℚ) else 0) =
        ((A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card : ℚ) := by
      rw [← Finset.sum_filter]
      have : C.filter (fun q => A.eval (A.eval q w) (List.replicate ℓ a) = c₀) =
          A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C := by
        ext q
        simp [Aut.mem_preimage, Aut.eval_append, and_comm]
      rw [this]
      simp
    rw [hpre]
    have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp only [c, C]; omega)
    change ((A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card : ℚ) - (c : ℚ) * (1 / (c : ℚ)) =
      ((A.preimage {c₀} (w ++ List.replicate ℓ a) ∩ C).card : ℚ) - 1
    field_simp
  have hV_le_HC : ∀ t ≤ n - c + 1, V t ≤ H_C := by
    intro t ht
    rw [Submodule.span_le]
    rintro f ⟨w, hw, c₀, hc₀, rfl⟩
    change pullbackLin A w (v₀ c₀) ∈ H_C
    rw [LinearMap.mem_ker, hsum_pull w c₀, hall_eq_one w (by omega) c₀ hc₀]
    simp
  have hV_mono : ∀ t, V t ≤ V (t + 1) := fun t => by
    apply Submodule.span_mono
    rintro f ⟨w, hw, c₀, hc₀, rfl⟩
    exact ⟨w, by omega, c₀, hc₀, rfl⟩
  have hstab : ∃ t < n - c + 1, V t = V (t + 1) := by
    by_contra hns
    push_neg at hns
    have hinc : ∀ t ≤ n - c + 1, c - 1 + t ≤ Module.finrank ℚ (V t) := by
      intro t ht
      induction t with
      | zero => simpa using hV0_finrank
      | succ t ih =>
        have hlt_sub : V t < V (t + 1) := lt_of_le_of_ne (hV_mono t) (hns t (by omega))
        have hlt_rk := Submodule.finrank_lt_finrank_of_lt hlt_sub
        have ih' := ih (by omega)
        omega
    have htop := hinc (n - c + 1) le_rfl
    have hle_HC : Module.finrank ℚ (V (n - c + 1)) ≤ Module.finrank ℚ H_C :=
      Submodule.finrank_mono (hV_le_HC (n - c + 1) le_rfl)
    rw [hfinrank_HC] at hle_HC
    have hc_le_n : c ≤ n := Finset.card_le_univ C
    omega
  obtain ⟨t, ht_lt, ht_eq⟩ := hstab
  have hinv : ∀ σ : α, ∀ f ∈ V t, pullbackLin A [σ] f ∈ V t := by
    intro σ f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨w, hw, c₀, hc₀, rfl⟩
      rw [ht_eq]
      apply Submodule.subset_span
      refine ⟨σ :: w, by simp; omega, c₀, hc₀, ?_⟩
      rw [pullbackLin_cons]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (V t).add_mem hx hy
    | smul k x _ hx => rw [map_smul]; exact (V t).smul_mem k hx
  have hall_in_Vt : ∀ (w : List α) (c₀ : Q), c₀ ∈ C → pullbackLin A w (v₀ c₀) ∈ V t := by
    intro w c₀ hc₀
    induction w with
    | nil =>
      rw [pullbackLin_nil]
      apply Submodule.span_mono (s := {f | ∃ u : List α, u.length ≤ 0 ∧ ∃ c' ∈ C, f = pullbackLin A u (v₀ c')})
      · rintro f ⟨u, hu, c', hc', rfl⟩
        exact ⟨u, by omega, c', hc', rfl⟩
      · exact Submodule.subset_span ⟨[], le_rfl, c₀, hc₀, rfl⟩
    | cons σ w ih =>
      rw [pullbackLin_cons]
      exact hinv σ _ ih
  obtain ⟨u₀, hu₀⟩ := hsync
  rw [Aut.isSyncWord_iff_exists_eval_eq] at hu₀
  obtain ⟨q_star, hq_star⟩ := hu₀
  let c_star := A.eval q_star (List.replicate ℓ a)
  have hc_star : c_star ∈ C := eval_replicate_mem_cycleStates A a q_star 0
  have hu₀_in_HC : pullbackLin A u₀ (v₀ c_star) ∈ H_C :=
    hV_le_HC t (by omega) (hall_in_Vt u₀ c_star hc_star)
  rw [LinearMap.mem_ker, hsum_pull u₀ c_star] at hu₀_in_HC
  have hpre_univ : A.preimage {c_star} (u₀ ++ List.replicate ℓ a) ∩ C = C := by
    ext q
    simp only [Finset.mem_inter, Aut.mem_preimage, Finset.mem_singleton, Aut.eval_append,
      hq_star q, and_iff_right_iff_imp]
    intro _
    rfl
  rw [hpre_univ] at hu₀_in_HC
  have hc_eq_one : (c : ℚ) = 1 := by change (c : ℚ) - 1 = 0 at hu₀_in_HC; linarith
  have : c = 1 := Nat.cast_injective hc_eq_one
  dsimp only [c, C] at this
  omega

end InitialStep

section OneClusterPrime
open KrylovEulerian

/-- A one-cluster automaton with respect to letter `a`: `cycleStates A a` forms a single
cycle under `a`. -/
def IsOneCluster {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A : Aut Q α) (a : α) : Prop :=
  ∀ p ∈ WeightedPrimeCycle.cycleStates A a, ∀ q ∈ WeightedPrimeCycle.cycleStates A a,
    ∃ j < (WeightedPrimeCycle.cycleStates A a).card, A.eval p (List.replicate j a) = q

lemma one_cluster_cycle_bij {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A : Aut Q α) (a : α) (h1c : IsOneCluster A a) {p₀ : Q} (hp₀ : p₀ ∈ cycleStates A a) :
    Set.BijOn (fun j : ℕ => A.eval p₀ (List.replicate j a))
      (Finset.range (cycleStates A a).card) (cycleStates A a) := by
  let m := (cycleStates A a).card
  have hmaps_all : ∀ j : ℕ, A.eval p₀ (List.replicate j a) ∈ cycleStates A a := by
    intro j
    induction j with
    | zero => simpa using hp₀
    | succ j ih =>
      rw [List.replicate_succ', Aut.eval_append]
      exact step_a_mem_cycleStates A a ih
  have hmaps : Set.MapsTo (fun j : ℕ => A.eval p₀ (List.replicate j a))
      (Finset.range m) (cycleStates A a) := fun j _ => hmaps_all j
  have hsurj : Set.SurjOn (fun j : ℕ => A.eval p₀ (List.replicate j a))
      (Finset.range m) (cycleStates A a) := by
    intro q hq
    obtain ⟨j, hj, hjq⟩ := h1c p₀ hp₀ q hq
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr hj), hjq⟩
  have himg_eq : (Finset.range m).image (fun j => A.eval p₀ (List.replicate j a)) =
      cycleStates A a := by
    ext q
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hmaps (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
    · intro hq; obtain ⟨j, hj, rfl⟩ := h1c p₀ hp₀ q hq; exact ⟨j, hj, rfl⟩
  have hinj : Set.InjOn (fun j : ℕ => A.eval p₀ (List.replicate j a)) (Finset.range m) := by
    apply Finset.injOn_of_card_image_eq
    rw [himg_eq, Finset.card_range]
  exact ⟨hmaps, hinj, hsurj⟩

/-- Double counting on a single cycle: for any `S ⊆ C` and any word `w`,
`∑ j ∈ range m, |(A.preimage S (w ++ a^(ℓ + j))) ∩ C| = m * |S|`. -/
theorem one_cluster_cycle_double_count {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A : Aut Q α) (a : α) (h1c : IsOneCluster A a)
    {S : Finset Q} (hSC : S ⊆ cycleStates A a) (w : List α) :
    ∑ j ∈ Finset.range (cycleStates A a).card,
      (A.preimage S (w ++ List.replicate (cycleLevel A a + j) a) ∩ cycleStates A a).card =
      (cycleStates A a).card * S.card := by
  let C := cycleStates A a
  let ℓ := cycleLevel A a
  let m := C.card
  have hrewrite : ∀ j ∈ Finset.range m,
      (A.preimage S (w ++ List.replicate (ℓ + j) a) ∩ C).card =
        ∑ p ∈ C, if A.eval (A.eval p (w ++ List.replicate ℓ a)) (List.replicate j a) ∈ S then 1 else 0 := by
    intro j _
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp only [Finset.mem_inter, Aut.mem_preimage, Finset.mem_filter, List.replicate_add,
      ← List.append_assoc, Aut.eval_append]
    exact and_comm
  rw [Finset.sum_congr rfl hrewrite, Finset.sum_comm]
  have hrow : ∀ p ∈ C,
      ∑ j ∈ Finset.range m,
        (if A.eval (A.eval p (w ++ List.replicate ℓ a)) (List.replicate j a) ∈ S then 1 else 0) =
        S.card := by
    intro p _
    let p₀ := A.eval p (w ++ List.replicate ℓ a)
    have hp₀C : p₀ ∈ C := eval_append_replicate_mem_cycleStates A a p w
    have hbij := one_cluster_cycle_bij A a h1c hp₀C
    change (∑ j ∈ Finset.range m, if A.eval p₀ (List.replicate j a) ∈ S then 1 else 0) = S.card
    rw [← Finset.card_filter]
    have himg : (Finset.filter (fun j => A.eval p₀ (List.replicate j a) ∈ S) (Finset.range m)).image
        (fun j => A.eval p₀ (List.replicate j a)) = S := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨j, ⟨_, hqS⟩, rfl⟩; exact hqS
      · intro hqS
        obtain ⟨j, hj, hjq⟩ := hbij.surjOn (hSC hqS)
        dsimp only at hjq
        rw [Finset.mem_coe, Finset.mem_range] at hj
        exact ⟨j, ⟨hj, by rw [hjq]; exact hqS⟩, hjq⟩
    have hcard_eq :
        (Finset.filter (fun j => A.eval p₀ (List.replicate j a) ∈ S) (Finset.range m)).card =
          (Finset.image (fun j => A.eval p₀ (List.replicate j a))
            (Finset.filter (fun j => A.eval p₀ (List.replicate j a) ∈ S) (Finset.range m))).card :=
      (Finset.card_image_of_injOn ((hbij.injOn).mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun j => A.eval p₀ (List.replicate j a) ∈ S)
          (Finset.range m))))).symm
    rw [hcard_eq, himg]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]

/-- Helper: Steinberg's prime one-cluster extension step (purely over `ℚ`). -/
private lemma one_cluster_prime_extension {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A : Aut Q α) (hsync : A.IsSync) (a : α) (h1c : IsOneCluster A a)
    (hp : Nat.Prime (cycleStates A a).card)
    {S : Finset Q} (hSC : S ⊆ cycleStates A a) (hS_pos : 1 ≤ S.card)
    (hS_lt : S.card < (cycleStates A a).card) :
    ∃ w : List α, w.length ≤ Fintype.card Q ∧
      S.card < (A.preimage S (w ++ List.replicate (cycleLevel A a) a) ∩ cycleStates A a).card := by
  classical
  let C := cycleStates A a
  let ℓ := cycleLevel A a
  let n := Fintype.card Q
  let p := C.card
  let σ_C : (Q → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun f => ∑ q ∈ C, f q
      map_add' := fun f g => Finset.sum_add_distrib
      map_smul' := fun k f => by simp [Finset.mul_sum] }
  let H_C := LinearMap.ker σ_C
  have hfinrank_HC : Module.finrank ℚ H_C = n - 1 := by
    have hsurj : LinearMap.range σ_C = ⊤ := by
      rw [eq_top_iff]
      intro y _
      refine ⟨fun _ => y / (p : ℚ), ?_⟩
      simp only [σ_C, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_const, nsmul_eq_mul]
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      change (p : ℚ) * (y / (p : ℚ)) = y
      field_simp
    have hrk := LinearMap.finrank_range_add_finrank_ker σ_C
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_self ℚ] at hrk
    dsimp only [n, H_C] at *
    omega
  let indS : Q → ℚ := fun q => if q ∈ S then 1 else 0
  let indC : Q → ℚ := fun q => if q ∈ C then 1 else 0
  let f₀ : Q → ℚ := indS - ((S.card : ℚ) / (p : ℚ)) • indC
  let u_S : Q → ℚ := pullbackLin A (List.replicate ℓ a) f₀
  have hbij := eval_cycleLevel_bijOn A a
  have huS_ne : u_S ≠ 0 := by
    intro h0
    obtain ⟨q_in, hq_in⟩ := Finset.card_pos.mp hS_pos
    obtain ⟨q₀, _, hq₀_eq⟩ := hbij.surjOn (hSC hq_in)
    dsimp only at hq₀_eq
    have hval := congrFun h0 q₀
    simp only [u_S, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, f₀, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, indS, indC] at hval
    change (if A.eval q₀ (List.replicate (cycleLevel A a) a) ∈ S then (1 : ℚ) else 0) -
      (S.card : ℚ) / (p : ℚ) *
        (if A.eval q₀ (List.replicate (cycleLevel A a) a) ∈ C then 1 else 0) = 0 at hval
    rw [hq₀_eq, if_pos hq_in, if_pos (hSC hq_in)] at hval
    have hlt_q : (S.card : ℚ) < (p : ℚ) := by exact_mod_cast hS_lt
    have hp_pos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
    field_simp at hval
    linarith
  have hsum_uS : ∀ w : List α,
      σ_C (pullbackLin A w u_S) =
        ((A.preimage S (w ++ List.replicate ℓ a) ∩ C).card : ℚ) - (S.card : ℚ) := by
    intro w
    simp only [σ_C, pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, u_S, f₀, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, indS, indC, Finset.sum_sub_distrib, mul_one]
    have h1 : ∑ q ∈ C, (if A.eval (A.eval q w) (List.replicate ℓ a) ∈ S then (1 : ℚ) else 0) =
        ((A.preimage S (w ++ List.replicate ℓ a) ∩ C).card : ℚ) := by
      rw [← Finset.sum_filter]
      have : C.filter (fun q => A.eval (A.eval q w) (List.replicate ℓ a) ∈ S) =
          A.preimage S (w ++ List.replicate ℓ a) ∩ C := by
        ext q
        simp [Aut.mem_preimage, Aut.eval_append, and_comm]
      rw [this]
      simp
    have h2 : ∑ q ∈ C, ((S.card : ℚ) / (p : ℚ)) *
          (if A.eval (A.eval q w) (List.replicate ℓ a) ∈ C then (1 : ℚ) else 0) = (S.card : ℚ) := by
      have hall : ∀ q ∈ C, A.eval (A.eval q w) (List.replicate ℓ a) ∈ C := by
        intro q _
        rw [← Aut.eval_append]
        exact eval_append_replicate_mem_cycleStates A a q w
      have hconst : ∀ q ∈ C, ((S.card : ℚ) / (p : ℚ)) *
          (if A.eval (A.eval q w) (List.replicate ℓ a) ∈ C then (1 : ℚ) else 0) =
          (S.card : ℚ) / (p : ℚ) := fun q hq => by simp [hall q hq]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      change (p : ℚ) * ((S.card : ℚ) / (p : ℚ)) = (S.card : ℚ)
      field_simp
    rw [h1, h2]
  -- Annihilation by Φ_p(T [a]) = ∑_{j < p} (T [a])^j
  let T_a : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) := pullbackLin A [a]
  have hTa_pow : ∀ j : ℕ, (T_a ^ j) = pullbackLin A (List.replicate j a) := by
    intro j
    induction j with
    | zero => simp [pullbackLin_nil]; rfl
    | succ j ih =>
      rw [pow_succ', ih, List.replicate_succ, pullbackLin_cons]
      rfl
  have hann : ∑ j ∈ Finset.range p, (T_a ^ j) u_S = 0 := by
    ext q
    simp only [Finset.sum_apply, LinearMap.coe_sum, Pi.zero_apply, hTa_pow]
    simp only [pullbackLin, Cerny.Linear.pullbackLin, LinearMap.coe_mk, AddHom.coe_mk, u_S, ← Aut.eval_append]
    let q₀ := A.eval q (List.replicate ℓ a)
    have hq₀C : q₀ ∈ C := eval_replicate_mem_cycleStates A a q 0
    have hcomm : ∀ j : ℕ, A.eval (A.eval q (List.replicate j a)) (List.replicate ℓ a) =
        A.eval q₀ (List.replicate j a) := by
      intro j
      rw [← Aut.eval_append, ← Aut.eval_append, ← List.replicate_add, ← List.replicate_add,
        add_comm j ℓ]
    have hbij_q₀ := one_cluster_cycle_bij A a h1c hq₀C
    have hsum_f₀ : ∑ x ∈ C, f₀ x = 0 := by
      simp only [f₀, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, indS, indC, Finset.sum_sub_distrib]
      have hs : ∑ x ∈ C, (if x ∈ S then (1 : ℚ) else 0) = (S.card : ℚ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSC]
        simp
      have hc' : ∑ x ∈ C, ((S.card : ℚ) / (p : ℚ)) * (if x ∈ C then (1 : ℚ) else 0) =
          (S.card : ℚ) := by
        have h1 : ∀ x ∈ C, ((S.card : ℚ) / (p : ℚ)) * (if x ∈ C then (1 : ℚ) else 0) =
            (S.card : ℚ) / (p : ℚ) := fun x hx => by simp [hx]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
        have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        change (p : ℚ) * ((S.card : ℚ) / (p : ℚ)) = (S.card : ℚ)
        field_simp
      rw [hs, hc', sub_self]
    have hbij_sum : ∑ j ∈ Finset.range p, f₀ (A.eval q₀ (List.replicate j a)) = ∑ x ∈ C, f₀ x := by
      refine Finset.sum_bij (fun j _ => A.eval q₀ (List.replicate j a)) ?_ ?_ ?_ ?_
      · intro j hj
        exact hbij_q₀.mapsTo (Finset.mem_coe.mpr hj)
      · intro i hi j hj hij
        exact hbij_q₀.injOn (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij
      · intro x hx
        obtain ⟨j, hj, hjx⟩ := hbij_q₀.surjOn hx
        exact ⟨j, Finset.mem_coe.mp hj, hjx⟩
      · intro _ _; rfl
    calc ∑ j ∈ Finset.range p, f₀ (A.eval q (List.replicate j a ++ List.replicate ℓ a))
        = ∑ j ∈ Finset.range p, f₀ (A.eval q₀ (List.replicate j a)) := by
          refine Finset.sum_congr rfl fun j _ => by rw [Aut.eval_append, hcomm j]
      _ = ∑ x ∈ C, f₀ x := hbij_sum
      _ = 0 := hsum_f₀
  -- Irreducibility of Φ_p over ℚ gives linear independence of {(T_a^j) u_S | j < p - 1}
  have hli_W0 : LinearIndependent ℚ (fun j : Fin (p - 1) => (T_a ^ j.1) u_S) := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hcoeff
    let g : Polynomial ℚ := ∑ j : Fin (p - 1), Polynomial.C (coeff j) * Polynomial.X ^ j.1
    have hdeg_g : g.natDegree < (Polynomial.cyclotomic p ℚ).natDegree := by
      rw [Polynomial.natDegree_cyclotomic]
      have htotient : Nat.totient p = p - 1 := Nat.totient_prime hp
      rw [htotient]
      have hp_two : 2 ≤ p := hp.two_le
      by_cases hg0 : g = 0
      · rw [hg0, Polynomial.natDegree_zero]
        omega
      · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
        apply (Finset.sup_le fun j _ => ?_).trans_lt (by omega : p - 2 < p - 1)
        calc (Polynomial.C (coeff j) * Polynomial.X ^ j.1).natDegree
            ≤ (Polynomial.C (coeff j)).natDegree + (Polynomial.X ^ j.1).natDegree :=
              Polynomial.natDegree_mul_le
          _ = 0 + j.1 := by simp
          _ ≤ p - 2 := by omega
    have hΦ_eval : Polynomial.aeval T_a (Polynomial.cyclotomic p ℚ) u_S = 0 := by
      have : Fact (Nat.Prime p) := ⟨hp⟩
      rw [Polynomial.cyclotomic_prime ℚ p, map_sum]
      simp only [map_pow, Polynomial.aeval_X, LinearMap.coe_sum, Finset.sum_apply]
      exact hann
    have hg_eval : Polynomial.aeval T_a g u_S = 0 := by
      simp only [g, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        ← Algebra.smul_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      exact hcoeff
    -- Ideal of polynomials annihilating u_S:
    let I : Ideal (Polynomial ℚ) :=
      { carrier := {P | Polynomial.aeval T_a P u_S = 0}
        zero_mem' := by simp
        add_mem' := fun {P₁ P₂} h₁ h₂ => by
          simp only [Set.mem_ofPred_eq, map_add, LinearMap.add_apply] at *
          rw [h₁, h₂, add_zero]
        smul_mem' := fun P₁ {P₂} h₂ => by
          simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
          change (Polynomial.aeval T_a P₁) ((Polynomial.aeval T_a P₂) u_S) = 0
          rw [h₂, map_zero] }
    have hΦ_mem : Polynomial.cyclotomic p ℚ ∈ I := hΦ_eval
    have hg_mem : g ∈ I := hg_eval
    have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
      Polynomial.cyclotomic.irreducible_rat hp.pos
    have h1_not_mem : (1 : Polynomial ℚ) ∉ I := by
      simp [I, huS_ne]
    -- Since Φ_p is irreducible and 1 ∉ I, gcd(g, Φ_p) = 1 or Φ_p ∣ g
    have hdvd : Polynomial.cyclotomic p ℚ ∣ g := by
      by_contra hndvd
      have hcop : IsCoprime g (Polynomial.cyclotomic p ℚ) :=
        hirr.coprime_iff_not_dvd.mpr hndvd |>.symm
      obtain ⟨a₁, b₁, hab⟩ := hcop
      have h1_mem : (1 : Polynomial ℚ) ∈ I := by
        rw [← hab]
        exact I.add_mem (I.smul_mem a₁ hg_mem) (I.smul_mem b₁ hΦ_mem)
      exact h1_not_mem h1_mem
    have hg_zero : g = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg_g
    intro j
    have hcs : ∀ (s : Finset (Fin (p - 1))) (F : Fin (p - 1) → Polynomial ℚ) (n : ℕ),
        (∑ i ∈ s, F i).coeff n = ∑ i ∈ s, (F i).coeff n := by
      intro s F n
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
  -- Now run Krylov chain W t ⊆ H_C
  let W : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
    Submodule.span ℚ {f | ∃ w : List α, w.length ≤ t ∧ ∃ j < p, f = pullbackLin A w ((T_a ^ j) u_S)}
  have hW0_finrank : p - 1 ≤ Module.finrank ℚ (W 0) := by
    have hspan_le : Submodule.span ℚ (Set.range (fun j : Fin (p - 1) => (T_a ^ j.1) u_S)) ≤ W 0 := by
      rw [Submodule.span_le]
      rintro f ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨[], by simp, j.1, by omega, by simp [pullbackLin_nil]⟩
    calc p - 1 = Fintype.card (Fin (p - 1)) := (Fintype.card_fin _).symm
      _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j : Fin (p - 1) => (T_a ^ j.1) u_S))) := by
          rw [finrank_span_eq_card hli_W0]
      _ ≤ Module.finrank ℚ (W 0) := Submodule.finrank_mono hspan_le
  have hne_ex : ∃ w' : List α, w'.length ≤ n - p + 1 ∧ ∃ j < p,
      σ_C (pullbackLin A w' ((T_a ^ j) u_S)) ≠ 0 := by
    by_contra hall0
    push_neg at hall0
    have hW_le_HC : ∀ t ≤ n - p + 1, W t ≤ H_C := by
      intro t ht
      rw [Submodule.span_le]
      rintro f ⟨w', hw', j, hj, rfl⟩
      change pullbackLin A w' ((T_a ^ j) u_S) ∈ H_C
      rw [LinearMap.mem_ker]
      exact hall0 w' (by omega) j hj
    have hW_mono : ∀ t, W t ≤ W (t + 1) := fun t => by
      apply Submodule.span_mono
      rintro f ⟨w', hw', j, hj, rfl⟩
      exact ⟨w', by omega, j, hj, rfl⟩
    have hstab : ∃ t < n - p + 1, W t = W (t + 1) := by
      by_contra hns
      push_neg at hns
      have hinc : ∀ t ≤ n - p + 1, p - 1 + t ≤ Module.finrank ℚ (W t) := by
        intro t ht
        induction t with
        | zero => simpa using hW0_finrank
        | succ t ih =>
          have hlt_sub : W t < W (t + 1) := lt_of_le_of_ne (hW_mono t) (hns t (by omega))
          have hlt_rk := Submodule.finrank_lt_finrank_of_lt hlt_sub
          have ih' := ih (by omega)
          omega
      have htop := hinc (n - p + 1) le_rfl
      have hle_HC : Module.finrank ℚ (W (n - p + 1)) ≤ Module.finrank ℚ H_C :=
        Submodule.finrank_mono (hW_le_HC (n - p + 1) le_rfl)
      rw [hfinrank_HC] at hle_HC
      have hp_le_n : p ≤ n := Finset.card_le_univ C
      omega
    obtain ⟨t, ht_lt, ht_eq⟩ := hstab
    have hinv : ∀ σ : α, ∀ f ∈ W t, pullbackLin A [σ] f ∈ W t := by
      intro σ f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨w', hw', j, hj, rfl⟩
        rw [ht_eq]
        apply Submodule.subset_span
        refine ⟨σ :: w', by simp; omega, j, hj, ?_⟩
        rw [pullbackLin_cons]
        rfl
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (W t).add_mem hx hy
      | smul k x _ hx => rw [map_smul]; exact (W t).smul_mem k hx
    have hall_in_Wt : ∀ w' : List α, pullbackLin A w' u_S ∈ W t := by
      intro w'
      induction w' with
      | nil =>
        rw [pullbackLin_nil]
        apply Submodule.span_mono (s := {f | ∃ u : List α, u.length ≤ 0 ∧ ∃ j < p, f = pullbackLin A u ((T_a ^ j) u_S)})
        · rintro f ⟨u, hu, j, hj, rfl⟩
          exact ⟨u, by omega, j, hj, rfl⟩
        · exact Submodule.subset_span ⟨[], le_rfl, 0, hp.pos, by simp [pullbackLin_nil]⟩
      | cons σ w' ih =>
        rw [pullbackLin_cons]
        exact hinv σ _ ih
    obtain ⟨u₀, hu₀⟩ := hsync
    rw [Aut.isSyncWord_iff_exists_eval_eq] at hu₀
    obtain ⟨q_star, hq_star⟩ := hu₀
    have hu₀_in_HC : pullbackLin A u₀ u_S ∈ H_C := hW_le_HC t (by omega) (hall_in_Wt u₀)
    rw [LinearMap.mem_ker, hsum_uS u₀] at hu₀_in_HC
    let c_star := A.eval q_star (List.replicate ℓ a)
    by_cases hcS : c_star ∈ S
    · have hpre_univ : A.preimage S (u₀ ++ List.replicate ℓ a) ∩ C = C := by
        ext q
        simp only [Finset.mem_inter, Aut.mem_preimage, Aut.eval_append, hq_star q,
          and_iff_right_iff_imp]
        intro _; exact hcS
      rw [hpre_univ] at hu₀_in_HC
      have : (p : ℚ) = (S.card : ℚ) := by linarith
      have : p = S.card := Nat.cast_injective this
      dsimp only [p, C] at this
      omega
    · have hpre_empty : A.preimage S (u₀ ++ List.replicate ℓ a) ∩ C = ∅ := by
        ext q
        simp [Aut.mem_preimage, Aut.eval_append, hq_star q, hcS, c_star]
      rw [hpre_empty, Finset.card_empty] at hu₀_in_HC
      simp only [Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero] at hu₀_in_HC
      omega
  obtain ⟨w', hw'_len, j₀, hj₀, hne0⟩ := hne_ex
  have hsum_pre_eq := one_cluster_cycle_double_count A a h1c hSC w'
  have hj₀_ne : (A.preimage S (w' ++ List.replicate (ℓ + j₀) a) ∩ C).card ≠ S.card := by
    intro heq
    apply hne0
    have hcomp : pullbackLin A w' ((T_a ^ j₀) u_S) = pullbackLin A (w' ++ List.replicate j₀ a) u_S := by
      rw [hTa_pow, pullbackLin_append]
      rfl
    rw [hcomp, hsum_uS]
    have hrep_eq : (w' ++ List.replicate j₀ a) ++ List.replicate ℓ a =
        w' ++ List.replicate (ℓ + j₀) a := by
      rw [List.append_assoc, ← List.replicate_add, add_comm j₀ ℓ]
    rw [hrep_eq, heq, sub_self]
  have hgt_ex : ∃ j ∈ Finset.range p,
      S.card < (A.preimage S (w' ++ List.replicate (ℓ + j) a) ∩ C).card := by
    by_contra hle_all
    push_neg at hle_all
    have hsum_le : ∑ j ∈ Finset.range p,
          (A.preimage S (w' ++ List.replicate (ℓ + j) a) ∩ C).card ≤
        ∑ _j ∈ Finset.range p, S.card := Finset.sum_le_sum hle_all
    have hsum_eq : ∑ j ∈ Finset.range p,
          (A.preimage S (w' ++ List.replicate (ℓ + j) a) ∩ C).card =
        ∑ _j ∈ Finset.range p, S.card := by
      dsimp only [p, ℓ, C]
      rw [hsum_pre_eq]; simp [Finset.sum_const, smul_eq_mul]
    have hall := (Finset.sum_eq_sum_iff_of_le hle_all).mp hsum_eq
    exact hj₀_ne (hall j₀ (Finset.mem_range.mpr hj₀))
  obtain ⟨j_pos, hj_pos, hj_gt⟩ := hgt_ex
  rw [Finset.mem_range] at hj_pos
  refine ⟨w' ++ List.replicate j_pos a, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    have hp_le_n : p ≤ n := Finset.card_le_univ C
    dsimp only [p, n] at hw'_len hj_pos hp_le_n
    omega
  · have hrep_eq : (w' ++ List.replicate j_pos a) ++ List.replicate ℓ a =
        w' ++ List.replicate (ℓ + j_pos) a := by
      rw [List.append_assoc, ← List.replicate_add, add_comm j_pos ℓ]
    rwa [hrep_eq]

/-- Steinberg's prime one-cluster theorem: if `A` is synchronizing and one-cluster
for `a` with `m = |C|` prime (or `m = 1`), then `A` has a synchronizing word of
length at most `(m - 1) * (n - 1) + m * ℓ ≤ (n - 1)^2`. -/
theorem one_cluster_prime_bound {Q α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A : Aut Q α) (hsync : A.IsSync) (a : α) (h1c : IsOneCluster A a)
    (hm : (cycleStates A a).card = 1 ∨ Nat.Prime (cycleStates A a).card) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (cycleStates A a).card.pred * (Fintype.card Q - 1) +
        (cycleStates A a).card * cycleLevel A a ∧
      (cycleStates A a).card.pred * (Fintype.card Q - 1) +
        (cycleStates A a).card * cycleLevel A a ≤ (Fintype.card Q - 1) ^ 2 := by
  let C := cycleStates A a
  let ℓ := cycleLevel A a
  let m := C.card
  let n := Fintype.card Q
  have hℓ_le : ℓ ≤ n - m := cycleLevel_le A a
  have hm_le_n : m ≤ n := Finset.card_le_univ C
  have hbound_le : m.pred * (n - 1) + m * ℓ ≤ (n - 1) ^ 2 := by
    have hm_pos : 1 ≤ m := (cycleStates_nonempty A a).card_pos
    have hmul : m * ℓ ≤ m * (n - m) := Nat.mul_le_mul_left m hℓ_le
    have hdiff : (n - m) ^ 2 ≥ n - m := by nlinarith
    have hm_eq : m = (m - 1) + 1 := by omega
    have hn_eq : n - 1 = (m - 1) + (n - m) := by omega
    calc m.pred * (n - 1) + m * ℓ
        = (m - 1) * (n - 1) + m * ℓ := rfl
      _ ≤ (m - 1) * (n - 1) + m * (n - m) := Nat.add_le_add_left hmul _
      _ = (m - 1) * (n - 1) + (m - 1) * (n - m) + (n - m) := by
          have hmul_eq : m * (n - m) = (m - 1) * (n - m) + (n - m) := by
            conv_lhs => lhs; rw [hm_eq]
            ring
          rw [hmul_eq]; ring
      _ ≤ (m - 1) * (n - 1) + (m - 1) * (n - m) + (n - m) ^ 2 := Nat.add_le_add_left hdiff _
      _ = (n - 1) ^ 2 := by rw [hn_eq]; ring
  rcases hm with hm1 | hp
  · -- m = 1: replicate ℓ a already synchronizes!
    obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hm1
    refine ⟨List.replicate ℓ a, ?_, ?_, hbound_le⟩
    · rw [Aut.isSyncWord_iff_exists_eval_eq]
      refine ⟨c₀, fun q => ?_⟩
      have hmem : A.eval q (List.replicate ℓ a) ∈ cycleStates A a :=
        eval_replicate_mem_cycleStates A a q 0
      rw [hc₀, Finset.mem_singleton] at hmem
      exact hmem
    · simp [hm1, ℓ]
  · -- m = p prime
    have hc2 : 2 ≤ m := hp.two_le
    obtain ⟨c₀, hc₀C, w₁, hw₁_len, hw₁_card⟩ := multi_cluster_initial_step A hsync a hc2
    let S₁ := A.preimage {c₀} (w₁ ++ List.replicate ℓ a) ∩ C
    have hS₁_sub : S₁ ⊆ C := Finset.inter_subset_right
    have hS₁_pre : S₁ ⊆ A.preimage {c₀} (w₁ ++ List.replicate ℓ a) := Finset.inter_subset_left
    -- Grow S ⊆ C from |S| ≥ 2 up to C
    have hgrow : ∀ d : ℕ, ∀ S : Finset Q, ∀ u : List α,
        S ⊆ C → S.card + d = m → 2 ≤ S.card →
        S ⊆ A.preimage {c₀} u → u.length ≤ (n - m + 1 + ℓ) + (S.card - 2) * (n + ℓ) →
        ∃ v : List α, C ⊆ A.preimage {c₀} v ∧
          v.length ≤ (n - m + 1 + ℓ) + (m - 2) * (n + ℓ) := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro S u hSC hd hS2 hSu hulen
        by_cases hd0 : d = 0
        · subst hd0
          have hSC_eq : S = C := Finset.eq_of_subset_of_card_le hSC (by omega)
          rw [← hSC_eq]
          exact ⟨u, hSu, by rw [show S.card = m by omega] at hulen; exact hulen⟩
        · have hS_lt : S.card < m := by omega
          obtain ⟨w, hw_len, hw_gt⟩ :=
            one_cluster_prime_extension A hsync a h1c hp hSC (by omega) hS_lt
          let S' := A.preimage S (w ++ List.replicate ℓ a) ∩ C
          have hS'_sub : S' ⊆ C := Finset.inter_subset_right
          have hS'_pre : S' ⊆ A.preimage {c₀} ((w ++ List.replicate ℓ a) ++ u) := by
            rw [← Aut.preimage_append]
            exact Finset.inter_subset_left.trans (A.preimage_mono hSu _)
          have hd' : S'.card + (m - S'.card) = m := by
            have := Finset.card_le_card hS'_sub
            omega
          have hS'_gt : S.card < S'.card := hw_gt
          have hd'_lt : m - S'.card < d := by omega
          have hlen' : ((w ++ List.replicate ℓ a) ++ u).length ≤
              (n - m + 1 + ℓ) + (S'.card - 2) * (n + ℓ) := by
            rw [List.length_append, List.length_append, List.length_replicate]
            have hmul1 : (S.card - 2) * (n + ℓ) + (n + ℓ) = (S.card - 1) * (n + ℓ) := by
              calc (S.card - 2) * (n + ℓ) + (n + ℓ) = (S.card - 2 + 1) * (n + ℓ) := by ring
                _ = (S.card - 1) * (n + ℓ) := by rw [show S.card - 2 + 1 = S.card - 1 by omega]
            have hmul2 : (S.card - 1) * (n + ℓ) ≤ (S'.card - 2) * (n + ℓ) :=
              Nat.mul_le_mul_right (n + ℓ) (by omega)
            omega
          exact ih (m - S'.card) hd'_lt S' ((w ++ List.replicate ℓ a) ++ u)
            hS'_sub hd' (by omega) hS'_pre hlen'
    obtain ⟨v, hv_sub, hv_len⟩ :=
      hgrow (m - S₁.card) S₁ (w₁ ++ List.replicate ℓ a) hS₁_sub
        (by have := Finset.card_le_card hS₁_sub; omega) hw₁_card hS₁_pre
        (by
          rw [List.length_append, List.length_replicate]
          exact le_trans (Nat.add_le_add_right hw₁_len ℓ) (Nat.le_add_right _ _))
    refine ⟨List.replicate ℓ a ++ v, ?_, ?_, hbound_le⟩
    · rw [Aut.isSyncWord_iff_preimage_univ]
      refine ⟨c₀, ?_⟩
      ext q
      simp only [Finset.mem_univ, iff_true, ← Aut.preimage_append]
      exact (Aut.mem_preimage A).mpr (hv_sub (eval_replicate_mem_cycleStates A a q 0))
    · rw [List.length_append, List.length_replicate]
      have harith : ℓ + ((n - m + 1 + ℓ) + (m - 2) * (n + ℓ)) =
          m.pred * (n - 1) + m * ℓ := by
        have hm1 : 1 ≤ m := by omega
        have hm2 : 2 ≤ m := hc2
        have hpred : m.pred = m - 1 := rfl
        rw [hpred]
        zify [hm1, hm2, hm_le_n, show 1 ≤ n by omega]
        ring
      exact le_trans (Nat.add_le_add_left hv_len ℓ) (le_of_eq harith)

end OneClusterPrime

end WeightedPrimeCycle
