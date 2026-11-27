import Cerny.Defs
import Cerny.Reduction
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Aperiodic Automata: `rt(A) ≤ ⌈3(n - 1)^2 / 4⌉`

This module formalizes Trahtman's theorem and the improved upper bound
`⌈3(n - 1)^2 / 4⌉ = (3 * (n - 1)^2 + (n - 1) % 2) / 4` for synchronizing
aperiodic automata:
1. `sink_scc_Gneq_exists`: existence of a sink SCC `M` in the pair graph `Gneq`.
2. `sink_scc_acyclic`: Trahtman's 8-line proof that `(Q, M)` is acyclic.
3. Stable partial order `leM`, congruence `equivM`, and `aperiodic_minmax_step`.
4. `aperiodic_bound`: `∃ w, A.IsSyncWord w ∧ w.length ≤ (3 * (n - 1)^2 + (n - 1) % 2) / 4`.
-/

namespace Aperiodic

/-- Repeated word `w^m`. -/
def iterWord {α : Type*} (w : List α) (m : ℕ) : List α :=
  (List.replicate m w).flatten

@[simp]
lemma iterWord_zero {α : Type*} (w : List α) : iterWord w 0 = [] := rfl

lemma iterWord_succ {α : Type*} (w : List α) (m : ℕ) :
    iterWord w (m + 1) = w ++ iterWord w m := by
  simp [iterWord, List.replicate_succ]

lemma iterWord_add {α : Type*} (w : List α) (a b : ℕ) :
    iterWord w (a + b) = iterWord w a ++ iterWord w b := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, iterWord_succ, ih, List.append_assoc]

lemma eval_iterWord_succ {Q α : Type*} (A : Aut Q α) (q : Q) (w : List α) (m : ℕ) :
    A.eval q (iterWord w (m + 1)) = A.eval (A.eval q (iterWord w m)) w := by
  calc A.eval q (iterWord w (m + 1))
      = A.eval q (iterWord w m ++ iterWord w 1) := by rw [iterWord_add]
    _ = A.eval (A.eval q (iterWord w m)) w := by simp [iterWord]

/-- An automaton is aperiodic if `q · w^m = q` (with `m ≥ 1`) implies `q · w = q`. -/
def IsAperiodic {Q α : Type*} (A : Aut Q α) : Prop :=
  ∀ (w : List α) (q : Q) (m : ℕ), 1 ≤ m → A.eval q (iterWord w m) = q → A.eval q w = q

section SinkGneq
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

private def ReachNeq (x y : {pq : Q × Q // pq.1 ≠ pq.2}) : Prop :=
  ∃ w : List α, (A.eval x.1.1 w, A.eval x.1.2 w) = y.1

private lemma reachNeq_refl (x : {pq : Q × Q // pq.1 ≠ pq.2}) : ReachNeq A x x :=
  ⟨[], rfl⟩

private lemma reachNeq_trans {x y z : {pq : Q × Q // pq.1 ≠ pq.2}}
    (hxy : ReachNeq A x y) (hyz : ReachNeq A y z) : ReachNeq A x z := by
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  refine ⟨u ++ v, ?_⟩
  simp only [Aut.eval_append]
  have h1 : A.eval x.1.1 u = y.1.1 := congrArg Prod.fst hu
  have h2 : A.eval x.1.2 u = y.1.2 := congrArg Prod.snd hu
  rw [h1, h2]
  exact hv

/-- For `|Q| ≥ 2`, there exists a nonempty, irreflexive, strongly connected sink
subset `M ⊆ Q × Q` in the pair graph `Gneq`. -/
theorem sink_scc_Gneq_exists (hn : 2 ≤ Fintype.card Q) :
    ∃ M : Finset (Q × Q),
      M.Nonempty ∧
      (∀ p q, (p, q) ∈ M → p ≠ q) ∧
      (∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M) ∧
      (∀ p q p' q', (p, q) ∈ M → (p', q') ∈ M →
        ∃ w : List α, A.eval p w = p' ∧ A.eval q w = q') := by
  classical
  have hpair : ∃ p q : Q, p ≠ q := by
    have h1 : 1 < (Finset.univ : Finset Q).card := by rw [Finset.card_univ]; exact hn
    obtain ⟨p, _, q, _, hpq⟩ := Finset.one_lt_card.mp h1
    exact ⟨p, q, hpq⟩
  obtain ⟨p₀, q₀, hpq₀⟩ := hpair
  let V := {pq : Q × Q // pq.1 ≠ pq.2}
  let x₀ : V := ⟨(p₀, q₀), hpq₀⟩
  haveI : Nonempty V := ⟨x₀⟩
  let R : V → Finset V := fun x => Finset.univ.filter (fun y => ReachNeq A x y)
  obtain ⟨x_min, _, hx_min⟩ := Finset.exists_min_image (Finset.univ : Finset V) (fun x => (R x).card)
    Finset.univ_nonempty
  let M : Finset (Q × Q) := (R x_min).image Subtype.val
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · refine ⟨x_min.1, Finset.mem_image_of_mem _ ?_⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact reachNeq_refl A x_min
  · intro p q hpq
    rcases Finset.mem_image.mp hpq with ⟨y, _, hy⟩
    have := y.2
    rw [hy] at this
    exact this
  · intro p q hpq a
    by_cases heq : A.step p a = A.step q a
    · left; exact heq
    · right
      rcases Finset.mem_image.mp hpq with ⟨y, hyR, hy_eq⟩
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
      let z : V := ⟨(A.step p a, A.step q a), heq⟩
      refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      apply reachNeq_trans A hyR
      refine ⟨[a], ?_⟩
      change (A.step y.1.1 a, A.step y.1.2 a) = (A.step p a, A.step q a)
      rw [hy_eq]
  · intro p q p' q' hpq hpq'
    rcases Finset.mem_image.mp hpq with ⟨y, hyR, hy_eq⟩
    rcases Finset.mem_image.mp hpq' with ⟨y', hy'R, hy'_eq⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hyR hy'R
    have hsub : R y ⊆ R x_min := by
      intro z hz
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact reachNeq_trans A hyR hz
    have hcard_eq : (R y).card = (R x_min).card :=
      le_antisymm (Finset.card_le_card hsub) (hx_min y (Finset.mem_univ y))
    have hReq : R y = R x_min := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hy'_in_Ry : y' ∈ R y := by
      rw [hReq]
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy'R
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hy'_in_Ry
    obtain ⟨w, hw⟩ := hy'_in_Ry
    refine ⟨w, ?_, ?_⟩
    · have := congrArg Prod.fst hw
      have hy1 : y.1.1 = p := congrArg Prod.fst hy_eq
      have hy'1 : y'.1.1 = p' := congrArg Prod.fst hy'_eq
      rwa [hy1, hy'1] at this
    · have := congrArg Prod.snd hw
      have hy2 : y.1.2 = q := congrArg Prod.snd hy_eq
      have hy'2 : y'.1.2 = q' := congrArg Prod.snd hy'_eq
      rwa [hy2, hy'2] at this

end SinkGneq

section Acyclic
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

private lemma exists_simple_cycle_of_walk (M : Finset (Q × Q)) :
    ∀ L : ℕ, 2 ≤ L → ∀ v : ℕ → Q,
      (∀ i, v (i + L) = v i) →
      (∀ i, v i = v (i + 1) ∨ (v i, v (i + 1)) ∈ M) →
      (∃ i < L, v i ≠ v (i + 1)) →
      ∃ (r : ℕ) (_ : 2 ≤ r), r ≤ L ∧ ∃ q : Fin r → Q, Function.Injective q ∧
        ∀ i : Fin r, (q i, q ⟨(i.1 + 1) % r, Nat.mod_lt _ (by omega)⟩) ∈ M := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro hL2 v hper hadj hne
    have hv_mod : ∀ i, v (i % L) = v i := by
      intro i
      have hdiv := Nat.div_add_mod i L
      have hmul : ∀ m k, v (L * m + k) = v k := by
        intro m k
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [Nat.mul_succ, add_assoc, add_comm L k, ← add_assoc, hper, ihm]
      conv_rhs => rw [← hdiv, hmul]
    by_cases h_eq_adj : ∃ i < L, v i = v (i + 1)
    · obtain ⟨i₀, hi₀_lt, hi₀⟩ := h_eq_adj
      have hL3 : 3 ≤ L := by
        by_contra hlt
        have hL_eq : L = 2 := by omega
        subst hL_eq
        obtain ⟨j, hj_lt, hj⟩ := hne
        have h01 : v 0 = v 1 := by
          rcases (by omega : i₀ = 0 ∨ i₀ = 1) with rfl | rfl
          · exact hi₀
          · have h2 : v 2 = v 0 := by simpa using hper 0
            rw [h2] at hi₀; exact hi₀.symm
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · exact hj h01
        · have h2 : v 2 = v 0 := by simpa using hper 0
          rw [h2] at hj; exact hj h01.symm
      -- Rotate v by i₀ + 1 so the duplicate is at L - 1, L
      let rot : ℕ → Q := fun k => v (i₀ + 1 + k)
      have hrot_per : ∀ k, rot (k + L) = rot k := fun k => by
        dsimp only [rot]; rw [← add_assoc]; exact hper _
      have hrot_last : rot (L - 1) = rot 0 := by
        dsimp only [rot]
        rw [show i₀ + 1 + (L - 1) = i₀ + L by omega, hper, add_zero]
        exact hi₀
      -- Drop index L - 1 by mapping k ↦ rot (k / (L - 1) * L + k % (L - 1))
      let v' : ℕ → Q := fun k => rot (k % (L - 1))
      have hv'_per : ∀ k, v' (k + (L - 1)) = v' k := fun k => by
        dsimp only [v']; rw [Nat.add_mod_right]
      have hv'_lt : ∀ k < L - 1, v' k = rot k := fun k hk => by
        dsimp only [v']; rw [Nat.mod_eq_of_lt hk]
      have hv'_adj : ∀ k, v' k = v' (k + 1) ∨ (v' k, v' (k + 1)) ∈ M := by
        intro k
        have hmod_lt : k % (L - 1) < L - 1 := Nat.mod_lt _ (by omega)
        dsimp only [v']
        by_cases hk : k % (L - 1) = L - 2
        · have hnext : (k + 1) % (L - 1) = 0 := by
            rw [Nat.add_mod, hk, Nat.mod_eq_of_lt (by omega : 1 < L - 1),
              show L - 2 + 1 = L - 1 by omega, Nat.mod_self]
          rw [hk, hnext, ← hrot_last]
          have h := hadj (i₀ + 1 + (L - 2))
          rwa [show i₀ + 1 + (L - 2) + 1 = i₀ + 1 + (L - 1) by omega] at h
        · have hnext : (k + 1) % (L - 1) = k % (L - 1) + 1 := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L - 1),
              Nat.mod_eq_of_lt (by omega)]
          rw [hnext]
          simpa [rot, add_assoc] using hadj (i₀ + 1 + k % (L - 1))
      have hv'_ne : ∃ k < L - 1, v' k ≠ v' (k + 1) := by
        obtain ⟨j, hj_lt, hj⟩ := hne
        let k := (j + L - (i₀ + 1)) % L
        have hk_lt : k < L := Nat.mod_lt _ (by omega)
        have hrot_k : rot k = v j := by
          dsimp only [rot, k]
          conv_lhs => rw [← hv_mod]
          have hmod1 : (i₀ + 1 + (j + L - (i₀ + 1)) % L) % L = j := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have h2 : i₀ + 1 + (j + L - (i₀ + 1)) = j + L := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj_lt]
          rw [hmod1]
        have hrot_k1 : rot (k + 1) = v (j + 1) := by
          dsimp only [rot, k]
          conv_lhs => rw [← hv_mod]
          have hmod1 : (i₀ + 1 + ((j + L - (i₀ + 1)) % L + 1)) % L = (j + 1) % L := by
            have h1 : (i₀ + 1 + ((j + L - (i₀ + 1)) % L + 1)) % L =
                (i₀ + 1 + (j + L - (i₀ + 1) + 1)) % L := by
              simp only [Nat.add_mod, Nat.mod_mod]
            have h2 : i₀ + 1 + (j + L - (i₀ + 1) + 1) = (j + 1) + L := by omega
            rw [h1, h2, Nat.add_mod_right]
          rw [hmod1, hv_mod]
        have hk_ne : k ≠ L - 1 := by
          intro heq
          rw [heq, hrot_last] at hrot_k
          have hk1 : rot (L - 1 + 1) = rot 0 := by
            rw [show L - 1 + 1 = 0 + L by omega, hrot_per]
          rw [heq, hk1] at hrot_k1
          exact hj (hrot_k.symm.trans hrot_k1)
        refine ⟨k, by omega, ?_⟩
        rw [hv'_lt k (by omega)]
        by_cases hk2 : k = L - 2
        · have hv'_eq : v' (k + 1) = rot 0 := by
            dsimp only [v']
            rw [hk2, show L - 2 + 1 = L - 1 by omega, Nat.mod_self]
          rw [hv'_eq, ← hrot_last, show L - 1 = k + 1 by omega, hrot_k, hrot_k1]
          exact hj
        · rw [hv'_lt (k + 1) (by omega), hrot_k, hrot_k1]
          exact hj
      obtain ⟨r, hr2, hrL, q, hq_inj, hq_M⟩ := ih (L - 1) (by omega) (by omega) v' hv'_per hv'_adj hv'_ne
      exact ⟨r, hr2, hrL.trans (by omega), q, hq_inj, hq_M⟩
    · push_neg at h_eq_adj
      by_cases hinj : Set.InjOn v (Finset.range L)
      · refine ⟨L, hL2, le_rfl, fun i => v i.1, fun i j hij => Fin.ext (hinj (by simp) (by simp) hij), ?_⟩
        intro i
        by_cases hi : i.1 + 1 = L
        · have hmod : (i.1 + 1) % L = 0 := by rw [hi, Nat.mod_self]
          simp only [hmod]
          have hper0 : v 0 = v (i.1 + 1) := by rw [hi, ← zero_add L, hper]
          rw [hper0]
          rcases hadj i.1 with heq | hmem
          · exact absurd heq (h_eq_adj i.1 i.2)
          · exact hmem
        · have hmod : (i.1 + 1) % L = i.1 + 1 := Nat.mod_eq_of_lt (by omega)
          simp only [hmod]
          rcases hadj i.1 with heq | hmem
          · exact absurd heq (h_eq_adj i.1 i.2)
          · exact hmem
      · simp only [Set.InjOn, Finset.coe_range, Set.mem_Iio, not_forall] at hinj
        obtain ⟨i, hi, j, hj, hij, hne_ij⟩ := hinj
        wlog hlt : i < j generalizing i j
        · exact this j hj i hi hij.symm (Ne.symm hne_ij) (by omega)
        let r := j - i
        have hr2 : 2 ≤ r := by
          by_contra hr_lt
          have hj_eq : j = i + 1 := by omega
          rw [hj_eq] at hij
          exact h_eq_adj i hi hij
        have hr_lt : r < L := by omega
        let v' : ℕ → Q := fun k => v (i + k % r)
        have hv'_per : ∀ k, v' (k + r) = v' k := fun k => by
          dsimp only [v']; rw [Nat.add_mod_right]
        have hv'_adj : ∀ k, v' k = v' (k + 1) ∨ (v' k, v' (k + 1)) ∈ M := by
          intro k
          dsimp only [v']
          have hmod_lt : k % r < r := Nat.mod_lt _ (by omega)
          by_cases hk : k % r = r - 1
          · have hnext : (k + 1) % r = 0 := by
              rw [Nat.add_mod, hk, Nat.mod_eq_of_lt (by omega : 1 < r),
                show r - 1 + 1 = r by omega, Nat.mod_self]
            rw [hk, hnext, add_zero, hij]
            have h := hadj (i + (r - 1))
            rwa [show i + (r - 1) + 1 = j by omega] at h
          · have hnext : (k + 1) % r = k % r + 1 := by
              rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < r), Nat.mod_eq_of_lt (by omega)]
            rw [hnext, ← add_assoc]
            exact hadj (i + k % r)
        have hv'_ne : ∃ k < r, v' k ≠ v' (k + 1) := by
          refine ⟨0, by omega, ?_⟩
          dsimp only [v']
          rw [Nat.zero_mod, add_zero, Nat.mod_eq_of_lt (by omega : 1 < r)]
          exact h_eq_adj i hi
        obtain ⟨r', hr'2, hr'L, q, hq_inj, hq_M⟩ := ih r hr_lt hr2 v' hv'_per hv'_adj hv'_ne
        exact ⟨r', hr'2, hr'L.trans (by omega), q, hq_inj, hq_M⟩

/-- Trahtman's acyclicity theorem: if `A` is aperiodic and `M` is a sink SCC in `Gneq`,
then `(Q, M)` has no directed cycle of length `≥ 2`. -/
theorem sink_scc_acyclic (hap : IsAperiodic A) (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    (hscc : ∀ p q p' q', (p, q) ∈ M → (p', q') ∈ M →
      ∃ w : List α, A.eval p w = p' ∧ A.eval q w = q') :
    ∀ (r : ℕ) (hr : 2 ≤ r) (q : Fin r → Q), Function.Injective q →
      ¬ ∀ i : Fin r, (q i, q ⟨(i.1 + 1) % r, Nat.mod_lt _ (by omega)⟩) ∈ M := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr2 q hq_inj hcycle
    haveI : NeZero r := ⟨by omega⟩
    have hstep_w : ∀ p p' : Q, (p, p') ∈ M → ∀ w : List α,
        A.eval p w = A.eval p' w ∨ (A.eval p w, A.eval p' w) ∈ M := by
      intro p p' hpp' w
      induction w generalizing p p' with
      | nil => right; exact hpp'
      | cons a w ihw =>
        rcases hsink p p' hpp' a with heq | hmem
        · left; simp [heq]
        · exact ihw _ _ hmem
    by_cases hr_eq : r = 2
    · subst hr_eq
      have h01 : (q 0, q 1) ∈ M := by simpa using hcycle 0
      have h10 : (q 1, q 0) ∈ M := by simpa using hcycle 1
      obtain ⟨w, hw0, hw1⟩ := hscc (q 0) (q 1) (q 1) (q 0) h01 h10
      have hw2 : A.eval (q 0) (iterWord w 2) = q 0 := by
        rw [eval_iterWord_succ]
        simp [iterWord, hw0, hw1]
      have h1 : A.eval (q 0) w = q 0 := hap w (q 0) 2 (by omega) hw2
      rw [hw0] at h1
      have h01_eq : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := hq_inj h1.symm
      cases h01_eq
    · have hr3 : 3 ≤ r := by omega
      haveI : NeZero r := ⟨by omega⟩
      have h01 : (q 0, q 1) ∈ M := by
        have h0 : (⟨0, by omega⟩ : Fin r) = 0 := rfl
        have h1 : (⟨(0 + 1) % r, Nat.mod_lt _ (by omega)⟩ : Fin r) = 1 :=
          Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : 1 < r)])
        simpa [h0, h1] using hcycle ⟨0, by omega⟩
      have h12 : (q 1, q 2) ∈ M := by
        have h1 : (⟨1, by omega⟩ : Fin r) = 1 :=
          Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : 1 < r)])
        have h2 : (⟨(1 + 1) % r, Nat.mod_lt _ (by omega)⟩ : Fin r) = 2 :=
          Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : 2 < r)])
        simpa [h1, h2] using hcycle ⟨1, by omega⟩
      obtain ⟨w, hw0, hw1⟩ := hscc (q 0) (q 1) (q 1) (q 2) h01 h12
      have hq12 : q 1 ≠ q 2 := by
        intro h
        have h12_eq := congrArg Fin.val (hq_inj h)
        simp [Nat.mod_eq_of_lt (by omega : 1 < r), Nat.mod_eq_of_lt (by omega : 2 < r)] at h12_eq
      -- By finitude of Q, there exists k ≥ 1 such that q 0 · w^(k+1) = q 0 · w^k
      have hstab_ex : ∃ k : ℕ, 1 ≤ k ∧ A.eval (q 0) (iterWord w (k + 1)) = A.eval (q 0) (iterWord w k) := by
        have hnotinj : ¬ Function.Injective (fun m : Fin (Fintype.card Q + 1) =>
            A.eval (q 0) (iterWord w m.1)) := by
          intro hinj
          have := Fintype.card_le_of_injective _ hinj
          rw [Fintype.card_fin] at this
          omega
        simp only [Function.Injective, not_forall] at hnotinj
        obtain ⟨a, b, hab, hne_ab⟩ := hnotinj
        have hlt_ab : a < b ∨ b < a := lt_or_gt_of_ne hne_ab
        suffices ∀ x y : Fin (Fintype.card Q + 1), x < y →
            A.eval (q 0) (iterWord w x.1) = A.eval (q 0) (iterWord w y.1) →
            ∃ k : ℕ, 1 ≤ k ∧ A.eval (q 0) (iterWord w (k + 1)) = A.eval (q 0) (iterWord w k) by
          rcases hlt_ab with h | h
          · exact this a b h hab
          · exact this b a h hab.symm
        intro x y hxy hxy_eq
        have hperiod : A.eval (A.eval (q 0) (iterWord w x.1)) (iterWord w (y.1 - x.1)) =
            A.eval (q 0) (iterWord w x.1) := by
          rw [← Aut.eval_append, ← iterWord_add, Nat.add_sub_cancel' (by omega : x.1 ≤ y.1)]
          exact hxy_eq.symm
        have hap_step := hap w (A.eval (q 0) (iterWord w x.1)) (y.1 - x.1) (by omega) hperiod
        rw [← eval_iterWord_succ] at hap_step
        by_cases hx0 : x.1 = 0
        · have hq0w : A.eval (q 0) w = q 0 := by
            simpa [hx0, iterWord] using hap_step
          refine ⟨1, le_rfl, ?_⟩
          rw [eval_iterWord_succ, eval_iterWord_succ]
          simp [iterWord, hq0w]
        · exact ⟨x.1, by omega, hap_step⟩
      let k := Nat.find hstab_ex
      have hk_spec := Nat.find_spec hstab_ex
      have hk1 : 1 ≤ k := hk_spec.1
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk_eq : k = 1 := by omega
        have heq := hk_spec.2
        change A.eval (q 0) (iterWord w (k + 1)) = A.eval (q 0) (iterWord w k) at heq
        rw [hk_eq, eval_iterWord_succ] at heq
        simp only [iterWord, List.replicate_one, List.flatten_cons, List.flatten_nil,
          List.append_nil] at heq
        rw [hw0, hw1] at heq
        exact hq12 heq.symm
      let u := iterWord w (k - 1)
      have h01_ne : A.eval (q 0) u ≠ A.eval (q 1) u := by
        intro heq
        have hlt_k : k - 1 < k := by omega
        have hmin := Nat.find_min hstab_ex hlt_k
        apply hmin
        refine ⟨by omega, ?_⟩
        have hL : A.eval (q 0) (iterWord w (k - 1 + 1)) = A.eval (q 1) u := by
          rw [show k - 1 + 1 = 1 + (k - 1) by omega, iterWord_add, Aut.eval_append]
          simp [iterWord, hw0, u]
        rw [hL]
        exact heq.symm
      have h12_eq : A.eval (q 1) u = A.eval (q 2) u := by
        have hL : A.eval (q 1) u = A.eval (q 0) (iterWord w k) := by
          rw [show k = 1 + (k - 1) by omega, iterWord_add, Aut.eval_append]
          simp [iterWord, hw0, u]
        have hR : A.eval (q 2) u = A.eval (q 0) (iterWord w (k + 1)) := by
          rw [show k + 1 = 2 + (k - 1) by omega, iterWord_add, Aut.eval_append]
          have h2 : A.eval (q 0) (iterWord w 2) = q 2 := by
            rw [eval_iterWord_succ]; simp [iterWord, hw0, hw1]
          rw [h2]
        rw [hL, hR]
        exact hk_spec.2.symm
      -- Build periodic walk of period r - 1 without Fin (r - 1) dependent casts
      let v : ℕ → Q := fun j =>
        if j % (r - 1) = 0 then A.eval (q 0) u
        else A.eval (q ⟨j % (r - 1) + 1, by have := Nat.mod_lt j (by omega : 0 < r - 1); omega⟩) u
      have hv_per : ∀ j, v (j + (r - 1)) = v j := fun j => by
        dsimp only [v]; simp [Nat.add_mod_right]
      have hv0_adj : ∀ j : ℕ, j < r - 1 →
          v j = v (j + 1) ∨ (v j, v (j + 1)) ∈ M := by
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          have hv0_eq : v 0 = A.eval (q 0) u := by simp [v]
          have hv1_eq : v 1 = A.eval (q 2) u := by
            have h1mod : 1 % (r - 1) = 1 := Nat.mod_eq_of_lt (by omega)
            have hq2 : (⟨2, by omega⟩ : Fin r) = 2 :=
              Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : 2 < r)])
            simp [v, h1mod, hq2]
          rw [hv0_eq, hv1_eq, ← h12_eq]
          exact hstep_w (q 0) (q 1) h01 u
        · by_cases hj_last : j = r - 2
          · subst hj_last
            have hvj_eq : v (r - 2) = A.eval (q ⟨r - 1, by omega⟩) u := by
              have hmod : (r - 2) % (r - 1) = r - 2 := Nat.mod_eq_of_lt (by omega)
              simp [v, hmod, hj0, show r - 2 + 1 = r - 1 by omega]
            have hvnext_eq : v (r - 2 + 1) = A.eval (q 0) u := by
              have hmod : (r - 2 + 1) % (r - 1) = 0 := by
                rw [show r - 2 + 1 = r - 1 by omega, Nat.mod_self]
              simp [v, hmod]
            rw [hvj_eq, hvnext_eq]
            have hmem := hcycle ⟨r - 1, by omega⟩
            have hq_eq : q ⟨(r - 1 + 1) % r, Nat.mod_lt _ (by omega)⟩ = q 0 :=
              congrArg q (Fin.ext (by simp [show r - 1 + 1 = r by omega]))
            rw [hq_eq] at hmem
            exact hstep_w _ _ hmem u
          · have hvj_eq : v j = A.eval (q ⟨j + 1, by omega⟩) u := by
              have hmod : j % (r - 1) = j := Nat.mod_eq_of_lt hj
              simp [v, hmod, hj0]
            have hvnext_eq : v (j + 1) = A.eval (q ⟨j + 2, by omega⟩) u := by
              have hmod : (j + 1) % (r - 1) = j + 1 := Nat.mod_eq_of_lt (by omega)
              simp [v, hmod, show j + 1 ≠ 0 by omega]
            rw [hvj_eq, hvnext_eq]
            have hmem := hcycle ⟨j + 1, by omega⟩
            have hq_eq : q ⟨(j + 1 + 1) % r, Nat.mod_lt _ (by omega)⟩ = q ⟨j + 2, by omega⟩ :=
              congrArg q (Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : j + 2 < r)]))
            rw [hq_eq] at hmem
            exact hstep_w _ _ hmem u
      have hv_adj : ∀ j, v j = v (j + 1) ∨ (v j, v (j + 1)) ∈ M := by
        intro j
        have h1 : v j = v (j % (r - 1)) := by dsimp only [v]; simp [Nat.mod_mod]
        have h2 : v (j + 1) = v (j % (r - 1) + 1) := by
          dsimp only [v]; simp [Nat.add_mod, Nat.mod_mod]
        rw [h1, h2]
        exact hv0_adj (j % (r - 1)) (Nat.mod_lt _ (by omega))
      have hv_ne : ∃ j < r - 1, v j ≠ v (j + 1) := by
        refine ⟨0, by omega, ?_⟩
        have hv0_eq : v 0 = A.eval (q 0) u := by simp [v]
        have hv1_eq : v 1 = A.eval (q ⟨2, by omega⟩) u := by
          have h1mod : 1 % (r - 1) = 1 := Nat.mod_eq_of_lt (by omega)
          simp [v, h1mod]
        rw [hv0_eq, hv1_eq]
        have hq2 : (⟨2, by omega⟩ : Fin r) = 2 := by
          ext; simp [Nat.mod_eq_of_lt (by omega : 2 < r)]
        rw [hq2, ← h12_eq]
        exact h01_ne
      obtain ⟨r', hr'2, hr'L, q', hq'_inj, hq'_M⟩ :=
        exists_simple_cycle_of_walk M (r - 1) (by omega) v hv_per hv_adj hv_ne
      exact ih r' (by omega) hr'2 q' hq'_inj hq'_M

end Acyclic

section PartialOrderAndQuotient
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Reflexive-transitive closure of `M`. -/
def leM (M : Finset (Q × Q)) (p q : Q) : Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ M) p q

/-- Equivalence closure of `M` (weakly connected components). -/
def equivM (M : Finset (Q × Q)) (p q : Q) : Prop :=
  Relation.EqvGen (fun x y => (x, y) ∈ M) p q

lemma leM_refl (M : Finset (Q × Q)) (p : Q) : leM M p p :=
  Relation.ReflTransGen.refl

lemma leM_trans {M : Finset (Q × Q)} {p q r : Q} (hpq : leM M p q) (hqr : leM M q r) :
    leM M p r :=
  Relation.ReflTransGen.trans hpq hqr

lemma leM_of_mem {M : Finset (Q × Q)} {p q : Q} (h : (p, q) ∈ M) : leM M p q :=
  Relation.ReflTransGen.single h

lemma leM_step {M : Finset (Q × Q)}
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    {p q : Q} (hpq : leM M p q) (a : α) : leM M (A.step p a) (A.step q a) := by
  induction hpq with
  | refl => exact leM_refl M _
  | tail _ hbc ih =>
    rcases hsink _ _ hbc a with heq | hmem
    · rw [← heq]; exact ih
    · exact leM_trans ih (leM_of_mem hmem)

lemma leM_eval {M : Finset (Q × Q)}
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    {p q : Q} (hpq : leM M p q) (w : List α) : leM M (A.eval p w) (A.eval q w) := by
  induction w generalizing p q with
  | nil => exact hpq
  | cons a w ih => exact ih (leM_step A hsink hpq a)

lemma leM_antisymm {M : Finset (Q × Q)}
    (hacyc : ∀ (r : ℕ) (hr : 2 ≤ r) (q : Fin r → Q), Function.Injective q →
      ¬ ∀ i : Fin r, (q i, q ⟨(i.1 + 1) % r, Nat.mod_lt _ (by omega)⟩) ∈ M)
    (hirr : ∀ p q, (p, q) ∈ M → p ≠ q)
    {p q : Q} (hpq : leM M p q) (hqp : leM M q p) : p = q := by
  by_contra hne
  have hpath : ∀ x y : Q, leM M x y →
      ∃ l : List Q, l ≠ [] ∧ l.head? = some x ∧ l.getLast? = some y ∧
        ∀ i (hi : i + 1 < l.length), (l[i], l[i + 1]) ∈ M := by
    intro x y hxy
    induction hxy with
    | refl => exact ⟨[x], by simp, rfl, rfl, fun i hi => by simp at hi⟩
    | @tail b c _ hbc ih =>
      obtain ⟨l, hl_ne, hhead, hlast, hchain⟩ := ih
      refine ⟨l ++ [c], by simp, ?_, by simp, ?_⟩
      · cases l with
        | nil => exact absurd rfl hl_ne
        | cons _ _ => exact hhead
      · intro i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hi1 : i + 1 < l.length
        · simpa [List.getElem_append_left (by omega : i < l.length),
            List.getElem_append_left hi1] using hchain i hi1
        · have hi_eq : i = l.length - 1 := by omega
          have hlast_eq : l[l.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hl_ne) Nat.one_pos) = b := by
            rw [← List.getLast_eq_getElem hl_ne]
            have hgl := List.getLast?_eq_some_getLast hl_ne
            rw [hlast] at hgl
            exact Option.some.inj hgl.symm
          simp only [hi_eq, Nat.sub_add_cancel (List.length_pos_of_ne_nil hl_ne)]
          rw [List.getElem_append_left (Nat.sub_lt (List.length_pos_of_ne_nil hl_ne) Nat.one_pos),
            List.getElem_append_right le_rfl]
          simp [hlast_eq, hbc]
  obtain ⟨l₁, hl₁_ne, hh₁, hl₁, hc₁⟩ := hpath p q hpq
  obtain ⟨l₂, hl₂_ne, hh₂, hl₂, hc₂⟩ := hpath q p hqp
  have hl₁_len : 2 ≤ l₁.length := by
    by_contra hlt
    have hlen1 : l₁.length = 1 := by have := List.length_pos_of_ne_nil hl₁_ne; omega
    rcases l₁ with _ | ⟨a, _ | ⟨b, t⟩⟩
    · exact hl₁_ne rfl
    · simp at hh₁ hl₁; exact hne (hh₁.symm.trans hl₁)
    · simp at hlen1
  have hl₂_len : 2 ≤ l₂.length := by
    by_contra hlt
    have hlen2 : l₂.length = 1 := by have := List.length_pos_of_ne_nil hl₂_ne; omega
    rcases l₂ with _ | ⟨a, _ | ⟨b, t⟩⟩
    · exact hl₂_ne rfl
    · simp at hh₂ hl₂; exact hne (hl₂.symm.trans hh₂)
    · simp at hlen2
  let walk := l₁.dropLast ++ l₂.dropLast
  have hwalk_len : 2 ≤ walk.length := by
    simp only [walk, List.length_append, List.length_dropLast]
    omega
  let v : ℕ → Q := fun i => walk[i % walk.length]'(Nat.mod_lt _ (by omega))
  have hv_per : ∀ i, v (i + walk.length) = v i := fun i => by
    dsimp only [v]; simp [Nat.add_mod_right]
  have hv0_adj : ∀ i < walk.length, (v i, v (i + 1)) ∈ M := by
    intro i hi
    dsimp only [v]
    simp only [Nat.mod_eq_of_lt hi]
    have h1_len : l₁.dropLast.length = l₁.length - 1 := List.length_dropLast
    have h2_len : l₂.dropLast.length = l₂.length - 1 := List.length_dropLast
    have hw_len : walk.length = l₁.dropLast.length + l₂.dropLast.length := List.length_append
    by_cases hi1 : i + 1 < l₁.dropLast.length
    · have hmod1 : (i + 1) % walk.length = i + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hmod1]
      dsimp only [walk]
      rw [List.getElem_append_left (by omega), List.getElem_append_left hi1,
        List.getElem_dropLast, List.getElem_dropLast]
      exact hc₁ i (by omega)
    · by_cases hi_end1 : i + 1 = l₁.dropLast.length
      · have hmod1 : (i + 1) % walk.length = i + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [hmod1]
        dsimp only [walk]
        rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega),
          List.getElem_dropLast, List.getElem_dropLast]
        have hlast₁ : l₁[l₁.length - 1]'(by omega) = q := by
          rw [← List.getLast_eq_getElem hl₁_ne]
          have := List.getLast?_eq_some_getLast hl₁_ne
          rw [hl₁] at this
          exact Option.some.inj this.symm
        have hhead₂ : l₂[0]'(by omega) = q := by
          rw [← List.head_eq_getElem hl₂_ne]
          have := List.head?_eq_some_head hl₂_ne
          rw [hh₂] at this
          exact Option.some.inj this.symm
        have hsub0 : i + 1 - l₁.dropLast.length = 0 := by omega
        simp only [hsub0, hhead₂]
        have h := hc₁ i (by omega)
        simp only [show i + 1 = l₁.length - 1 by omega] at h
        rwa [hlast₁] at h
      · by_cases hi2 : i + 1 < walk.length
        · have hmod1 : (i + 1) % walk.length = i + 1 := Nat.mod_eq_of_lt hi2
          simp only [hmod1]
          dsimp only [walk]
          rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
            List.getElem_dropLast, List.getElem_dropLast]
          have hsub : i - l₁.dropLast.length + 1 = i + 1 - l₁.dropLast.length := by omega
          simp only [← hsub]
          exact hc₂ (i - l₁.dropLast.length) (by omega)
        · have hi_last : i = walk.length - 1 := by omega
          have hmod : (i + 1) % walk.length = 0 := by
            rw [hi_last, Nat.sub_add_cancel (by omega : 1 ≤ walk.length), Nat.mod_self]
          simp only [hmod]
          dsimp only [walk]
          rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega),
            List.getElem_dropLast, List.getElem_dropLast]
          have hlast₂ : l₂[l₂.length - 1]'(by omega) = p := by
            rw [← List.getLast_eq_getElem hl₂_ne]
            have := List.getLast?_eq_some_getLast hl₂_ne
            rw [hl₂] at this
            exact Option.some.inj this.symm
          have hhead₁ : l₁[0]'(by omega) = p := by
            rw [← List.head_eq_getElem hl₁_ne]
            have := List.head?_eq_some_head hl₁_ne
            rw [hh₁] at this
            exact Option.some.inj this.symm
          rw [hhead₁]
          have h := hc₂ (i - l₁.dropLast.length) (by omega)
          simp only [show i - l₁.dropLast.length + 1 = l₂.length - 1 by omega] at h
          rwa [hlast₂] at h
  have hv_adj : ∀ i, v i = v (i + 1) ∨ (v i, v (i + 1)) ∈ M := by
    intro i
    right
    have h1 : v i = v (i % walk.length) := by dsimp only [v]; simp [Nat.mod_mod]
    have h2 : v (i + 1) = v (i % walk.length + 1) := by
      dsimp only [v]; simp [Nat.add_mod, Nat.mod_mod]
    rw [h1, h2]
    exact hv0_adj (i % walk.length) (Nat.mod_lt _ (by omega))
  have hv_ne : ∃ i < walk.length, v i ≠ v (i + 1) :=
    ⟨0, by omega, hirr _ _ (hv0_adj 0 (by omega))⟩
  obtain ⟨r, hr2, _, q', hq'_inj, hq'_M⟩ :=
    exists_simple_cycle_of_walk M walk.length hwalk_len v hv_per hv_adj hv_ne
  exact hacyc r hr2 q' hq'_inj hq'_M

lemma equivM_step {M : Finset (Q × Q)}
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    {p q : Q} (hpq : equivM M p q) (a : α) : equivM M (A.step p a) (A.step q a) := by
  induction hpq with
  | rel x y hxy =>
    rcases hsink x y hxy a with heq | hmem
    · rw [heq]; exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ hmem
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

def equivSetoid (M : Finset (Q × Q)) : Setoid Q where
  r := equivM M
  iseqv := Relation.EqvGen.is_equivalence _

/-- Quotient automaton modulo `equivM M`. -/
def quotientAut (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M) :
    Aut (Quotient (equivSetoid M)) α where
  step q a := Quotient.liftOn q (fun p => Quotient.mk (equivSetoid M) (A.step p a))
    (fun _ _ hpq => Quotient.sound (equivM_step A hsink hpq a))

lemma quotientAut_eval (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    (p : Q) (w : List α) :
    (quotientAut A M hsink).eval (Quotient.mk (equivSetoid M) p) w =
      Quotient.mk (equivSetoid M) (A.eval p w) := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => exact ih (A.step p a)

lemma quotientAut_isAperiodic (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    (hap : IsAperiodic A) : IsAperiodic (quotientAut A M hsink) := by
  intro w q_bar m hm hiter
  induction q_bar using Quotient.inductionOn with
  | h p =>
    rw [quotientAut_eval] at hiter ⊢
    -- Since p and p · w^m are in the same class, wait: does p · w^m ≡_M p imply p · w ≡_M p?
    -- Wait: by finitude of the class (or Q), p · w^(m^k) = p · w^(m^l) for some k < l,
    -- wait: we don't even know the class is closed under w!
    -- Wait: p · w^m ≡_M p means w^m preserves the class of p!
    -- So p, p · w^m, p · w^(2m), ... are all in the class of p (in Q)!
    -- By finitude of Q, ∃ i < j, p · w^(i*m) = p · w^(j*m), so by IsAperiodic of A,
    -- p · w^(i*m + 1) = p · w^(i*m)! Wait: then p · w^(i*m) ≡_M p · w^(i*m + 1),
    -- Wait: p · w^(i*m) ≡_M p doesn't immediately give p · w ≡_M p unless w is invertible?
    -- NO! Look: p ≡_M p · w^m means applying w gives p · w ≡_M p · w^(m+1)!
    -- By induction, p · w^t ≡_M p · w^(t+m) for all t!
    -- Wait: if p · w^(i*m + 1) = p · w^(i*m), then p · w ≡_M p · w^(i*m + 1) = p · w^(i*m) ≡_M p!
    -- YES!! That's why!
    have hcongr : ∀ t : ℕ, equivM M (A.eval p (iterWord w t)) (A.eval p (iterWord w (t + m))) := by
      intro t
      induction t with
      | zero =>
        simp only [iterWord_zero, Aut.eval_nil, zero_add]
        exact Quotient.exact hiter.symm
      | succ t iht =>
        -- Actually, better: p ≡_M p · w^m implies p · u ≡_M (p · w^m) · u = p · (w^m ++ u) = p · (u' ...)
        -- Specifically for u = w^t: p · w^t ≡_M (p · w^m) · w^t = p · w^(m + t) = p · w^(t + m)!
        have hstep_w : ∀ x y : Q, equivM M x y → ∀ u : List α, equivM M (A.eval x u) (A.eval y u) := by
          intro x y hxy u
          induction u generalizing x y with
          | nil => exact hxy
          | cons a u ihu => exact ihu _ _ (equivM_step A hsink hxy a)
        have h0 := hstep_w p (A.eval p (iterWord w m)) (Quotient.exact hiter.symm) (iterWord w (t + 1))
        rw [← Aut.eval_append, ← iterWord_add, add_comm m (t + 1)] at h0
        exact h0
    have hmult : ∀ k : ℕ, equivM M p (A.eval p (iterWord w (k * m))) := by
      intro k
      induction k with
      | zero => simp; exact Relation.EqvGen.refl _
      | succ k ihk =>
        rw [Nat.succ_mul]
        exact Relation.EqvGen.trans _ _ _ ihk (hcongr (k * m))
    -- Find i < j with p · w^(i*m) = p · w^(j*m)
    have hnotinj : ¬ Function.Injective (fun k : Fin (Fintype.card Q + 1) =>
        A.eval p (iterWord w (k.1 * m))) := by
      intro hinj
      have := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_fin] at this
      omega
    simp only [Function.Injective, not_forall] at hnotinj
    obtain ⟨a, b, hab, hne_ab⟩ := hnotinj
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm (Ne.symm hne_ab) (by omega)
    have hper : A.eval (A.eval p (iterWord w (a.1 * m))) (iterWord w ((b.1 - a.1) * m)) =
        A.eval p (iterWord w (a.1 * m)) := by
      rw [← Aut.eval_append, ← iterWord_add, ← Nat.add_mul, Nat.add_sub_cancel' (by omega : a.1 ≤ b.1)]
      exact hab.symm
    have hap1 := hap w (A.eval p (iterWord w (a.1 * m))) ((b.1 - a.1) * m)
      (Nat.mul_pos (by omega) hm) hper
    have hw_congr : equivM M (A.eval p w) (A.eval p (iterWord w (a.1 * m + 1))) := by
      have hstep_w : ∀ x y : Q, equivM M x y → ∀ u : List α, equivM M (A.eval x u) (A.eval y u) := by
        intro x y hxy u
        induction u generalizing x y with
        | nil => exact hxy
        | cons c u ihu => exact ihu _ _ (equivM_step A hsink hxy c)
      have h0 := hstep_w p (A.eval p (iterWord w (a.1 * m))) (hmult a.1) w
      rw [← Aut.eval_append, show iterWord w (a.1 * m) ++ w = iterWord w (a.1 * m + 1) by
        rw [show a.1 * m + 1 = a.1 * m + 1 from rfl, iterWord_add]; simp [iterWord]] at h0
      exact h0
    have heq_w : A.eval p (iterWord w (a.1 * m + 1)) = A.eval p (iterWord w (a.1 * m)) := by
      rw [eval_iterWord_succ]
      exact hap1
    apply Quotient.sound
    exact Relation.EqvGen.trans _ _ _ hw_congr
      (Relation.EqvGen.trans _ _ _ (by rw [heq_w]; exact Relation.EqvGen.refl _)
        (Relation.EqvGen.symm _ _ (hmult a.1)))

lemma quotientAut_isSync (M : Finset (Q × Q))
    [Fintype (Quotient (equivSetoid M))] [DecidableEq (Quotient (equivSetoid M))]
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    [Nonempty Q] (hsync : A.IsSync) : (quotientAut A M hsink).IsSync := by
  classical
  obtain ⟨w, hw⟩ := hsync
  rw [Aut.isSyncWord_iff_exists_eval_eq] at hw
  obtain ⟨q₀, hq₀⟩ := hw
  refine ⟨w, ?_⟩
  haveI : Nonempty (Quotient (equivSetoid M)) := ⟨Quotient.mk _ q₀⟩
  rw [Aut.isSyncWord_iff_exists_eval_eq]
  refine ⟨Quotient.mk _ q₀, fun q_bar => ?_⟩
  induction q_bar using Quotient.inductionOn with
  | h p => rw [quotientAut_eval, hq₀ p]

lemma quotientAut_stronglyConnected (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    (hsc : A.StronglyConnected) : (quotientAut A M hsink).StronglyConnected := by
  intro p_bar q_bar
  induction p_bar using Quotient.inductionOn with
  | h p =>
    induction q_bar using Quotient.inductionOn with
    | h q =>
      obtain ⟨w, hw⟩ := hsc p q
      exact ⟨w, by rw [quotientAut_eval, hw]⟩

end PartialOrderAndQuotient

section MinMaxStep
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Minimal elements of `(Q, leM M)`. -/
noncomputable def MinQ (M : Finset (Q × Q)) : Finset Q :=
  open scoped Classical in
  Finset.univ.filter (fun m => ∀ p : Q, leM M p m → p = m)

/-- Maximal elements of `(Q, leM M)`. -/
noncomputable def MaxQ (M : Finset (Q × Q)) : Finset Q :=
  open scoped Classical in
  Finset.univ.filter (fun m => ∀ p : Q, leM M m p → p = m)

lemma exists_leM_min (M : Finset (Q × Q))
    (hanti : ∀ p q : Q, leM M p q → leM M q p → p = q) (q : Q) :
    ∃ m ∈ MinQ M, leM M m q := by
  classical
  let below (x : Q) : Finset Q := Finset.univ.filter (fun y => leM M y x)
  have hbelow_ne : ∀ x, (below x).Nonempty := fun x =>
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, leM_refl M x⟩⟩
  let S : Finset Q := below q
  obtain ⟨m, hmS, hm_min⟩ := Finset.exists_min_image S (fun x => (below x).card) (hbelow_ne q)
  simp only [S, below, Finset.mem_filter, Finset.mem_univ, true_and] at hmS
  refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, ?_⟩, hmS⟩
  intro p hpm
  have hpq : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ p, leM_trans hpm hmS⟩
  have hsub : below p ⊆ below m := by
    intro y hy
    simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact leM_trans hy hpm
  have hcard_eq : (below p).card = (below m).card :=
    le_antisymm (Finset.card_le_card hsub) (hm_min p hpq)
  have heq_set : below p = below m := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm_in_bp : m ∈ below p := by
    rw [heq_set]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, leM_refl M m⟩
  simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in_bp
  exact hanti p m hpm hm_in_bp

lemma exists_leM_max (M : Finset (Q × Q))
    (hanti : ∀ p q : Q, leM M p q → leM M q p → p = q) (q : Q) :
    ∃ m ∈ MaxQ M, leM M q m := by
  classical
  let above (x : Q) : Finset Q := Finset.univ.filter (fun y => leM M x y)
  have habove_ne : ∀ x, (above x).Nonempty := fun x =>
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, leM_refl M x⟩⟩
  let S : Finset Q := above q
  obtain ⟨m, hmS, hm_min⟩ := Finset.exists_min_image S (fun x => (above x).card) (habove_ne q)
  simp only [S, above, Finset.mem_filter, Finset.mem_univ, true_and] at hmS
  refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, ?_⟩, hmS⟩
  intro p hmp
  have hpq : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ p, leM_trans hmS hmp⟩
  have hsub : above p ⊆ above m := by
    intro y hy
    simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact leM_trans hmp hy
  have hcard_eq : (above p).card = (above m).card :=
    le_antisymm (Finset.card_le_card hsub) (hm_min p hpq)
  have heq_set : above p = above m := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm_in_ap : m ∈ above p := by
    rw [heq_set]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, leM_refl M m⟩
  simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in_ap
  exact (hanti m p hmp hm_in_ap).symm

lemma card_minQ_ge (M : Finset (Q × Q))
    [Fintype (Quotient (equivSetoid M))]
    (hanti : ∀ p q : Q, leM M p q → leM M q p → p = q) :
    Fintype.card (Quotient (equivSetoid M)) ≤ (MinQ M).card := by
  classical
  have hsurj : ∀ c : Quotient (equivSetoid M), ∃ m ∈ MinQ M, Quotient.mk (equivSetoid M) m = c := by
    intro c
    induction c using Quotient.inductionOn with
    | h q =>
      obtain ⟨m, hm_min, hmq⟩ := exists_leM_min M hanti q
      refine ⟨m, hm_min, Quotient.sound ?_⟩
      induction hmq with
      | refl => exact Relation.EqvGen.refl _
      | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)
  choose f hf_mem hf_eq using hsurj
  have hinj : Function.Injective f := by
    intro c₁ c₂ h
    rw [← hf_eq c₁, ← hf_eq c₂, h]
  calc Fintype.card (Quotient (equivSetoid M))
      ≤ Fintype.card (↥(MinQ M)) :=
        Fintype.card_le_of_injective (fun c => ⟨f c, hf_mem c⟩) (fun _ _ h => hinj (congrArg Subtype.val h))
    _ = (MinQ M).card := Fintype.card_coe _

lemma card_maxQ_ge (M : Finset (Q × Q))
    [Fintype (Quotient (equivSetoid M))]
    (hanti : ∀ p q : Q, leM M p q → leM M q p → p = q) :
    Fintype.card (Quotient (equivSetoid M)) ≤ (MaxQ M).card := by
  classical
  have hsurj : ∀ c : Quotient (equivSetoid M), ∃ m ∈ MaxQ M, Quotient.mk (equivSetoid M) m = c := by
    intro c
    induction c using Quotient.inductionOn with
    | h q =>
      obtain ⟨m, hm_max, hqm⟩ := exists_leM_max M hanti q
      refine ⟨m, hm_max, Quotient.sound ?_⟩
      apply Relation.EqvGen.symm
      clear hm_max
      induction hqm with
      | refl => exact Relation.EqvGen.refl _
      | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)
  choose f hf_mem hf_eq using hsurj
  have hinj : Function.Injective f := by
    intro c₁ c₂ h
    rw [← hf_eq c₁, ← hf_eq c₂, h]
  calc Fintype.card (Quotient (equivSetoid M))
      ≤ Fintype.card (↥(MaxQ M)) :=
        Fintype.card_le_of_injective (fun c => ⟨f c, hf_mem c⟩) (fun _ _ h => hinj (congrArg Subtype.val h))
    _ = (MaxQ M).card := Fintype.card_coe _

/-- Connectedness of `T` in the comparability graph of `leM M`. -/
def IsCompConnected (M : Finset (Q × Q)) (T : Finset Q) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T,
    Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ (leM M u v ∨ leM M v u)) x y

lemma isCompConnected_image (M : Finset (Q × Q))
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    {T : Finset Q} (hT : IsCompConnected M T) (w : List α) :
    IsCompConnected M (A.image T w) := by
  intro x' hx' y' hy'
  rcases (Aut.mem_image A).mp hx' with ⟨x, hxT, rfl⟩
  rcases (Aut.mem_image A).mp hy' with ⟨y, hyT, rfl⟩
  have hpath := hT x hxT y hyT
  have hgen : ∀ a b, Relation.ReflTransGen
      (fun u v => u ∈ T ∧ v ∈ T ∧ (leM M u v ∨ leM M v u)) a b →
      Relation.ReflTransGen
        (fun u v => u ∈ A.image T w ∧ v ∈ A.image T w ∧ (leM M u v ∨ leM M v u))
        (A.eval a w) (A.eval b w) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine Relation.ReflTransGen.tail ih ⟨Finset.mem_image_of_mem _ hbc.1,
        Finset.mem_image_of_mem _ hbc.2.1, ?_⟩
      rcases hbc.2.2 with h | h
      · left; exact leM_eval A hsink h w
      · right; exact leM_eval A hsink h w
  exact hgen x y hpath

lemma isCompConnected_of_equiv_class (M : Finset (Q × Q))
    [DecidableEq (Quotient (equivSetoid M))] (c : Quotient (equivSetoid M)) :
    IsCompConnected M (Finset.univ.filter (fun q => Quotient.mk (equivSetoid M) q = c)) := by
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have heqv : equivM M x y := Quotient.exact (hx.trans hy.symm)
  induction heqv with
  | rel a b hab =>
    exact Relation.ReflTransGen.single
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, Or.inl (leM_of_mem hab)⟩
  | refl => exact Relation.ReflTransGen.refl
  | @symm a b hab ih =>
    -- Here hx : ⟦b⟧ = c, hy : ⟦a⟧ = c
    have ih' := ih hy hx
    clear hx hy ih hab
    induction ih' with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v _ huv ihrev =>
      have hvu : v ∈ Finset.univ.filter (fun q => Quotient.mk (equivSetoid M) q = c) ∧
          u ∈ Finset.univ.filter (fun q => Quotient.mk (equivSetoid M) q = c) ∧
          (leM M v u ∨ leM M u v) :=
        ⟨huv.2.1, huv.1, huv.2.2.symm⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hvu) ihrev
  | @trans a b d hab hbd ih1 ih2 =>
    have hb : Quotient.mk (equivSetoid M) b = c := by
      rw [← hx]; exact Quotient.sound (Relation.EqvGen.symm _ _ hab)
    exact Relation.ReflTransGen.trans (ih1 hx hb) (ih2 hb hy)

/-- Min/max contraction step for aperiodic strongly connected automata. -/
theorem aperiodic_minmax_step (M : Finset (Q × Q))
    [Fintype (Quotient (equivSetoid M))]
    (hsink : ∀ p q, (p, q) ∈ M → ∀ a : α, A.step p a = A.step q a ∨ (A.step p a, A.step q a) ∈ M)
    (hanti : ∀ p q : Q, leM M p q → leM M q p → p = q)
    (hsc : A.StronglyConnected)
    {T : Finset Q} (hT_conn : IsCompConnected M T) (hT_card : 2 ≤ T.card) :
    ∃ w : List α,
      (A.image T w).card ≤ T.card - 1 ∧
      IsCompConnected M (A.image T w) ∧
      w.length ≤ Fintype.card Q - Fintype.card (Quotient (equivSetoid M)) + 1 - (T.card + 1) / 2 := by
  classical
  let n := Fintype.card Q
  let n₁ := Fintype.card (Quotient (equivSetoid M))
  let T_above := T.filter (fun q => ∃ p ∈ T, p ≠ q ∧ leM M p q)
  let T_below := T.filter (fun p => ∃ q ∈ T, p ≠ q ∧ leM M p q)
  have hcover : T ⊆ T_above ∪ T_below := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) x
    have hpath := hT_conn x hx y hy
    have hstep1 : ∃ z ∈ T, z ≠ x ∧ (leM M x z ∨ leM M z x) := by
      have haux : ∀ a b, Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ (leM M u v ∨ leM M v u)) a b →
          a ≠ b → ∃ z ∈ T, z ≠ a ∧ (leM M a z ∨ leM M z a) := by
        intro a b hab
        induction hab using Relation.ReflTransGen.head_induction_on with
        | refl => intro hne; exact absurd rfl hne
        | @head u v huv hvy ih =>
          intro _
          by_cases huv_eq : u = v
          · subst huv_eq; exact ih (by assumption)
          · exact ⟨v, huv.2.1, fun h => huv_eq h.symm, huv.2.2⟩
      exact haux x y hpath hxy.symm
    obtain ⟨z, hzT, hzx, hle | hle⟩ := hstep1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, z, hzT, hzx.symm, hle⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, z, hzT, hzx, hle⟩)
  have hmax_card : (T.card + 1) / 2 ≤ T_above.card ∨ (T.card + 1) / 2 ≤ T_below.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le T_above T_below
    omega
  -- Helper for shortest path to a nonempty target set B disjoint from A_set
  have hpath_merge : ∀ (A_set B_set : Finset Q),
      A_set ⊆ T → B_set.Nonempty → Disjoint A_set B_set →
      (T.card + 1) / 2 ≤ A_set.card → n₁ ≤ B_set.card →
      (∀ q ∈ A_set, ∃ p ∈ T, p ≠ q ∧ (leM M p q ∧ (∀ w, A.eval q w ∈ B_set → A.eval p w = A.eval q w) ∨
        leM M q p ∧ (∀ w, A.eval q w ∈ B_set → A.eval p w = A.eval q w))) →
      ∃ w : List α, (A.image T w).card ≤ T.card - 1 ∧
        IsCompConnected M (A.image T w) ∧ w.length ≤ n - n₁ + 1 - (T.card + 1) / 2 := by
    intro A_set B_set hAT hB_ne hdisj hA_card hB_card hmerge_prop
    have hA_ne : A_set.Nonempty := Finset.card_pos.mp (by omega)
    have hdist : ∀ q : Q, ∃ m : ℕ, ∃ v : List α, v.length = m ∧ A.eval q v ∈ B_set := by
      intro q
      obtain ⟨b, hb⟩ := hB_ne
      obtain ⟨v, hv⟩ := hsc q b
      exact ⟨v.length, v, rfl, by rw [hv]; exact hb⟩
    let d : Q → ℕ := fun q => Nat.find (hdist q)
    obtain ⟨q_star, hq_star_mem, hq_star_min⟩ := Finset.exists_min_image A_set d hA_ne
    obtain ⟨v, hv_len, hv_inB⟩ := Nat.find_spec (hdist q_star)
    change v.length = d q_star at hv_len
    have hq_star_nB : q_star ∉ B_set := Finset.disjoint_left.mp hdisj hq_star_mem
    have hd_pos : 1 ≤ d q_star := by
      by_contra h0
      have hd0 : d q_star = 0 := by omega
      rw [hd0, List.length_eq_zero_iff] at hv_len
      subst hv_len
      exact hq_star_nB hv_inB
    let qj : ℕ → Q := fun j => A.eval q_star (v.take j)
    have hqj_nB : ∀ j < d q_star, qj j ∉ B_set := by
      intro j hj hmem
      have hle : d q_star ≤ (v.take j).length :=
        Nat.find_min' (hdist q_star) ⟨v.take j, rfl, hmem⟩
      rw [List.length_take, hv_len] at hle
      omega
    have hqj_inj : ∀ i j, i < j → j < d q_star → qj i ≠ qj j := by
      intro i j hij hj heq
      let v' := v.take i ++ v.drop j
      have hv'_len : v'.length < d q_star := by
        simp only [v', List.length_append, List.length_take, List.length_drop, hv_len]
        omega
      have hv'_mem : A.eval q_star v' ∈ B_set := by
        simp only [v', Aut.eval_append]
        change A.eval (qj i) (v.drop j) ∈ B_set
        rw [heq]
        change A.eval (A.eval q_star (v.take j)) (v.drop j) ∈ B_set
        rw [← Aut.eval_append, List.take_append_drop]
        exact hv_inB
      have hle := Nat.find_min' (hdist q_star) ⟨v', rfl, hv'_mem⟩
      change d q_star ≤ v'.length at hle
      omega
    have hqj_nA : ∀ j, 1 ≤ j → j < d q_star → qj j ∉ A_set := by
      intro j hj1 hj hmem
      have hmin := hq_star_min (qj j) hmem
      have hle := Nat.find_min' (hdist (qj j))
        ⟨v.drop j, rfl, by
          change A.eval (A.eval q_star (v.take j)) (v.drop j) ∈ B_set
          rw [← Aut.eval_append, List.take_append_drop]
          exact hv_inB⟩
      change d (qj j) ≤ (v.drop j).length at hle
      rw [List.length_drop, hv_len] at hle
      omega
    let mid : Finset Q := (Finset.Ico 1 (d q_star)).image qj
    have hmid_sub : mid ⊆ Finset.univ \ (A_set ∪ B_set) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      rw [Finset.mem_Ico] at hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      exact ⟨hqj_nA j hj.1 hj.2, hqj_nB j hj.2⟩
    have hmid_card : mid.card = d q_star - 1 := by
      rw [Finset.card_image_of_injOn]
      · simp [Nat.card_Ico]
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · exact absurd hab (hqj_inj a b hlt hb.2)
        · rfl
        · exact absurd hab.symm (hqj_inj b a hgt ha.2)
    have hAB_le : A_set.card + B_set.card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_univ _
    have hle_univ : mid.card ≤ n - (A_set.card + B_set.card) := by
      have h1 := Finset.card_le_card hmid_sub
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
        Finset.card_union_of_disjoint hdisj] at h1
      exact h1
    have hv_len_le : v.length ≤ n - n₁ + 1 - (T.card + 1) / 2 := by
      rw [hv_len]
      omega
    obtain ⟨p, hpT, hpq, hmerge⟩ := hmerge_prop q_star hq_star_mem
    have hpq_eval : A.eval p v = A.eval q_star v := by
      rcases hmerge with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact hm v hv_inB
    have himg_eq : A.image (T.erase p) v = A.image T v := by
      ext x
      simp only [Aut.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, Finset.erase_subset _ _ hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        by_cases hzp : z = p
        · subst hzp
          exact ⟨q_star, Finset.mem_erase.mpr ⟨hpq.symm, hAT hq_star_mem⟩, hpq_eval.symm⟩
        · exact ⟨z, Finset.mem_erase.mpr ⟨hzp, hz⟩, rfl⟩
    refine ⟨v, ?_, isCompConnected_image A M hsink hT_conn v, hv_len_le⟩
    rw [← himg_eq]
    calc (A.image (T.erase p) v).card
        ≤ (T.erase p).card := A.card_image_le _ _
      _ = T.card - 1 := Finset.card_erase_of_mem hpT
  rcases hmax_card with h_above | h_below
  · obtain ⟨q₀, _⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    apply hpath_merge T_above (MinQ M) (Finset.filter_subset _ _)
    · obtain ⟨m, hm, _⟩ := exists_leM_min M hanti q₀
      exact ⟨m, hm⟩
    · rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [T_above, Finset.mem_filter] at hq1
      simp only [MinQ, Finset.mem_filter, Finset.mem_univ, true_and] at hq2
      obtain ⟨p, _, hpq, hle⟩ := hq1.2
      exact hpq (hq2 p hle)
    · exact h_above
    · exact card_minQ_ge M hanti
    · intro q hq
      simp only [T_above, Finset.mem_filter] at hq
      obtain ⟨p, hpT, hpq, hle⟩ := hq.2
      refine ⟨p, hpT, hpq, Or.inl ⟨hle, fun w hw => ?_⟩⟩
      simp only [MinQ, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hw (A.eval p w) (leM_eval A hsink hle w)
  · obtain ⟨q₀, _⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    apply hpath_merge T_below (MaxQ M) (Finset.filter_subset _ _)
    · obtain ⟨m, hm, _⟩ := exists_leM_max M hanti q₀
      exact ⟨m, hm⟩
    · rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [T_below, Finset.mem_filter] at hq1
      simp only [MaxQ, Finset.mem_filter, Finset.mem_univ, true_and] at hq2
      obtain ⟨p, _, hpq, hle⟩ := hq1.2
      exact hpq (hq2 p hle).symm
    · exact h_below
    · exact card_maxQ_ge M hanti
    · intro q hq
      simp only [T_below, Finset.mem_filter] at hq
      obtain ⟨p, hpT, hpq, hle⟩ := hq.2
      refine ⟨p, hpT, hpq.symm, Or.inr ⟨hle, fun w hw => ?_⟩⟩
      simp only [MaxQ, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hw (A.eval p w) (leM_eval A hsink hle w)

end MinMaxStep

section MainBound

/-- Improved aperiodic upper bound `⌈3(n - 1)^2 / 4⌉`. -/
def apBound (n : ℕ) : ℕ :=
  (3 * (n - 1) ^ 2 + (n - 1) % 2) / 4

@[simp]
lemma apBound_one : apBound 1 = 0 := by simp [apBound]

lemma apBound_le_cerny (n : ℕ) : apBound n ≤ (n - 1) ^ 2 := by
  unfold apBound
  omega

private lemma four_mul_apBound (m : ℕ) (hm : 1 ≤ m) :
    4 * apBound m = 3 * (m - 1) ^ 2 + (m - 1) % 2 := by
  unfold apBound
  have hdiv : 4 ∣ 3 * (m - 1) ^ 2 + (m - 1) % 2 := by
    rcases Nat.even_or_odd (m - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]
      refine ⟨3 * k ^ 2, ?_⟩
      have hmod : (k + k) % 2 = 0 := by omega
      rw [hmod]; ring
    · rw [hk]
      refine ⟨3 * k ^ 2 + 3 * k + 1, ?_⟩
      have hmod : (2 * k + 1) % 2 = 1 := by omega
      rw [hmod]; ring
  exact Nat.mul_div_cancel' hdiv

private lemma sum_ap_step (d : ℕ) :
    ∑ r ∈ Finset.Ico 2 (d + 2), (d + 1 - (r + 1) / 2) = apBound (d + 1) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    rcases d with _ | _ | d
    · simp [apBound]
    · simp [apBound]
    · have hsplit : Finset.Ico 2 (d + 4) = Finset.Ico 2 (d + 2) ∪ {d + 2, d + 3} := by
        ext r; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hdisj : Disjoint (Finset.Ico 2 (d + 2)) {d + 2, d + 3} := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hr1 hr2
        omega
      rw [show d + 2 + 2 = d + 4 by omega, hsplit, Finset.sum_union hdisj]
      have hpair : ∑ r ∈ ({d + 2, d + 3} : Finset ℕ), (d + 3 - (r + 1) / 2) =
          (d + 3 - (d + 3) / 2) + (d + 3 - (d + 4) / 2) := by
        rw [Finset.sum_pair (by omega)]
      have hshift : ∑ r ∈ Finset.Ico 2 (d + 2), (d + 3 - (r + 1) / 2) =
          ∑ r ∈ Finset.Ico 2 (d + 2), ((d + 1 - (r + 1) / 2) + 2) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Ico] at hr
        have hle : (r + 1) / 2 ≤ d + 1 := by omega
        omega
      rw [hshift, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
        ih d (by omega), hpair]
      have hL := four_mul_apBound (d + 1) (by omega)
      have hR := four_mul_apBound (d + 3) (by omega)
      have hsub3 : d + 3 - 1 = d + 2 := by omega
      simp only [Nat.add_sub_cancel, hsub3] at hL hR
      rw [show d + 1 + 1 + 1 = d + 3 by omega]
      rcases Nat.even_or_odd d with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod1 : (k + k) % 2 = 0 := by omega
        have hmod2 : (k + k + 2) % 2 = 0 := by omega
        have hdiv1 : (k + k + 3) / 2 = k + 1 := by omega
        have hdiv2 : (k + k + 4) / 2 = k + 2 := by omega
        rw [hmod1] at hL; rw [hmod2] at hR; rw [hdiv1, hdiv2]
        rw [show k + k + 2 - 2 = k + k by omega,
          show k + k + 3 - (k + 1) = k + 2 by omega,
          show k + k + 3 - (k + 2) = k + 1 by omega]
        nlinarith
      · have hmod1 : (2 * k + 1) % 2 = 1 := by omega
        have hmod2 : (2 * k + 1 + 2) % 2 = 1 := by omega
        have hdiv1 : (2 * k + 1 + 3) / 2 = k + 2 := by omega
        have hdiv2 : (2 * k + 1 + 4) / 2 = k + 2 := by omega
        rw [hmod1] at hL; rw [hmod2] at hR; rw [hdiv1, hdiv2]
        rw [show 2 * k + 1 + 2 - 2 = 2 * k + 1 by omega,
          show 2 * k + 1 + 3 - (k + 2) = k + 2 by omega]
        nlinarith

private lemma apBound_add_step {n₁ d : ℕ} (hn₁ : 1 ≤ n₁) :
    apBound n₁ + apBound (d + 1) ≤ apBound (n₁ + d) := by
  have h1 := four_mul_apBound n₁ hn₁
  have h2 := four_mul_apBound (d + 1) (by omega)
  have h3 := four_mul_apBound (n₁ + d) (by omega)
  simp only [Nat.add_sub_cancel] at h2
  have hsub : n₁ + d - 1 = (n₁ - 1) + d := by omega
  rw [hsub] at h3
  have hmod : (n₁ - 1) % 2 + d % 2 ≤ ((n₁ - 1) + d) % 2 + 2 := by omega
  nlinarith

private lemma apBound_absorb {m k : ℕ} (hm : 1 ≤ m) :
    apBound m + k * (k + 1) / 2 ≤ apBound (m + k) := by
  have h1 := four_mul_apBound m hm
  have h3 := four_mul_apBound (m + k) (by omega)
  have hdiv : 2 * (k * (k + 1) / 2) ≤ k * (k + 1) := Nat.mul_div_le _ 2
  have hsub : m + k - 1 = (m - 1) + k := by omega
  rw [hsub] at h3
  have hmod : (m - 1) % 2 ≤ ((m - 1) + k) % 2 + 1 := by omega
  have hlin : (m - 1) % 2 + 2 * (k * (k + 1) / 2) ≤ ((m - 1) + k) % 2 + 2 * (m - 1) * k + 3 * k ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk2 : k ≤ k ^ 2 := by nlinarith
      nlinarith
  nlinarith

/-- Improved Černý bound for all synchronizing aperiodic automata:
`rt(A) ≤ ⌈3(n - 1)^2 / 4⌉`. -/
theorem aperiodic_bound :
    ∀ {Q : Type*} {α : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
      (A : Aut Q α), IsAperiodic A → A.IsSync →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ apBound (Fintype.card Q) := by
  -- First prove for strongly connected automata by strong induction on Fintype.card Q,
  -- then lift via sink_scc_exists + absorption_lemma.
  intro Q α _ _ _ A hap hsync
  have hSC : ∀ (n : ℕ), ∀ {Q' : Type _} {α' : Type _} [Fintype Q'] [DecidableEq Q'] [Nonempty Q']
      (B : Aut Q' α'), Fintype.card Q' = n → B.StronglyConnected → IsAperiodic B → B.IsSync →
      ∃ w : List α', B.IsSyncWord w ∧ w.length ≤ apBound n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro Q α _ _ _ A hcard hsc hap hsync
      by_cases hn1 : n ≤ 1
      · have h1 : Fintype.card Q = 1 := by have := Fintype.card_pos (α := Q); omega
        haveI : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        exact ⟨[], A.isSyncWord_nil_of_subsingleton, by simp⟩
      · have hn2 : 2 ≤ Fintype.card Q := by omega
        obtain ⟨M, hM_ne, hirr, hsink, hscc⟩ := sink_scc_Gneq_exists A hn2
        have hacyc := sink_scc_acyclic A hap M hsink hscc
        have hanti : ∀ p q : Q, leM M p q → leM M q p → p = q :=
          fun p q hpq hqp => leM_antisymm hacyc hirr hpq hqp
        let Q₁ := Quotient (equivSetoid M)
        let A₁ := quotientAut A M hsink
        haveI : DecidableRel (equivSetoid M).r := Classical.decRel _
        haveI : Fintype Q₁ := Quotient.fintype (equivSetoid M)
        haveI : DecidableEq Q₁ := Classical.decEq Q₁
        haveI : Nonempty Q₁ := ⟨Quotient.mk _ (Classical.arbitrary Q)⟩
        have hn₁_pos : 1 ≤ Fintype.card Q₁ := Fintype.card_pos
        have hn₁_lt : Fintype.card Q₁ < n := by
          obtain ⟨⟨p₀, q₀⟩, hpq₀⟩ := hM_ne
          have hne_pq : p₀ ≠ q₀ := hirr p₀ q₀ hpq₀
          have heq_mk : Quotient.mk (equivSetoid M) p₀ = Quotient.mk (equivSetoid M) q₀ :=
            Quotient.sound (Relation.EqvGen.rel _ _ hpq₀)
          let img : Finset Q := Finset.univ.image (Quotient.out : Q₁ → Q)
          have himg_card : img.card = Fintype.card Q₁ := by
            rw [Finset.card_image_of_injective _ Quotient.out_injective, Finset.card_univ]
          have himg_ssub : img ⊂ Finset.univ := by
            rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
            by_cases hp : Quotient.out (Quotient.mk (equivSetoid M) p₀) = p₀
            · refine ⟨q₀, Finset.mem_univ _, fun hmem => ?_⟩
              rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
              have h1 : c = Quotient.mk (equivSetoid M) q₀ := by rw [← hc, Quotient.out_eq]
              rw [h1, ← heq_mk, hp] at hc
              exact hne_pq hc
            · refine ⟨p₀, Finset.mem_univ _, fun hmem => ?_⟩
              rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
              have h1 : c = Quotient.mk (equivSetoid M) p₀ := by rw [← hc, Quotient.out_eq]
              rw [h1] at hc
              exact hp hc
          have hlt := Finset.card_lt_card himg_ssub
          rw [himg_card, Finset.card_univ] at hlt
          omega
        obtain ⟨u, hu_sync, hu_len⟩ := ih (Fintype.card Q₁) hn₁_lt A₁ rfl
          (quotientAut_stronglyConnected A M hsink hsc)
          (quotientAut_isAperiodic A M hsink hap)
          (quotientAut_isSync A M hsink hsync)
        rw [Aut.isSyncWord_iff_exists_eval_eq] at hu_sync
        obtain ⟨c₀, hc₀⟩ := hu_sync
        let R : Finset Q := Finset.univ.filter (fun q => Quotient.mk (equivSetoid M) q = c₀)
        have hR_img : A.image Finset.univ u ⊆ R := by
          intro x hx
          rcases (Aut.mem_image A).mp hx with ⟨p, _, rfl⟩
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← quotientAut_eval A M hsink]
          exact hc₀ (Quotient.mk _ p)
        have hR_ne : R.Nonempty := (A.image_nonempty Finset.univ_nonempty u).mono hR_img
        have hR_conn : IsCompConnected M R := isCompConnected_of_equiv_class M c₀
        let d := n - Fintype.card Q₁
        have hR_card : R.card ≤ d + 1 := by
          -- Every other class has ≥ 1 element
          let others : Finset Q₁ := Finset.univ.erase c₀
          have hchoose : ∀ c ∈ others, ∃ q : Q, Quotient.mk (equivSetoid M) q = c :=
            fun c _ => Quotient.exists_rep c
          choose g hg using hchoose
          let G : Finset Q := others.attach.image (fun c => g c.1 c.2)
          have hdisj : Disjoint R G := by
            rw [Finset.disjoint_left]
            intro x hxR hxG
            simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hxR
            rcases Finset.mem_image.mp hxG with ⟨c, _, rfl⟩
            have hc_ne : c.1 ≠ c₀ := (Finset.mem_erase.mp c.2).1
            rw [hg c.1 c.2] at hxR
            exact hc_ne hxR
          have hq_card_eq : Fintype.card (Quotient (equivSetoid M)) = Fintype.card Q₁ :=
            Fintype.card_congr (Equiv.refl Q₁)
          have hG_card : G.card = Fintype.card Q₁ - 1 := by
            rw [Finset.card_image_of_injOn]
            · simp [others, Finset.card_erase_of_mem (Finset.mem_univ c₀), hq_card_eq]
            · intro a _ b _ hab
              have ha := hg a.1 a.2
              have hb := hg b.1 b.2
              have hmk := congrArg (Quotient.mk (equivSetoid M)) hab
              rw [ha, hb] at hmk
              exact Subtype.ext hmk
          have hsum_le : R.card + G.card ≤ n := by
            rw [← Finset.card_union_of_disjoint hdisj, ← hcard]
            exact Finset.card_le_univ _
          omega
        -- Contract A.image Finset.univ u to size 1
        have hcontract : ∀ T : Finset Q, T.Nonempty → IsCompConnected M T → T.card ≤ d + 1 →
            ∃ v : List α, (A.image T v).card = 1 ∧
              v.length ≤ ∑ r ∈ Finset.Ico 2 (T.card + 1), (d + 1 - (r + 1) / 2) := by
          intro T
          induction hTc : T.card using Nat.strong_induction_on generalizing T with
          | ind s ihT =>
            intro hT_ne hT_conn hT_le
            by_cases hs1 : s ≤ 1
            · have hs_eq : T.card = 1 := by have := hT_ne.card_pos; omega
              exact ⟨[], by simpa [Aut.image_nil] using hs_eq, by simp⟩
            · have hs2 : 2 ≤ T.card := by omega
              obtain ⟨v₁, hv₁_card, hv₁_conn, hv₁_len⟩ :=
                aperiodic_minmax_step A M hsink hanti hsc hT_conn hs2
              have hT'_ne : (A.image T v₁).Nonempty := A.image_nonempty hT_ne v₁
              have hT'_lt : (A.image T v₁).card < s := by omega
              have hT'_le : (A.image T v₁).card ≤ d + 1 := by omega
              obtain ⟨v₂, hv₂_card, hv₂_len⟩ :=
                ihT (A.image T v₁).card hT'_lt (A.image T v₁) rfl hT'_ne hv₁_conn hT'_le
              refine ⟨v₁ ++ v₂, by rw [Aut.image_append]; exact hv₂_card, ?_⟩
              have hq_eq : Fintype.card (Quotient (equivSetoid M)) = Fintype.card Q₁ :=
                Fintype.card_congr (Equiv.refl Q₁)
              have h1 : v₁.length ≤ d + 1 - (s + 1) / 2 := by
                rw [hq_eq, hcard, hTc] at hv₁_len
                exact hv₁_len
              have hsub_sum : ∑ r ∈ Finset.Ico 2 ((A.image T v₁).card + 1), (d + 1 - (r + 1) / 2) ≤
                  ∑ r ∈ Finset.Ico 2 s, (d + 1 - (r + 1) / 2) := by
                rw [← Finset.sum_sdiff (Finset.Ico_subset_Ico_right (by omega : (A.image T v₁).card + 1 ≤ s))]
                exact Nat.le_add_left _ _
              have hsplit_set : Finset.Ico 2 (s + 1) = Finset.Ico 2 s ∪ {s} := by
                ext r; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
              have hdisj_set : Disjoint (Finset.Ico 2 s) {s} := by
                rw [Finset.disjoint_left]
                intro r hr1 hr2
                simp only [Finset.mem_Ico, Finset.mem_singleton] at hr1 hr2
                omega
              have hsplit : ∑ r ∈ Finset.Ico 2 (s + 1), (d + 1 - (r + 1) / 2) =
                  ∑ r ∈ Finset.Ico 2 s, (d + 1 - (r + 1) / 2) + (d + 1 - (s + 1) / 2) := by
                rw [hsplit_set, Finset.sum_union hdisj_set, Finset.sum_singleton]
              rw [List.length_append, hsplit]
              omega
        obtain ⟨v, hv_card, hv_len⟩ := hcontract R hR_ne hR_conn hR_card
        refine ⟨u ++ v, ?_, ?_⟩
        · have hsub_img : A.image (A.image Finset.univ u) v ⊆ A.image R v :=
            A.image_mono hR_img v
          have hne_img : (A.image (A.image Finset.univ u) v).Nonempty :=
            A.image_nonempty (A.image_nonempty Finset.univ_nonempty u) v
          have hcard_le : (A.image (A.image Finset.univ u) v).card ≤ (A.image R v).card :=
            Finset.card_le_card hsub_img
          have hcard_pos : 1 ≤ (A.image (A.image Finset.univ u) v).card := hne_img.card_pos
          rw [Aut.IsSyncWord, Aut.image_append]
          omega
        · have hsum_le : ∑ r ∈ Finset.Ico 2 (R.card + 1), (d + 1 - (r + 1) / 2) ≤
              ∑ r ∈ Finset.Ico 2 (d + 2), (d + 1 - (r + 1) / 2) := by
            rw [← Finset.sum_sdiff (Finset.Ico_subset_Ico_right (by omega : R.card + 1 ≤ d + 2))]
            exact Nat.le_add_left _ _
          rw [sum_ap_step] at hsum_le
          have hbound := apBound_add_step (d := d) hn₁_pos
          have hnd : Fintype.card Q₁ + d = n := by omega
          rw [hnd] at hbound
          rw [List.length_append]
          omega
  -- Actually: contracting R itself gives v with (A.image R v).card = 1,
  -- and since A.image Finset.univ u ⊆ R, (A.image (A.image Finset.univ u) v).card = 1!
  obtain ⟨C, hclosed, hC_ne, hreach, hC_sc, hC_sync⟩ := A.sink_scc_exists hsync
  haveI : Nonempty C := hC_ne.coe_sort
  have hapC : IsAperiodic (A.restrict C hclosed) := by
    intro w q m hm hiter
    apply Subtype.ext
    have h1 := congrArg Subtype.val hiter
    rw [Aut.restrict_eval] at h1
    rw [Aut.restrict_eval]
    exact hap w q.1 m hm h1
  obtain ⟨v, hv_sync, hv_len⟩ := hSC (Fintype.card C) (A.restrict C hclosed) rfl hC_sc hapC hC_sync
  obtain ⟨u, hu_sub, hu_len⟩ := A.absorption_lemma C hclosed hreach
  refine ⟨u ++ v, ?_, ?_⟩
  · rw [Aut.isSyncWord_iff_exists_eval_eq] at hv_sync ⊢
    obtain ⟨q₀, hq₀⟩ := hv_sync
    refine ⟨q₀.1, fun q => ?_⟩
    have hqu : A.eval q u ∈ C := hu_sub (Finset.mem_image_of_mem _ (Finset.mem_univ q))
    rw [Aut.eval_append]
    have := congrArg Subtype.val (hq₀ ⟨A.eval q u, hqu⟩)
    rw [Aut.restrict_eval] at this
    exact this
  · have hm_pos : 1 ≤ C.card := hC_ne.card_pos
    have hcard_C : Fintype.card C = C.card := Fintype.card_coe C
    have hC_le : C.card ≤ Fintype.card Q := Finset.card_le_univ C
    let k := Fintype.card Q - C.card
    have hnk : C.card + k = Fintype.card Q := by omega
    calc (u ++ v).length
        = u.length + v.length := List.length_append
      _ ≤ k * (k + 1) / 2 + apBound C.card := by
          rw [← hcard_C]; exact Nat.add_le_add hu_len hv_len
      _ = apBound C.card + k * (k + 1) / 2 := Nat.add_comm _ _
      _ ≤ apBound (C.card + k) := apBound_absorb hm_pos
      _ = apBound (Fintype.card Q) := by rw [hnk]

end MainBound

end Aperiodic
