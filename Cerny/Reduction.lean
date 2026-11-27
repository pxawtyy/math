import Cerny.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reduction to Strongly Connected Automata and Absorption Lemma

This module proves:
1. `sync_iff_pair_merge`: an automaton is synchronizing iff every pair of states merges.
2. `sink_scc_exists`: every synchronizing automaton has a unique sink SCC `C`
   whose restriction is strongly connected and synchronizing.
3. `absorption_lemma`: all states can be mapped into `C` by a word of length
   at most `k * (k + 1) / 2`, where `k = |Q| - |C|`.
4. `cerny_reduction_to_strongly_connected`: Černý's bound for strongly connected
   automata implies Černý's bound for all automata.
-/

namespace Aut

section PairMerge
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

private lemma sync_set_of_pair_merge
    (hmerge : ∀ p q : Q, ∃ w, A.eval p w = A.eval q w) :
    ∀ S : Finset Q, S.Nonempty → ∃ w : List α, (A.image S w).card = 1 := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    intro hS
    by_cases hn : n ≤ 1
    · have hc : S.card = 1 := by
        have := hS.card_pos
        omega
      exact ⟨[], by simpa [image_nil] using hc⟩
    · have h2 : 1 < S.card := by omega
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
      obtain ⟨u, hu⟩ := hmerge p q
      have himg_eq : A.image (S.erase q) u = A.image S u := by
        ext x
        simp only [mem_image]
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨r, Finset.erase_subset _ _ hr, rfl⟩
        · rintro ⟨r, hr, rfl⟩
          by_cases hrq : r = q
          · subst hrq
            exact ⟨p, Finset.mem_erase.mpr ⟨hpq, hp⟩, hu⟩
          · exact ⟨r, Finset.mem_erase.mpr ⟨hrq, hr⟩, rfl⟩
      have hcard_lt : (A.image S u).card < n := by
        rw [← himg_eq]
        calc (A.image (S.erase q) u).card
            ≤ (S.erase q).card := card_image_le _ _ _
          _ = S.card - 1 := Finset.card_erase_of_mem hq
          _ < n := by omega
      obtain ⟨v, hv⟩ := ih (A.image S u).card hcard_lt (A.image S u) rfl (A.image_nonempty hS u)
      exact ⟨u ++ v, by rw [image_append]; exact hv⟩

/-- An automaton on a nonempty finite state space is synchronizing iff every pair
of states can be merged. -/
theorem sync_iff_pair_merge [Nonempty Q] :
    A.IsSync ↔ ∀ p q : Q, ∃ w, A.eval p w = A.eval q w := by
  constructor
  · intro hsync p q
    obtain ⟨w, hw⟩ := hsync
    rw [isSyncWord_iff_exists_eval_eq] at hw
    obtain ⟨q₀, hq₀⟩ := hw
    exact ⟨w, by rw [hq₀ p, hq₀ q]⟩
  · intro hmerge
    obtain ⟨w, hw⟩ := A.sync_set_of_pair_merge hmerge Finset.univ Finset.univ_nonempty
    exact ⟨w, hw⟩

end PairMerge

section SinkSCC
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

/-- Restriction of an automaton `A` to a `step`-closed subset `C : Finset Q`. -/
def restrict (C : Finset Q) (hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C) :
    Aut C α where
  step q a := ⟨A.step q.1 a, hclosed q.1 q.2 a⟩

lemma restrict_eval (C : Finset Q) (hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C)
    (q : C) (w : List α) :
    ((A.restrict C hclosed).eval q w).1 = A.eval q.1 w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    simp only [eval_cons, ih]
    rfl

/-- Every synchronizing automaton on a nonempty state set has a nonempty `step`-closed
sink component `C` such that `A.restrict C` is strongly connected and synchronizing,
and every state reaches `C`. -/
theorem sink_scc_exists [Nonempty Q] (hsync : A.IsSync) :
    ∃ (C : Finset Q) (hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C),
      C.Nonempty ∧
      (∀ q : Q, ∃ w : List α, A.eval q w ∈ C) ∧
      (A.restrict C hclosed).StronglyConnected ∧
      (A.restrict C hclosed).IsSync := by
  classical
  obtain ⟨w₀, hw₀⟩ := hsync
  obtain ⟨c₀, hc₀⟩ := (A.isSyncWord_iff_exists_eval_eq).mp hw₀
  let C : Finset Q := Finset.univ.filter (fun q => ∃ w : List α, A.eval c₀ w = q)
  have hc₀_mem : c₀ ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl⟩
  have hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C := by
    intro q hq a
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨w, hw⟩ := hq
    exact ⟨w ++ [a], by simp [hw, eval_singleton]⟩
  refine ⟨C, hclosed, ⟨c₀, hc₀_mem⟩, ?_, ?_, ?_⟩
  · intro q
    exact ⟨w₀, by rw [hc₀ q]; exact hc₀_mem⟩
  · intro p q
    have hq : q.1 ∈ C := q.2
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨w, hw⟩ := hq
    refine ⟨w₀ ++ w, Subtype.ext ?_⟩
    rw [restrict_eval, eval_append, hc₀ p.1, hw]
  · have : Nonempty C := ⟨⟨c₀, hc₀_mem⟩⟩
    refine ⟨w₀, ?_⟩
    rw [isSyncWord_iff_exists_eval_eq]
    refine ⟨⟨c₀, hc₀_mem⟩, fun q => Subtype.ext ?_⟩
    rw [restrict_eval, hc₀ q.1]

end SinkSCC

section Absorption
variable {Q α : Type*} [Fintype Q] [DecidableEq Q] (A : Aut Q α)

private lemma eval_mem_of_closed (C : Finset Q)
    (hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C)
    {q : Q} (hq : q ∈ C) (w : List α) : A.eval q w ∈ C := by
  induction w generalizing q with
  | nil => exact hq
  | cons a w ih => exact ih (hclosed q hq a)

private def absorbBound (k t : ℕ) : ℕ :=
  t * k - t * (t - 1) / 2

private lemma tri_succ (t : ℕ) : (t + 1) * t / 2 = t * (t - 1) / 2 + t := by
  cases t with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    have hmul : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    omega

private lemma tri_le_mul {t k : ℕ} (ht : t ≤ k) : t * (t - 1) / 2 ≤ t * k := by
  have h1 : t * (t - 1) ≤ 2 * (t * k) := by
    have : t - 1 ≤ k := by omega
    nlinarith
  omega

private lemma absorbBound_succ {k t : ℕ} (ht : t < k) :
    absorbBound k (t + 1) = absorbBound k t + (k - t) := by
  unfold absorbBound
  simp only [Nat.add_sub_cancel]
  rw [tri_succ]
  have hle1 : t * (t - 1) / 2 ≤ t * k := tri_le_mul (by omega)
  have hle2 : t * (t - 1) / 2 + t ≤ (t + 1) * k := by
    have : (t + 1) * k = t * k + k := by ring
    omega
  have htk : (t + 1) * k = t * k + k := by ring
  omega

private lemma absorbBound_zero (k : ℕ) : absorbBound k 0 = 0 := by
  simp [absorbBound]

private lemma absorbBound_self (k : ℕ) : absorbBound k k = k * (k + 1) / 2 := by
  have h : ∀ t ≤ k, absorbBound k t + (k - t) * (k - t + 1) / 2 = k * (k + 1) / 2 := by
    intro t ht
    induction t with
    | zero => simp [absorbBound_zero]
    | succ m ih =>
      rw [absorbBound_succ (by omega)]
      have ih' := ih (by omega)
      have hkm : k - m = (k - (m + 1)) + 1 := by omega
      have htri : (k - m) * (k - m + 1) / 2 = (k - (m + 1)) * (k - (m + 1) + 1) / 2 + (k - m) := by
        rw [hkm]
        have := tri_succ (k - (m + 1) + 1)
        simp only [Nat.add_sub_cancel] at this
        have h1 : (k - (m + 1) + 1) * (k - (m + 1) + 1 + 1) =
            (k - (m + 1) + 1 + 1) * (k - (m + 1) + 1) := by ring
        have h2 : (k - (m + 1)) * (k - (m + 1) + 1) =
            (k - (m + 1) + 1) * (k - (m + 1)) := by ring
        omega
      omega
  simpa using h k le_rfl

private lemma absorbBound_mono {k a b : ℕ} (hab : a ≤ b) (hb : b ≤ k) :
    absorbBound k a ≤ absorbBound k b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    calc absorbBound k a
        ≤ absorbBound k (a + d) := ih (by omega) (by omega)
      _ ≤ absorbBound k (a + d + 1) := by
          rw [absorbBound_succ (by omega)]
          omega

private lemma absorbBound_step {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    (k - r + 1) + absorbBound k (r - 1) ≤ absorbBound k r := by
  have hr_eq : r = (r - 1) + 1 := by omega
  conv_rhs => rw [hr_eq]
  rw [absorbBound_succ (by omega)]
  omega

/-- Absorption lemma: if `C` is a `step`-closed subset of `Q` reachable from every state,
and `k = |Q| - |C|`, then there is a word `u` of length `≤ k * (k + 1) / 2` mapping all of
`Q` into `C`. -/
theorem absorption_lemma (C : Finset Q)
    (hclosed : ∀ q ∈ C, ∀ a : α, A.step q a ∈ C)
    (hreach : ∀ q : Q, ∃ w : List α, A.eval q w ∈ C) :
    let k := Fintype.card Q - C.card
    ∃ u : List α, A.image Finset.univ u ⊆ C ∧ u.length ≤ k * (k + 1) / 2 := by
  classical
  intro k
  have hmain : ∀ r : ℕ, ∀ S : Finset Q, (S \ C).card = r →
      ∃ u : List α, A.image S u ⊆ C ∧ u.length ≤ absorbBound k r := by
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro S hr_eq
      by_cases hr0 : r = 0
      · subst hr0
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hr_eq
        refine ⟨[], ?_, by simp [absorbBound_zero]⟩
        simpa [image_nil] using hr_eq
      · have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero hr0
        have hSC_ne : (S \ C).Nonempty := Finset.card_pos.mp (by omega)
        have hdist : ∀ q : Q, ∃ n : ℕ, ∃ v : List α, v.length = n ∧ A.eval q v ∈ C := by
          intro q
          obtain ⟨v, hv⟩ := hreach q
          exact ⟨v.length, v, rfl, hv⟩
        let d : Q → ℕ := fun q => Nat.find (hdist q)
        obtain ⟨q_star, hq_star_mem, hq_star_min⟩ := Finset.exists_min_image (S \ C) d hSC_ne
        have hq_star_nC : q_star ∉ C := (Finset.mem_sdiff.mp hq_star_mem).2
        obtain ⟨v, hv_len, hv_inC⟩ := Nat.find_spec (hdist q_star)
        change v.length = d q_star at hv_len
        have hd_pos : 1 ≤ d q_star := by
          by_contra h0
          have hd0 : d q_star = 0 := by omega
          rw [hd0, List.length_eq_zero_iff] at hv_len
          subst hv_len
          exact hq_star_nC hv_inC
        -- Intermediate states q_j = eval q_star (v.take j) for j < d q_star
        let qj : ℕ → Q := fun j => A.eval q_star (v.take j)
        have hqj_nC : ∀ j < d q_star, qj j ∉ C := by
          intro j hj hmem
          have hle : d q_star ≤ j := Nat.find_min' (hdist q_star)
            ⟨v.take j, by rw [List.length_take, hv_len]; omega, hmem⟩
          omega
        have hqj_inj : ∀ i j, i < j → j < d q_star → qj i ≠ qj j := by
          intro i j hij hj heq
          let v' := v.take i ++ v.drop j
          have hv'_len : v'.length < d q_star := by
            simp only [v', List.length_append, List.length_take, List.length_drop, hv_len]
            omega
          have hv'_mem : A.eval q_star v' ∈ C := by
            simp only [v', eval_append]
            change A.eval (qj i) (v.drop j) ∈ C
            rw [heq]
            change A.eval (A.eval q_star (v.take j)) (v.drop j) ∈ C
            rw [← eval_append, List.take_append_drop]
            exact hv_inC
          have hle := Nat.find_min' (hdist q_star) ⟨v', rfl, hv'_mem⟩
          change d q_star ≤ v'.length at hle
          omega
        have hqj_not_SC : ∀ j, 1 ≤ j → j < d q_star → qj j ∉ S \ C := by
          intro j hj1 hj hmem
          have hmin := hq_star_min (qj j) hmem
          have hle : d (qj j) ≤ d q_star - j := by
            apply Nat.find_min' (hdist (qj j))
            refine ⟨v.drop j, by rw [List.length_drop, hv_len], ?_⟩
            change A.eval (A.eval q_star (v.take j)) (v.drop j) ∈ C
            rw [← eval_append, List.take_append_drop]
            exact hv_inC
          omega
        -- Map j ∈ Finset.Ico 1 (d q_star) into (Finset.univ \ C) \ (S \ C)
        let mid : Finset Q := (Finset.Ico 1 (d q_star)).image qj
        have hmid_sub : mid ⊆ (Finset.univ \ C) \ (S \ C) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
          rw [Finset.mem_Ico] at hj
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨hqj_nC j hj.2, by simpa [Finset.mem_sdiff] using hqj_not_SC j hj.1 hj.2⟩
        have hmid_card : mid.card = d q_star - 1 := by
          rw [Finset.card_image_of_injOn]
          · simp [Nat.card_Ico]
          · intro a ha b hb hab
            rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
            rcases lt_trichotomy a b with hlt | rfl | hgt
            · exact absurd hab (hqj_inj a b hlt hb.2)
            · rfl
            · exact absurd hab.symm (hqj_inj b a hgt ha.2)
        have hSC_sub_univ : S \ C ⊆ Finset.univ \ C := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
          exact hx.2
        have hunivC_card : (Finset.univ \ C).card = k := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ C), Finset.card_univ]
        have hrk : r ≤ k := by
          rw [← hr_eq, ← hunivC_card]
          exact Finset.card_le_card hSC_sub_univ
        have hdiff_card : ((Finset.univ \ C) \ (S \ C)).card = k - r := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSC_sub_univ, hunivC_card, hr_eq]
        have hd_le : d q_star ≤ k - r + 1 := by
          have := Finset.card_le_card hmid_sub
          rw [hmid_card, hdiff_card] at this
          omega
        -- Now check that (A.image S v \ C).card ≤ r - 1
        let S' := A.image S v
        have hS'_sub : S' \ C ⊆ A.image ((S \ C).erase q_star) v := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rcases (mem_image A).mp hx.1 with ⟨p, hpS, rfl⟩
          have hp_nC : p ∉ C := fun hpC => hx.2 (eval_mem_of_closed A C hclosed hpC v)
          have hp_ne : p ≠ q_star := by
            rintro rfl
            exact hx.2 hv_inC
          exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hp_ne, Finset.mem_sdiff.mpr ⟨hpS, hp_nC⟩⟩)
        have hr'_le : (S' \ C).card ≤ r - 1 := by
          calc (S' \ C).card
              ≤ (A.image ((S \ C).erase q_star) v).card := Finset.card_le_card hS'_sub
            _ ≤ ((S \ C).erase q_star).card := card_image_le _ _ _
            _ = r - 1 := by rw [Finset.card_erase_of_mem hq_star_mem, hr_eq]
        have hr'_lt : (S' \ C).card < r := by omega
        obtain ⟨u', hu'_sub, hu'_len⟩ := ih (S' \ C).card hr'_lt S' rfl
        refine ⟨v ++ u', ?_, ?_⟩
        · rw [image_append]
          exact hu'_sub
        · calc (v ++ u').length
              = v.length + u'.length := List.length_append
            _ ≤ d q_star + absorbBound k (S' \ C).card := by rw [hv_len]; exact Nat.add_le_add_left hu'_len _
            _ ≤ (k - r + 1) + absorbBound k (r - 1) := by
                have hmono := absorbBound_mono hr'_le (by omega : r - 1 ≤ k)
                omega
            _ ≤ absorbBound k r := absorbBound_step hr_pos hrk
  have huniv_sub : (Finset.univ \ C).card ≤ k := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ C), Finset.card_univ]
  obtain ⟨u, hu_sub, hu_len⟩ := hmain (Finset.univ \ C).card Finset.univ rfl
  refine ⟨u, hu_sub, ?_⟩
  calc u.length
      ≤ absorbBound k (Finset.univ \ C).card := hu_len
    _ ≤ absorbBound k k := absorbBound_mono huniv_sub le_rfl
    _ = k * (k + 1) / 2 := absorbBound_self k

end Absorption

section ReductionTheorem

private lemma cerny_reduction_arith (m k : ℕ) (hm : 1 ≤ m) :
    (m - 1) ^ 2 + k * (k + 1) / 2 ≤ (m + k - 1) ^ 2 := by
  have hdiv : 2 * (k * (k + 1) / 2) ≤ k * (k + 1) := Nat.mul_div_le _ 2
  have h1 : m - 1 + k = m + k - 1 := by omega
  have h2 : (m + k - 1) ^ 2 = (m - 1) ^ 2 + 2 * (m - 1) * k + k ^ 2 := by
    rw [← h1]; ring
  nlinarith

/-- If Černý's bound `(m - 1)^2` holds for all strongly connected synchronizing
automata, then it holds for all synchronizing automata. -/
theorem cerny_reduction_to_strongly_connected
    (hSC : ∀ {Q' : Type u} {α' : Type v} [Fintype Q'] [DecidableEq Q'] [Nonempty Q']
      (B : Aut Q' α'), B.StronglyConnected → B.IsSync →
      ∃ w : List α', B.IsSyncWord w ∧ w.length ≤ (Fintype.card Q' - 1) ^ 2) :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] [Nonempty Q]
      (A : Aut Q α), A.IsSync →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  intro Q α _ _ _ A hsync
  obtain ⟨C, hclosed, hC_ne, hreach, hC_sc, hC_sync⟩ := A.sink_scc_exists hsync
  have : Nonempty C := hC_ne.coe_sort
  obtain ⟨v, hv_sync, hv_len⟩ := hSC (B := A.restrict C hclosed) hC_sc hC_sync
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
      _ ≤ k * (k + 1) / 2 + (C.card - 1) ^ 2 := by rw [← hcard_C]; exact Nat.add_le_add hu_len hv_len
      _ = (C.card - 1) ^ 2 + k * (k + 1) / 2 := Nat.add_comm _ _
      _ ≤ (C.card + k - 1) ^ 2 := cerny_reduction_arith C.card k hm_pos
      _ = (Fintype.card Q - 1) ^ 2 := by rw [hnk]

end ReductionTheorem

end Aut
