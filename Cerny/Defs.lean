import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

/-!
# Base Definitions for Finite Automata and Synchronizing Words

This module defines the minimal complete deterministic finite automaton `Aut Q α`
and basic operations (`eval`, `image`, `preimage`, `IsSyncWord`, `IsSync`,
`StronglyConnected`) along with fundamental lemmas.
-/

/-- A complete deterministic finite automaton with state type `Q` and alphabet `α`. -/
structure Aut (Q α : Type*) where
  /-- Transition function. -/
  step : Q → α → Q

namespace Aut

section Basic
variable {Q α : Type*} (A : Aut Q α)

/-- Evaluate the automaton starting from state `q` along word `w`. -/
def eval (q : Q) (w : List α) : Q :=
  w.foldl A.step q

@[simp]
lemma eval_nil (q : Q) : A.eval q [] = q := rfl

@[simp]
lemma eval_cons (q : Q) (a : α) (w : List α) :
    A.eval q (a :: w) = A.eval (A.step q a) w := rfl

@[simp]
lemma eval_append (q : Q) (u v : List α) :
    A.eval q (u ++ v) = A.eval (A.eval q u) v := by
  simp [eval, List.foldl_append]

lemma eval_singleton (q : Q) (a : α) : A.eval q [a] = A.step q a := rfl

/-- Strong connectivity: every state is reachable from every other state. -/
def StronglyConnected : Prop :=
  ∀ p q : Q, ∃ w, A.eval p w = q

end Basic

section FinsetOps
variable {Q α : Type*} [DecidableEq Q] (A : Aut Q α)

/-- Image of a set of states `S` under word `w`. -/
def image (S : Finset Q) (w : List α) : Finset Q :=
  S.image (fun q => A.eval q w)

@[simp]
lemma image_nil (S : Finset Q) : A.image S [] = S := by
  simp [image]

@[simp]
lemma image_empty (w : List α) : A.image ∅ w = ∅ := by
  simp [image]

lemma mem_image {S : Finset Q} {w : List α} {q' : Q} :
    q' ∈ A.image S w ↔ ∃ q ∈ S, A.eval q w = q' := by
  simp [image]

lemma image_append (S : Finset Q) (u v : List α) :
    A.image S (u ++ v) = A.image (A.image S u) v := by
  ext q
  simp only [mem_image, eval_append]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨A.eval p u, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

lemma image_mono {S T : Finset Q} (h : S ⊆ T) (w : List α) :
    A.image S w ⊆ A.image T w :=
  Finset.image_subset_image h

lemma image_nonempty {S : Finset Q} (hS : S.Nonempty) (w : List α) :
    (A.image S w).Nonempty :=
  hS.image _

lemma card_image_le (S : Finset Q) (w : List α) :
    (A.image S w).card ≤ S.card :=
  Finset.card_image_le

lemma image_singleton (q : Q) (w : List α) :
    A.image {q} w = {A.eval q w} := by
  simp [image]

section FintypeQ
variable [Fintype Q]

/-- Preimage of a set of states `S` under word `w`. -/
def preimage (S : Finset Q) (w : List α) : Finset Q :=
  Finset.univ.filter (fun q => A.eval q w ∈ S)

@[simp]
lemma mem_preimage {S : Finset Q} {w : List α} {q : Q} :
    q ∈ A.preimage S w ↔ A.eval q w ∈ S := by
  simp [preimage]

@[simp]
lemma preimage_nil (S : Finset Q) : A.preimage S [] = S := by
  ext q; simp

@[simp]
lemma preimage_empty (w : List α) : A.preimage ∅ w = ∅ := by
  ext q; simp

@[simp]
lemma preimage_univ (w : List α) : A.preimage Finset.univ w = Finset.univ := by
  ext q; simp

lemma preimage_append (S : Finset Q) (u v : List α) :
    A.preimage (A.preimage S u) v = A.preimage S (v ++ u) := by
  ext q; simp [eval_append]

lemma preimage_mono {S T : Finset Q} (h : S ⊆ T) (w : List α) :
    A.preimage S w ⊆ A.preimage T w := by
  intro q hq
  simp only [mem_preimage] at hq ⊢
  exact h hq

lemma image_subset_iff_subset_preimage {S T : Finset Q} {w : List α} :
    A.image S w ⊆ T ↔ S ⊆ A.preimage T w := by
  constructor
  · intro h q hq
    rw [mem_preimage]
    exact h (Finset.mem_image_of_mem _ hq)
  · intro h q hq
    rcases (mem_image A).mp hq with ⟨p, hp, rfl⟩
    exact (mem_preimage A).mp (h hp)

/-- `w` is a synchronizing word if it maps all states to a single state. -/
def IsSyncWord (w : List α) : Prop :=
  (A.image Finset.univ w).card = 1

/-- `A` is synchronizing if it admits a synchronizing word. -/
def IsSync : Prop :=
  ∃ w, A.IsSyncWord w

lemma isSyncWord_nil_of_subsingleton [Subsingleton Q] [Nonempty Q] :
    A.IsSyncWord [] := by
  simp only [IsSyncWord, image_nil, Finset.card_eq_one]
  refine ⟨Classical.arbitrary Q, ?_⟩
  ext x
  simp [Subsingleton.elim x (Classical.arbitrary Q)]

lemma isSync_of_card_eq_one (h : Fintype.card Q = 1) : A.IsSync := by
  rw [← Finset.card_univ, Finset.card_eq_one] at h
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨[], ?_⟩
  simp only [IsSyncWord, image_nil, Finset.card_eq_one]
  exact ⟨q₀, hq₀⟩

lemma isSyncWord_iff_preimage_univ [Nonempty Q] {w : List α} :
    A.IsSyncWord w ↔ ∃ q₀ : Q, A.preimage {q₀} w = Finset.univ := by
  unfold IsSyncWord
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp only [mem_preimage, Finset.mem_singleton, Finset.mem_univ, iff_true]
    have hmem : A.eval q w ∈ A.image Finset.univ w :=
      Finset.mem_image_of_mem _ (Finset.mem_univ q)
    rw [hq₀, Finset.mem_singleton] at hmem
    exact hmem
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q'
    simp only [mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨q, rfl⟩
      have hq : q ∈ A.preimage {q₀} w := by rw [hq₀]; exact Finset.mem_univ q
      simpa using hq
    · rintro rfl
      obtain ⟨q⟩ := ‹Nonempty Q›
      have hq : q ∈ A.preimage {q'} w := by rw [hq₀]; exact Finset.mem_univ q
      exact ⟨q, by simpa using hq⟩

lemma isSyncWord_iff_exists_eval_eq [Nonempty Q] {w : List α} :
    A.IsSyncWord w ↔ ∃ q₀ : Q, ∀ q : Q, A.eval q w = q₀ := by
  rw [isSyncWord_iff_preimage_univ]
  constructor
  · rintro ⟨q₀, h⟩
    refine ⟨q₀, fun q => ?_⟩
    have hq : q ∈ A.preimage {q₀} w := by rw [h]; exact Finset.mem_univ q
    simpa using hq
  · rintro ⟨q₀, h⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp [h q]

lemma isSyncWord_append_left [Nonempty Q] {u v : List α} (hv : A.IsSyncWord v) :
    A.IsSyncWord (u ++ v) := by
  rw [isSyncWord_iff_exists_eval_eq] at hv ⊢
  obtain ⟨q₀, hq₀⟩ := hv
  exact ⟨q₀, fun q => by simp [hq₀]⟩

lemma isSyncWord_append_right [Nonempty Q] {u v : List α} (hu : A.IsSyncWord u) :
    A.IsSyncWord (u ++ v) := by
  rw [isSyncWord_iff_exists_eval_eq] at hu ⊢
  obtain ⟨q₀, hq₀⟩ := hu
  exact ⟨A.eval q₀ v, fun q => by simp [hq₀]⟩

/-- A synchronizing automaton with at least two states has a letter whose transition
map is not bijective. -/
lemma exists_nonbijective_letter [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (hn2 : 2 ≤ Fintype.card Q) : ∃ b : α, ¬ Function.Bijective (fun q => A.step q b) := by
  classical
  by_contra hall
  push_neg at hall
  have hbij_word : ∀ w : List α, Function.Bijective (fun q => A.eval q w) := by
    intro w
    induction w with
    | nil => exact Function.bijective_id
    | cons b rest ih => exact ih.comp (hall b)
  obtain ⟨w, hw⟩ := hsync
  rw [isSyncWord_iff_exists_eval_eq] at hw
  obtain ⟨q₀, hq₀⟩ := hw
  obtain ⟨p₁, p₂, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Q)
  exact hne ((hbij_word w).injective ((hq₀ p₁).trans (hq₀ p₂).symm))

/-- A synchronizing automaton with at least two states has a letter with a collision
in its preimage: some state has at least two preimages under that single letter. -/
lemma exists_collision_letter_of_isSync [Nonempty Q] (A : Aut Q α) (hsync : A.IsSync)
    (hn2 : 2 ≤ Fintype.card Q) : ∃ (c₀ : Q) (b : α), 2 ≤ (A.preimage {c₀} [b]).card := by
  classical
  obtain ⟨b, hb⟩ := A.exists_nonbijective_letter hsync hn2
  have hnotinj : ¬ Function.Injective (fun q => A.step q b) := by
    intro hinj
    exact hb (Finite.injective_iff_bijective.mp hinj)
  have hcoll : ∃ p₁ p₂, A.step p₁ b = A.step p₂ b ∧ p₁ ≠ p₂ := by
    by_contra hcoll
    apply hnotinj
    intro p₁ p₂ heq
    by_contra hne
    exact hcoll ⟨p₁, p₂, heq, hne⟩
  obtain ⟨p₁, p₂, heq, hne⟩ := hcoll
  refine ⟨A.step p₁ b, b, ?_⟩
  have hsub : ({p₁, p₂} : Finset Q) ⊆ A.preimage {A.step p₁ b} [b] := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [Aut.mem_preimage]
    · simp [Aut.mem_preimage, heq]
  rw [← Finset.card_pair hne]
  exact Finset.card_le_card hsub

/-- Given a backward chain of preimages from `{q₀}` up to `Finset.univ`,
the reverse concatenation of the words is a synchronizing word of total length `∑ i, (w i).length`. -/
lemma isSyncWord_of_chain [Nonempty Q] (k : ℕ) (S : Fin (k + 1) → Finset Q)
    (w : Fin k → List α) (q₀ : Q)
    (h0 : S 0 = {q₀})
    (hk : S (Fin.last k) = Finset.univ)
    (hstep : ∀ i : Fin k, S i.succ ⊆ A.preimage (S i.castSucc) (w i)) :
    ∃ u : List α, A.IsSyncWord u ∧ u.length = ∑ i : Fin k, (w i).length := by
  have hsub : ∀ j : ℕ, (hj : j ≤ k) →
      ∃ u : List α, S ⟨j, Nat.lt_succ_of_le hj⟩ ⊆ A.preimage {q₀} u ∧
        u.length = ∑ i : Fin j, (w (Fin.castLE hj i)).length := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨[], ?_, by simp⟩
      simpa [h0] using subset_rfl
    | succ j ih =>
      intro hj
      obtain ⟨u, hu, hlen⟩ := ih (Nat.le_of_succ_le hj)
      let i : Fin k := ⟨j, hj⟩
      refine ⟨w i ++ u, ?_, ?_⟩
      · rw [← preimage_append]
        exact (hstep i).trans (A.preimage_mono hu (w i))
      · simp only [List.length_append, hlen, Fin.sum_univ_castSucc]
        rw [add_comm]
        rfl
  obtain ⟨u, hu, hlen⟩ := hsub k le_rfl
  refine ⟨u, ?_, hlen⟩
  rw [isSyncWord_iff_preimage_univ]
  refine ⟨q₀, ?_⟩
  ext q
  simp only [Finset.mem_univ, iff_true]
  exact hu (by rw [show (⟨k, Nat.lt_succ_of_le le_rfl⟩ : Fin (k + 1)) = Fin.last k from rfl, hk]; exact Finset.mem_univ q)

end FintypeQ
end FinsetOps

end Aut
