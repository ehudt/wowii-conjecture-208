/-
Copyright 2026 Ehud Tamir

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import WOWII208.Defs

/-!
# Proof Development: Written on the Wall II — Conjecture 208

Complete, self-contained, zero-dependency Lean 4 proof of WOWII Conjecture 208.
-/

@[expose] public section

namespace WOWII208

theorem list_length_filter_eq_countP {α : Type} (l : List α) (P : α → Bool) :
    (l.filter P).length = l.countP P := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.countP_cons]
    cases P x <;> simp [ih]

theorem list_nodup_reverse {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.reverse_cons, List.nodup_append]
    refine ⟨ih h.2, by simp, fun a ha b hb hab => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb; subst hab
    exact h.1 (List.mem_reverse.mp ha)

theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (heq : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq ▸ List.getElem_mem ..) h.1
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq.symm ▸ List.getElem_mem ..) h.1
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        simp only [List.length_cons] at hi hj
        exact congrArg Nat.succ (ih h.2 (by omega) (by omega) heq)

theorem list_nodup_map_inj_on {α β : Type} {l : List α} (f : α → β)
    (hnd : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun x hx y hy =>
      hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))⟩
    intro hm
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hm
    have := hinj y (List.mem_cons_of_mem a hy) a (List.mem_cons_self ..) hya
    subst this; exact hnd.1 hy

theorem list_countP_or_le {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP (fun x => P x || Q x) ≤ l.countP P + l.countP Q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    cases P x <;> cases Q x <;> simp <;> omega

theorem list_countP_le_length {α : Type} (l : List α) (P : α → Bool) :
    l.countP P ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases P x <;> simp <;> omega

theorem list_countP_add_not {α : Type} (l : List α) (P : α → Bool) :
    l.countP P + l.countP (fun x => !P x) = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases P x <;> simp <;> omega

theorem list_countP_mono {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ x ∈ l, P x = true → Q x = true) :
    l.countP P ≤ l.countP Q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x (List.mem_cons_self ..)
    cases hP : P x <;> cases hQ : Q x
    · simp; exact hxs
    · simp; omega
    · exact absurd (hx hP) (by simp [hQ])
    · simp; exact hxs

theorem list_countP_eq_of_eq {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ x ∈ l, P x = Q x) :
    l.countP P = l.countP Q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem list_countP_disjoint {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ x ∈ l, !(P x && Q x) = true) :
    l.countP P + l.countP Q ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x (List.mem_cons_self ..)
    cases hP : P x <;> cases hQ : Q x <;> simp_all <;> omega

theorem list_countP_add_split {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP (fun x => P x && Q x) + l.countP (fun x => P x && !Q x) = l.countP P := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    cases P x <;> cases Q x <;> simp <;> omega

theorem list_countP_pos_iff {α : Type} (l : List α) (P : α → Bool) :
    0 < l.countP P ↔ ∃ x ∈ l, P x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.mem_cons]
    cases hP : P x
    · simp [hP, ih]
    · simp [hP]

theorem list_countP_eq_zero_iff {α : Type} (l : List α) (P : α → Bool) :
    l.countP P = 0 ↔ ∀ x ∈ l, P x = false := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.mem_cons]
    cases hP : P x
    · simp [hP, ih]
    · simp [hP]

theorem list_countP_eq_of_forall_true {α : Type} (l : List α) (P : α → Bool)
    (h : ∀ x ∈ l, P x = true) : l.countP P = l.length := by
  have h0 : l.countP (fun x => !P x) = 0 :=
    (list_countP_eq_zero_iff l _).mpr (fun x hx => by simp [h x hx])
  have := list_countP_add_not l P
  omega

theorem list_countP_single {α : Type} [DecidableEq α] (l : List α) (a : α)
    (hnodup : l.Nodup) (hmem : a ∈ l) :
    l.countP (fun x => decide (x = a)) = 1 := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    simp only [List.countP_cons]
    by_cases hxa : x = a
    · subst hxa
      have h0 : xs.countP (fun y => decide (y = x)) = 0 :=
        (list_countP_eq_zero_iff xs _).mpr (fun y hy => by
          simp only [decide_eq_false_iff_not]
          intro h; subst h; exact hnodup.1 hy)
      simp [h0]
    · have hmem' : a ∈ xs := by
        cases hmem with
        | head => exact absurd rfl hxa
        | tail _ h => exact h
      simp [hxa, ih hnodup.2 hmem']

theorem list_sum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

theorem list_sum_map_eq {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem list_sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

theorem list_sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, Nat.succ_mul]
    omega

theorem list_sum_map_ite_const {α : Type} (l : List α) (P : α → Bool) (c : Nat) :
    (l.map (fun x => if P x then c else 0)).sum = l.countP P * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    cases P x
    · simp; exact ih
    · simp [ih, Nat.succ_mul]; omega

theorem list_sum_map_mul_left {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Nat.mul_add]

theorem list_sum_map_countP_swap {α β : Type} (la : List α) (lb : List β) (R : α → β → Bool) :
    (la.map (fun a => lb.countP (fun b => R a b))).sum =
    (lb.map (fun b => la.countP (fun a => R a b))).sum := by
  induction la with
  | nil =>
    simp [list_sum_map_const]
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have hstep : (lb.map (fun b => (a :: as).countP (fun x => R x b))).sum =
        (lb.map (fun b => (if R a b then 1 else 0) + as.countP (fun x => R x b))).sum := by
      apply list_sum_map_eq
      intro b _
      simp only [List.countP_cons]
      cases R a b <;> simp <;> omega
    rw [hstep, list_sum_map_add, list_sum_map_ite_const]
    have heq_cnt : lb.countP (fun b => R a b) = lb.countP (R a) := rfl
    omega

theorem list_sum_eq_const_imp {α : Type} (l : List α) (P : α → Bool) (f : α → Nat) (c : Nat)
    (hle : ∀ x ∈ l, P x = true → f x ≤ c)
    (heq : (l.map (fun x => if P x then f x else 0)).sum = l.countP P * c) :
    ∀ x ∈ l, P x = true → f x = c := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons] at heq
    have hle_as : ∀ y ∈ as, P y = true → f y ≤ c :=
      fun y hy => hle y (List.mem_cons_of_mem a hy)
    have hsum_le : (as.map (fun x => if P x then f x else 0)).sum ≤ as.countP P * c := by
      have h1 : (as.map (fun x => if P x then f x else 0)).sum ≤
          (as.map (fun x => if P x then c else 0)).sum := by
        apply list_sum_map_le
        intro y hy
        cases hPy : P y
        · simp
        · simp [hle_as y hy hPy]
      rw [list_sum_map_ite_const] at h1
      exact h1
    cases hPa : P a
    · simp [hPa] at heq
      intro x hx hPx
      cases hx with
      | head => rw [hPa] at hPx; cases hPx
      | tail _ h => exact ih hle_as heq x h hPx
    · simp only [hPa, ↓reduceIte] at heq
      have hfa : f a ≤ c := hle a (List.mem_cons_self ..) hPa
      rw [Nat.succ_mul] at heq
      have hfa_eq : f a = c := by omega
      have has_eq : (as.map (fun x => if P x then f x else 0)).sum = as.countP P * c := by omega
      intro x hx hPx
      cases hx with
      | head => exact hfa_eq
      | tail _ h => exact ih hle_as has_eq x h hPx

theorem list_nodup_subset_countP {α : Type} [DecidableEq α] (l : List α) (u : List α)
    (hnodup : l.Nodup) (hsub : ∀ x ∈ l, x ∈ u) (P : α → Bool)
    (hP : ∀ x ∈ l, P x = true) :
    l.length ≤ u.countP P := by
  induction l generalizing u with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnodup
    have hPa : P a = true := hP a (List.mem_cons_self ..)
    have ha_u : a ∈ u := hsub a (List.mem_cons_self ..)
    -- Split u at a
    have ⟨u1, u2, hu⟩ := List.append_of_mem ha_u
    subst hu
    have hsub' : ∀ x ∈ as, x ∈ u1 ++ u2 := by
      intro x hx
      have hxu : x ∈ u1 ++ a :: u2 := hsub x (List.mem_cons_of_mem a hx)
      rw [List.mem_append, List.mem_cons] at hxu
      rw [List.mem_append]
      rcases hxu with h1 | h2 | h3
      · exact Or.inl h1
      · subst h2; exact absurd hx hnodup.1
      · exact Or.inr h3
    have hih := ih (u1 ++ u2) hnodup.2 hsub' (fun x hx => hP x (List.mem_cons_of_mem a hx))
    simp only [List.countP_append, List.countP_cons, hPa, ↓reduceIte] at hih ⊢
    simp only [List.length_cons]
    omega

theorem nodup_length_le_countFin {n : Nat} (l : List (Fin n)) (hnodup : l.Nodup)
    (P : Fin n → Bool) (hP : ∀ x ∈ l, P x = true) :
    l.length ≤ countFin n P :=
  list_nodup_subset_countP l (List.finRange n) hnodup (fun x _ => List.mem_finRange x) P hP

theorem nodup_length_le_n {n : Nat} (l : List (Fin n)) (hnodup : l.Nodup) :
    l.length ≤ n := by
  have h := nodup_length_le_countFin l hnodup (fun _ => true) (fun _ _ => rfl)
  have h2 : countFin n (fun _ => true) = n := by
    unfold countFin
    rw [list_countP_eq_of_forall_true _ _ (fun _ _ => rfl), List.length_finRange]
  omega

theorem countFin_le (n : Nat) (P : Fin n → Bool) : countFin n P ≤ n := by
  unfold countFin
  have := list_countP_le_length (List.finRange n) P
  rw [List.length_finRange] at this
  exact this

theorem countFin_add_not (n : Nat) (P : Fin n → Bool) :
    countFin n P + countFin n (fun x => !P x) = n := by
  unfold countFin
  have := list_countP_add_not (List.finRange n) P
  rw [List.length_finRange] at this
  exact this

theorem countFin_mono (n : Nat) (P Q : Fin n → Bool)
    (h : ∀ x : Fin n, P x = true → Q x = true) :
    countFin n P ≤ countFin n Q :=
  list_countP_mono (List.finRange n) P Q (fun x _ => h x)

theorem countFin_eq (n : Nat) (P Q : Fin n → Bool) (h : ∀ x : Fin n, P x = Q x) :
    countFin n P = countFin n Q :=
  list_countP_eq_of_eq (List.finRange n) P Q (fun x _ => h x)

theorem countFin_single (n : Nat) (a : Fin n) :
    countFin n (fun x => decide (x = a)) = 1 :=
  list_countP_single (List.finRange n) a (List.nodup_finRange n) (List.mem_finRange a)

theorem countFin_pos_iff (n : Nat) (P : Fin n → Bool) :
    0 < countFin n P ↔ ∃ x : Fin n, P x = true := by
  unfold countFin
  rw [list_countP_pos_iff]
  constructor
  · rintro ⟨x, _, h⟩; exact ⟨x, h⟩
  · rintro ⟨x, h⟩; exact ⟨x, List.mem_finRange x, h⟩

theorem countFin_eq_zero_iff (n : Nat) (P : Fin n → Bool) :
    countFin n P = 0 ↔ ∀ x : Fin n, P x = false := by
  unfold countFin
  rw [list_countP_eq_zero_iff]
  constructor
  · intro h x; exact h x (List.mem_finRange x)
  · intro h x _; exact h x

theorem sumFin_le (n : Nat) (f g : Fin n → Nat) (h : ∀ x : Fin n, f x ≤ g x) :
    sumFin n f ≤ sumFin n g :=
  list_sum_map_le (List.finRange n) f g (fun x _ => h x)

theorem sumFin_eq (n : Nat) (f g : Fin n → Nat) (h : ∀ x : Fin n, f x = g x) :
    sumFin n f = sumFin n g :=
  list_sum_map_eq (List.finRange n) f g (fun x _ => h x)

theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun x => f x + g x) = sumFin n f + sumFin n g :=
  list_sum_map_add (List.finRange n) f g

theorem sumFin_const (n : Nat) (c : Nat) :
    sumFin n (fun _ => c) = n * c := by
  unfold sumFin
  rw [list_sum_map_const, List.length_finRange]

theorem sumFin_swap (n : Nat) (R : Fin n → Fin n → Bool) :
    sumFin n (fun u => countFin n (fun v => R u v)) =
    sumFin n (fun v => countFin n (fun u => R u v)) :=
  list_sum_map_countP_swap (List.finRange n) (List.finRange n) R

theorem exists_subset_of_countFin_ge {n : Nat} (P : Fin n → Bool) (k : Nat)
    (hk : k ≤ countFin n P) :
    ∃ Q : Fin n → Bool, (∀ x, Q x = true → P x = true) ∧ countFin n Q = k := by
  -- Take the first k elements of (List.finRange n).filter P
  let L := ((List.finRange n).filter P).take k
  have hflen : ((List.finRange n).filter P).length = countFin n P := by
    unfold countFin
    rw [list_length_filter_eq_countP]
  have hLlen : L.length = k := by
    simp [L, List.length_take, hflen, Nat.min_eq_left hk]
  have hLnodup : L.Nodup :=
    ((List.nodup_finRange n).filter P).take
  have hLsub : ∀ x ∈ L, P x = true := by
    intro x hx
    have hmem := List.mem_of_mem_take hx
    exact (List.mem_filter.mp hmem).2
  refine ⟨fun x => decide (x ∈ L), ?_, ?_⟩
  · intro x hx
    exact hLsub x (of_decide_eq_true hx)
  · have hle : L.length ≤ countFin n (fun x => decide (x ∈ L)) :=
      nodup_length_le_countFin L hLnodup _ (fun x hx => decide_eq_true hx)
    have hge : countFin n (fun x => decide (x ∈ L)) ≤ L.length := by
      unfold countFin
      have h1 : (List.finRange n).countP (fun x => decide (x ∈ L)) =
          ((List.finRange n).filter (fun x => decide (x ∈ L))).length := by
        rw [list_length_filter_eq_countP]
      rw [h1]
      have hnod := (List.nodup_finRange n).filter (fun x => decide (x ∈ L))
      have hsub2 : ∀ x ∈ (List.finRange n).filter (fun x => decide (x ∈ L)), x ∈ L := by
        intro x hx
        exact of_decide_eq_true (List.mem_filter.mp hx).2
      have h2 := list_nodup_subset_countP _ L hnod hsub2 (fun _ => true) (fun _ _ => rfl)
      rw [list_countP_eq_of_forall_true _ _ (fun _ _ => rfl)] at h2
      exact h2
    omega

theorem exists_of_countFin_ge_two {n : Nat} (P : Fin n → Bool) (h : 2 ≤ countFin n P) :
    ∃ a b : Fin n, a ≠ b ∧ P a = true ∧ P b = true := by
  have hlen : 2 ≤ ((List.finRange n).filter P).length := by
    rw [list_length_filter_eq_countP]; exact h
  have hnod : ((List.finRange n).filter P).Nodup := (List.nodup_finRange n).filter P
  cases hF : (List.finRange n).filter P with
  | nil => rw [hF] at hlen; simp at hlen
  | cons a rest =>
    cases rest with
    | nil => rw [hF] at hlen; simp at hlen
    | cons b tail =>
      rw [hF] at hnod
      rw [List.nodup_cons] at hnod
      have hab : a ≠ b := fun heq => hnod.1 (heq ▸ List.mem_cons_self ..)
      have ha : P a = true := (List.mem_filter.mp (hF ▸ List.mem_cons_self ..)).2
      have hb : P b = true :=
        (List.mem_filter.mp (hF ▸ List.mem_cons_of_mem a (List.mem_cons_self ..))).2
      exact ⟨a, b, hab, ha, hb⟩

theorem exists_of_countFin_eq_two {n : Nat} (P : Fin n → Bool) (h : countFin n P = 2) :
    ∃ a b : Fin n, a ≠ b ∧ (∀ x : Fin n, P x = true ↔ x = a ∨ x = b) := by
  have hlen : ((List.finRange n).filter P).length = 2 := by
    rw [list_length_filter_eq_countP]; exact h
  have hnod : ((List.finRange n).filter P).Nodup := (List.nodup_finRange n).filter P
  cases hF : (List.finRange n).filter P with
  | nil => rw [hF] at hlen; simp at hlen
  | cons a rest =>
    cases rest with
    | nil => rw [hF] at hlen; simp at hlen
    | cons b tail =>
      cases tail with
      | cons c _ => rw [hF] at hlen; simp at hlen
      | nil =>
        rw [hF] at hnod
        rw [List.nodup_cons] at hnod
        have hab : a ≠ b := fun heq => hnod.1 (heq ▸ List.mem_cons_self ..)
        refine ⟨a, b, hab, fun x => ?_⟩
        have hmem : x ∈ (List.finRange n).filter P ↔ P x = true := by
          simp [List.mem_filter, List.mem_finRange]
        rw [← hmem, hF]
        simp

/-! ## Section 2: Simple Graphs, Connectedness, Matchings, and Hamiltonian Paths -/

namespace SimpleGraph

variable {n : Nat}

def deg (G : SimpleGraph n) (u : Fin n) : Nat :=
  countFin n (fun v => G.adj u v)

def degComp (G : SimpleGraph n) (u : Fin n) : Nat :=
  countFin n (fun v => decide (u ≠ v) && !G.adj u v)

def edgeCount (G : SimpleGraph n) : Nat :=
  sumFin n (fun u => countFin n (fun v => decide (u.val < v.val) && G.adj u v))

theorem matching_two_mul_le (G : SimpleGraph n) (M : List (Fin n × Fin n))
    (hM : G.IsMatching M) : 2 * M.length ≤ n := by
  have hlen : (M.flatMap (fun e => [e.1, e.2])).length = 2 * M.length := by
    clear hM
    induction M with
    | nil => simp
    | cons e es ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, List.length_cons, List.length_nil, ih]
      simp only [List.length_cons]
      omega
  have hle := nodup_length_le_n (M.flatMap (fun e => [e.1, e.2])) hM.2
  omega

/-- The matching number `μ(G)` is the maximum cardinality of a matching of `G`. -/
private theorem matchingNumber_go_le (G : SimpleGraph n) :
    ∀ m, G.HasMatching (matchingNumberAux G m) ∧ ∀ k ≤ m, G.HasMatching k → k ≤ matchingNumberAux G m := by
  intro m
  induction m with
  | zero =>
    refine ⟨⟨[], ⟨by simp, by simp⟩, rfl⟩, fun k hk _ => by omega⟩
  | succ m ih =>
    unfold matchingNumberAux
    split
    · rename_i h
      exact ⟨h, fun k hk _ => hk⟩
    · rename_i h
      refine ⟨ih.1, fun k hk hMk => ?_⟩
      by_cases hkm : k = m + 1
      · subst hkm; exact absurd hMk h
      · exact ih.2 k (by omega) hMk

theorem matchingNumber_spec_aux (G : SimpleGraph n) :
    G.HasMatching G.matchingNumber ∧ ∀ M, G.IsMatching M → M.length ≤ G.matchingNumber := by
  have h := matchingNumber_go_le G n
  refine ⟨h.1, fun M hM => ?_⟩
  have hle : M.length ≤ n := by
    have := G.matching_two_mul_le M hM; omega
  exact h.2 M.length hle ⟨M, hM, rfl⟩

theorem two_mul_matchingNumber_le (G : SimpleGraph n) : 2 * G.matchingNumber ≤ n := by
  obtain ⟨⟨M, hM, hlen⟩, _⟩ := G.matchingNumber_spec_aux
  have := G.matching_two_mul_le M hM
  omega

/-! ### Basic Degree and Handshaking Identities -/

theorem deg_add_degComp (G : SimpleGraph n) (u : Fin n) :
    G.deg u + G.degComp u = n - 1 := by
  have h1 := countFin_add_not n (fun v => decide (u = v))
  have hsingle : countFin n (fun v => decide (u = v)) = 1 := by
    rw [countFin_eq n _ (fun v => decide (v = u)) (fun v => by
      by_cases h : u = v <;> simp [h, eq_comm])]
    exact countFin_single n u
  have hsplit := list_countP_add_split (List.finRange n)
    (fun v => !decide (u = v)) (fun v => G.adj u v)
  have hdeg : (List.finRange n).countP (fun v => !decide (u = v) && G.adj u v) = G.deg u := by
    unfold deg countFin
    apply list_countP_eq_of_eq
    intro v _
    by_cases h : u = v
    · subst h; simp [G.irrefl u]
    · simp [h]
  have hcomp : (List.finRange n).countP (fun v => !decide (u = v) && !G.adj u v) = G.degComp u := by
    unfold degComp countFin
    apply list_countP_eq_of_eq
    intro v _
    by_cases h : u = v <;> simp [h]
  have hne : (List.finRange n).countP (fun v => !decide (u = v)) = n - 1 := by
    unfold countFin at h1 hsingle
    omega
  omega

theorem deg_le (G : SimpleGraph n) (u : Fin n) : G.deg u ≤ n - 1 := by
  have := G.deg_add_degComp u; omega

theorem two_mul_edgeCount (G : SimpleGraph n) :
    2 * G.edgeCount = sumFin n (fun u => G.deg u) := by
  have hswap : G.edgeCount =
      sumFin n (fun u => countFin n (fun v => decide (v.val < u.val) && G.adj u v)) := by
    unfold edgeCount
    rw [sumFin_swap n (fun u v => decide (u.val < v.val) && G.adj u v)]
    apply sumFin_eq
    intro u
    apply countFin_eq
    intro v
    rw [G.symm v u]
  have hadd : G.edgeCount + G.edgeCount = sumFin n (fun u => G.deg u) := by
    conv => lhs; arg 2; rw [hswap]
    unfold edgeCount
    rw [← sumFin_add]
    apply sumFin_eq
    intro u
    have hsplit := list_countP_add_split (List.finRange n)
      (fun v => G.adj u v) (fun v => decide (u.val < v.val))
    have h1 : countFin n (fun v => decide (u.val < v.val) && G.adj u v) =
        (List.finRange n).countP (fun v => G.adj u v && decide (u.val < v.val)) := by
      unfold countFin; apply list_countP_eq_of_eq; intro v _; exact Bool.and_comm ..
    have h2 : countFin n (fun v => decide (v.val < u.val) && G.adj u v) =
        (List.finRange n).countP (fun v => G.adj u v && !decide (u.val < v.val)) := by
      unfold countFin; apply list_countP_eq_of_eq; intro v _
      by_cases huv : u = v
      · subst huv; simp [G.irrefl u]
      · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
        by_cases hlt : u.val < v.val
        · have hgt : ¬(v.val < u.val) := by omega
          simp [hlt, hgt]
        · have hgt : v.val < u.val := by omega
          simp [hlt, hgt]
    rw [h1, h2, hsplit]
    rfl
  omega

theorem two_mul_compEdgeCount (G : SimpleGraph n) :
    2 * G.compEdgeCount = sumFin n (fun u => G.degComp u) := by
  have hswap : G.compEdgeCount =
      sumFin n (fun u => countFin n (fun v => decide (v.val < u.val) && !G.adj u v)) := by
    unfold compEdgeCount
    rw [sumFin_swap n (fun u v => decide (u.val < v.val) && !G.adj u v)]
    apply sumFin_eq
    intro u
    apply countFin_eq
    intro v
    rw [G.symm v u]
  have hadd : G.compEdgeCount + G.compEdgeCount = sumFin n (fun u => G.degComp u) := by
    conv => lhs; arg 2; rw [hswap]
    unfold compEdgeCount
    rw [← sumFin_add]
    apply sumFin_eq
    intro u
    have hsplit := list_countP_add_split (List.finRange n)
      (fun v => decide (u ≠ v) && !G.adj u v) (fun v => decide (u.val < v.val))
    have h1 : countFin n (fun v => decide (u.val < v.val) && !G.adj u v) =
        (List.finRange n).countP (fun v => (decide (u ≠ v) && !G.adj u v) && decide (u.val < v.val)) := by
      unfold countFin; apply list_countP_eq_of_eq; intro v _
      by_cases hlt : u.val < v.val
      · have hne : u ≠ v := fun h => by subst h; omega
        simp [hlt, hne]
      · simp [hlt]
    have h2 : countFin n (fun v => decide (v.val < u.val) && !G.adj u v) =
        (List.finRange n).countP (fun v => (decide (u ≠ v) && !G.adj u v) && !decide (u.val < v.val)) := by
      unfold countFin; apply list_countP_eq_of_eq; intro v _
      by_cases huv : u = v
      · subst huv; simp
      · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
        by_cases hlt : u.val < v.val
        · have hgt : ¬(v.val < u.val) := by omega
          simp [hlt, hgt, huv]
        · have hgt : v.val < u.val := by omega
          simp [hlt, hgt, huv]
    rw [h1, h2, hsplit]
    rfl
  omega

theorem two_mul_edge_add_comp (G : SimpleGraph n) :
    2 * G.edgeCount + 2 * G.compEdgeCount = n * (n - 1) := by
  rw [G.two_mul_edgeCount, G.two_mul_compEdgeCount, ← sumFin_add]
  rw [sumFin_eq n _ (fun _ => n - 1) (fun u => G.deg_add_degComp u)]
  exact sumFin_const n (n - 1)

theorem pos_deg_of_connected (G : SimpleGraph n) (hn : 1 < n) (hconn : G.IsConnected)
    (u : Fin n) : 1 ≤ G.deg u := by
  -- Pick another vertex v ≠ u
  let v : Fin n := if u.val = 0 then ⟨1, hn⟩ else ⟨0, by omega⟩
  have huv : u ≠ v := by
    intro h
    by_cases hu : u.val = 0
    · have hv : u.val = 1 := by simpa [v, hu] using congrArg Fin.val h
      omega
    · have hv : u.val = 0 := by simpa [v, hu] using congrArg Fin.val h
      omega
  obtain ⟨l, hlen, hwalk, h0, hlast⟩ := hconn u v
  have hlen2 : 1 < l.length := by
    apply Classical.byContradiction; intro h
    have heq : l.length = 1 := by omega
    have hidx : l.length - 1 = 0 := by omega
    have : u = v := by
      rw [← h0, ← hlast]
      congr 1; exact hidx.symm
    exact huv this
  have hadj : G.adj l[0] l[1] = true := hwalk 0 hlen2
  rw [h0] at hadj
  have hpos : 0 < G.deg u := (countFin_pos_iff n _).mpr ⟨l[1], hadj⟩
  omega

/-- Two adjacent degree-1 vertices cannot exist in a connected graph with `n ≥ 3`. -/
theorem no_isolated_edge_of_connected (G : SimpleGraph n) (hn : 3 ≤ n) (hconn : G.IsConnected)
    (a b : Fin n) (hab : G.adj a b = true) (ha : G.deg a ≤ 1) (hb : G.deg b ≤ 1) : False := by
  -- There exists a third vertex c distinct from a and b
  have hcnt : countFin n (fun x => decide (x = a) || decide (x = b)) ≤ 2 := by
    have h1 : countFin n (fun x => decide (x = a) || decide (x = b)) ≤
        countFin n (fun x => decide (x = a)) + countFin n (fun x => decide (x = b)) := by
      unfold countFin
      induction List.finRange n with
      | nil => simp
      | cons x xs ih =>
        simp only [List.countP_cons]
        cases decide (x = a) <;> cases decide (x = b) <;> simp <;> omega
    rw [countFin_single, countFin_single] at h1
    omega
  have hnot := countFin_add_not n (fun x => decide (x = a) || decide (x = b))
  have hpos : 0 < countFin n (fun x => !(decide (x = a) || decide (x = b))) := by omega
  obtain ⟨c, hc⟩ := (countFin_pos_iff n _).mp hpos
  have hca : c ≠ a := by intro h; subst h; simp at hc
  have hcb : c ≠ b := by intro h; subst h; simp at hc
  -- Every neighbor of a must be b, and every neighbor of b must be a
  have hnbr_a : ∀ x : Fin n, G.adj a x = true → x = b := by
    intro x hax
    apply Classical.byContradiction; intro hxb
    have h2 : 2 ≤ G.deg a := by
      have hl : [b, x].Nodup := by simp [Ne.symm hxb]
      exact nodup_length_le_countFin [b, x] hl (fun v => G.adj a v) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hab
        · exact hax)
    omega
  have hnbr_b : ∀ x : Fin n, G.adj b x = true → x = a := by
    intro x hbx
    apply Classical.byContradiction; intro hxa
    have h2 : 2 ≤ G.deg b := by
      have hl : [a, x].Nodup := by simp [Ne.symm hxa]
      exact nodup_length_le_countFin [a, x] hl (fun v => G.adj b v) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · rw [G.symm]; exact hab
        · exact hbx)
    omega
  -- Walk from a to c stays forever in {a, b}
  obtain ⟨l, hlen, hwalk, h0, hlast⟩ := hconn a c
  have hstay : ∀ k (hk : k < l.length), l[k] = a ∨ l[k] = b := by
    intro k
    induction k with
    | zero => intro _; exact Or.inl h0
    | succ k ih =>
      intro hk
      have hk' : k < l.length := by omega
      have hadj := hwalk k hk
      rcases ih hk' with ha' | hb'
      · rw [ha'] at hadj; exact Or.inr (hnbr_a _ hadj)
      · rw [hb'] at hadj; exact Or.inl (hnbr_b _ hadj)
  rcases hstay (l.length - 1) (by omega) with h1 | h2
  · rw [hlast] at h1; exact hca h1
  · rw [hlast] at h2; exact hcb h2

/-! ### Adding an Edge -/

def addEdge (G : SimpleGraph n) (u v : Fin n) (huv : u ≠ v) : SimpleGraph n where
  adj x y := G.adj x y || (decide (x = u) && decide (y = v)) || (decide (x = v) && decide (y = u))
  irrefl x := by
    have h1 := G.irrefl x
    by_cases hxu : x = u
    · subst hxu; simp [h1, huv]
    · by_cases hxv : x = v
      · subst hxv; simp [h1, Ne.symm huv]
      · simp [h1, hxu, hxv]
  symm x y := by
    rw [G.symm x y]
    cases G.adj y x <;> by_cases hxu : x = u <;> by_cases hyv : y = v <;>
      by_cases hxv : x = v <;> by_cases hyu : y = u <;> simp_all

theorem addEdge_connected (G : SimpleGraph n) (u v : Fin n) (huv : u ≠ v)
    (hconn : G.IsConnected) : (G.addEdge u v huv).IsConnected := by
  intro a b
  obtain ⟨l, hlen, hwalk, h0, hlast⟩ := hconn a b
  refine ⟨l, hlen, ?_, h0, hlast⟩
  intro k hk
  simp [addEdge, hwalk k hk]

theorem addEdge_matchingNumber_le (G : SimpleGraph n) (u v : Fin n) (huv : u ≠ v) :
    G.matchingNumber ≤ (G.addEdge u v huv).matchingNumber := by
  obtain ⟨⟨M, hM, hlen⟩, _⟩ := G.matchingNumber_spec_aux
  have hM' : (G.addEdge u v huv).IsMatching M := by
    refine ⟨fun e he => ?_, hM.2⟩
    simp [addEdge, hM.1 e he]
  have := (G.addEdge u v huv).matchingNumber_spec_aux.2 M hM'
  omega

theorem addEdge_compEdgeCount_lt (G : SimpleGraph n) (u v : Fin n) (huv : u ≠ v)
    (hnon : G.adj u v = false) :
    (G.addEdge u v huv).compEdgeCount < G.compEdgeCount := by
  -- Use handshaking: 2 * compEdgeCount(G') + 2 = 2 * compEdgeCount(G)
  suffices h : 2 * (G.addEdge u v huv).compEdgeCount < 2 * G.compEdgeCount by omega
  rw [two_mul_compEdgeCount, two_mul_compEdgeCount]
  -- Every vertex has degComp(G') ≤ degComp(G), and u has strictly smaller degComp
  have hle : ∀ x : Fin n, (G.addEdge u v huv).degComp x ≤ G.degComp x := by
    intro x
    apply countFin_mono
    intro y hy
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hy ⊢
    refine ⟨hy.1, ?_⟩
    have h2 := hy.2
    simp only [addEdge, Bool.or_eq_false_iff] at h2
    exact h2.1.1
  have hlt_u : (G.addEdge u v huv).degComp u < G.degComp u := by
    -- In degComp u, v is counted in G but not in G'
    have hdiff : ∀ x : Fin n,
        (decide (u ≠ x) && !G.adj u x) =
        ((decide (u ≠ x) && !(G.addEdge u v huv).adj u x) || decide (x = v)) := by
      intro x
      by_cases hxv : x = v
      · subst hxv
        simp [addEdge, huv, hnon]
      · by_cases hxu : u = x
        · subst hxu; simp [hxv]
        · have hux : x ≠ u := Ne.symm hxu
          simp [addEdge, hxv, hxu, hux, huv]
    have hdisj : ∀ x ∈ List.finRange n,
        !((decide (u ≠ x) && !(G.addEdge u v huv).adj u x) && decide (x = v)) = true := by
      intro x _
      by_cases hxv : x = v
      · subst hxv; simp [addEdge, huv]
      · simp [hxv]
    have hsum : G.degComp u = (G.addEdge u v huv).degComp u + 1 := by
      have h1 : G.degComp u =
          countFin n (fun x => (decide (u ≠ x) && !(G.addEdge u v huv).adj u x) || decide (x = v)) :=
        countFin_eq n _ _ hdiff
      rw [h1]
      have hadd : ∀ l : List (Fin n),
          (∀ x ∈ l, !((decide (u ≠ x) && !(G.addEdge u v huv).adj u x) && decide (x = v)) = true) →
          l.countP (fun x => (decide (u ≠ x) && !(G.addEdge u v huv).adj u x) || decide (x = v)) =
          l.countP (fun x => decide (u ≠ x) && !(G.addEdge u v huv).adj u x) +
          l.countP (fun x => decide (x = v)) := by
        intro l hl
        induction l with
        | nil => simp
        | cons a as ih =>
          simp only [List.countP_cons]
          have ha := hl a (List.mem_cons_self ..)
          have has := ih (fun y hy => hl y (List.mem_cons_of_mem a hy))
          cases hA : (decide (u ≠ a) && !(G.addEdge u v huv).adj u a) <;>
            cases hB : decide (a = v) <;> simp_all <;> omega
      unfold degComp countFin
      rw [hadd (List.finRange n) hdisj]
      have hs := countFin_single n v
      unfold countFin at hs
      omega
    omega
  -- Sum over Fin n is strictly smaller because u ∈ finRange n has strictly smaller value
  have hstrict : ∀ (l : List (Fin n)) (f g : Fin n → Nat),
      (∀ x ∈ l, f x ≤ g x) → (∃ a ∈ l, f a < g a) → (l.map f).sum < (l.map g).sum := by
    intro l f g hle_l ⟨a, ha, hlt_a⟩
    induction l with
    | nil => simp at ha
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      cases ha with
      | head =>
        have hxs := list_sum_map_le xs f g (fun y hy => hle_l y (List.mem_cons_of_mem a hy))
        omega
      | tail _ hmem =>
        have hx := hle_l x (List.mem_cons_self ..)
        have hxs := ih (fun y hy => hle_l y (List.mem_cons_of_mem x hy)) hmem
        omega
  exact hstrict (List.finRange n) _ _ (fun x _ => hle x) ⟨u, List.mem_finRange u, hlt_u⟩

/-! ## Section 3: Base Cases `n = 2` and `n = 3` -/

theorem hamPath_of_n_eq_2 (G : SimpleGraph 2) (hconn : G.IsConnected) : G.HasHamiltonianPath := by
  have hd := G.pos_deg_of_connected (by omega) hconn ⟨0, Nat.zero_lt_two⟩
  have hpos : 0 < countFin 2 (fun v => G.adj ⟨0, Nat.zero_lt_two⟩ v) :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hd
  obtain ⟨v, hv⟩ := (countFin_pos_iff 2 _).mp hpos
  have hv1 : v = ⟨1, Nat.one_lt_two⟩ := by
    have hne : v ≠ ⟨0, Nat.zero_lt_two⟩ := by intro h; subst h; rw [G.irrefl] at hv; cases hv
    have hvlt : v.val < 2 := v.isLt
    have hvne : v.val ≠ 0 := fun h => hne (Fin.ext h)
    apply Fin.ext
    show v.val = 1
    omega
  subst hv1
  refine ⟨[⟨0, Nat.zero_lt_two⟩, ⟨1, Nat.one_lt_two⟩], rfl, by decide, ?_⟩
  intro k hk
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  exact hv

theorem hamPath_of_n_eq_3 (G : SimpleGraph 3) (hconn : G.IsConnected) : G.HasHamiltonianPath := by
  -- Every vertex has degree ≥ 1, sum of degrees is even, so sum ≥ 4, hence some vertex has degree 2!
  have hd0 := G.pos_deg_of_connected (by omega) hconn ⟨0, by omega⟩
  have hd1 := G.pos_deg_of_connected (by omega) hconn ⟨1, by omega⟩
  have hd2 := G.pos_deg_of_connected (by omega) hconn ⟨2, by omega⟩
  have hsum := G.two_mul_edgeCount
  have hsum_exp : sumFin 3 (fun u => G.deg u) =
      G.deg ⟨0, by omega⟩ + G.deg ⟨1, by omega⟩ + G.deg ⟨2, by omega⟩ := by
    unfold sumFin
    have hfr : List.finRange 3 = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
    rw [hfr]; simp; omega
  have hge4 : 4 ≤ G.deg ⟨0, by omega⟩ + G.deg ⟨1, by omega⟩ + G.deg ⟨2, by omega⟩ := by omega
  have hdeg2 : ∃ b : Fin 3, G.deg b = 2 := by
    have h0 := G.deg_le ⟨0, by omega⟩
    have h1 := G.deg_le ⟨1, by omega⟩
    have h2 := G.deg_le ⟨2, by omega⟩
    by_cases e0 : G.deg ⟨0, by omega⟩ = 2
    · exact ⟨⟨0, by omega⟩, e0⟩
    · by_cases e1 : G.deg ⟨1, by omega⟩ = 2
      · exact ⟨⟨1, by omega⟩, e1⟩
      · exact ⟨⟨2, by omega⟩, by omega⟩
  obtain ⟨b, hb⟩ := hdeg2
  -- b is adjacent to both other vertices
  have hcompl := G.deg_add_degComp b
  have hcomp0 : G.degComp b = 0 := by omega
  have hall : ∀ x : Fin 3, x ≠ b → G.adj b x = true := by
    intro x hxb
    have h0 := (countFin_eq_zero_iff 3 _).mp hcomp0 x
    simp [Ne.symm hxb] at h0
    exact h0
  -- Find the other two vertices a, c
  have hne_cnt : countFin 3 (fun x => !decide (x = b)) = 2 := by
    have h1 := countFin_add_not 3 (fun x => decide (x = b))
    have h2 := countFin_single 3 b
    omega
  obtain ⟨a, c, hac, hspec⟩ := exists_of_countFin_eq_two _ hne_cnt
  have hab : a ≠ b := by
    have := (hspec a).mpr (Or.inl rfl); simp at this; exact this
  have hcb : c ≠ b := by
    have := (hspec c).mpr (Or.inr rfl); simp at this; exact this
  refine ⟨[a, b, c], rfl, ?_, ?_⟩
  · simp [hab, hac, Ne.symm hcb]
  · intro k hk
    have hk' : k = 0 ∨ k = 1 := by simp at hk; omega
    rcases hk' with rfl | rfl
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [G.symm]; exact hall a hab
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      exact hall c hcb

/-! ## Section 4: Universal-Vertex Extension `G+` and Pósa/Chvátal Extremal Lemma -/

/-- The universal-vertex extension `G+ = G + v*` on `Fin (n + 1)`, where `v* = ⟨n, _⟩`. -/
def adjPlus (G : SimpleGraph n) (x y : Fin (n + 1)) : Bool :=
  if x = y then false
  else if hx : x.val < n then
    if hy : y.val < n then G.adj ⟨x.val, hx⟩ ⟨y.val, hy⟩ else true
  else true

theorem adjPlus_irrefl (G : SimpleGraph n) (x : Fin (n + 1)) : G.adjPlus x x = false := by
  simp [adjPlus]

theorem adjPlus_symm (G : SimpleGraph n) (x y : Fin (n + 1)) : G.adjPlus x y = G.adjPlus y x := by
  unfold adjPlus
  by_cases hxy : x = y
  · subst hxy; simp
  · have hyx : y ≠ x := Ne.symm hxy
    simp only [hxy, hyx, ↓reduceIte]
    by_cases hx : x.val < n <;> by_cases hy : y.val < n <;> simp [hx, hy, G.symm]

def emb (x : Fin n) : Fin (n + 1) := ⟨x.val, by omega⟩

theorem emb_inj {x y : Fin n} (h : emb x = emb y) : x = y :=
  Fin.ext (by simpa [emb] using congrArg Fin.val h)

theorem adjPlus_emb (G : SimpleGraph n) (x y : Fin n) :
    G.adjPlus (emb x) (emb y) = G.adj x y := by
  unfold adjPlus emb
  by_cases h : (⟨x.val, by omega⟩ : Fin (n + 1)) = ⟨y.val, by omega⟩
  · have hxy : x = y := Fin.ext (by simpa using congrArg Fin.val h)
    subst hxy; simp [G.irrefl]
  · simp [h, x.isLt, y.isLt]

theorem adjPlus_star_right (G : SimpleGraph n) (x : Fin n) :
    G.adjPlus (emb x) ⟨n, by omega⟩ = true := by
  unfold adjPlus emb
  have hne : (⟨x.val, by omega⟩ : Fin (n + 1)) ≠ ⟨n, by omega⟩ := by
    intro h
    have hv : x.val = n := by simpa using congrArg Fin.val h
    have := x.isLt; omega
  simp [hne, x.isLt]

theorem adjPlus_star_left (G : SimpleGraph n) (x : Fin n) :
    G.adjPlus ⟨n, by omega⟩ (emb x) = true := by
  rw [adjPlus_symm]; exact adjPlus_star_right G x

/-- If `G + uv` has a Hamiltonian path while `G` does not, then `G+` has a Hamiltonian path
    from `emb u` to `emb v`. -/
theorem exists_hamPath_plus (G : SimpleGraph n) (u v : Fin n) (huv : u ≠ v)
    (hno : ¬ G.HasHamiltonianPath)
    (hplus : (G.addEdge u v huv).HasHamiltonianPath) :
    ∃ (Q : List (Fin (n + 1))) (hQlen : Q.length = n + 1),
      Q.Nodup ∧
      Q[0]'(by omega) = emb u ∧ Q[n]'(by omega) = emb v ∧
      ∀ (k : Nat) (hk : k + 1 < Q.length), G.adjPlus Q[k] Q[k + 1] = true := by
  obtain ⟨p, hplen, hpnodup, hpwalk⟩ := hplus
  -- p cannot be a walk in G, so some consecutive pair in p is {u, v}
  have hex : ∃ k, ∃ (hk : k + 1 < p.length), G.adj p[k] p[k + 1] = false := by
    apply Classical.byContradiction; intro hall
    apply hno
    refine ⟨p, hplen, hpnodup, fun k hk => ?_⟩
    cases h : G.adj p[k] p[k + 1]
    · exact absurd ⟨k, hk, h⟩ hall
    · rfl
  obtain ⟨k, hk, hkf⟩ := hex
  have hpair : (p[k] = u ∧ p[k + 1] = v) ∨ (p[k] = v ∧ p[k + 1] = u) := by
    have hadj := hpwalk k hk
    simp only [addEdge, hkf, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hadj
    exact hadj
  -- Ensure p' has p'[k'] = u and p'[k' + 1] = v (reverse p if needed)
  have hgood : ∃ (p' : List (Fin n)) (m : Nat) (hp'len : p'.length = n) (hm : m + 1 < n),
      p'.Nodup ∧ (G.addEdge u v huv).IsWalk p' ∧
      p'[m]'(by omega) = u ∧ p'[m + 1]'(by omega) = v := by
    rcases hpair with ⟨hku, hkv⟩ | ⟨hkv, hku⟩
    · exact ⟨p, k, hplen, by omega, hpnodup, hpwalk, hku, hkv⟩
    · refine ⟨p.reverse, n - 2 - k, by simp [hplen], by omega, list_nodup_reverse hpnodup, ?_, ?_, ?_⟩
      · intro j hj
        rw [List.length_reverse] at hj
        simp only [List.getElem_reverse]
        rw [(G.addEdge u v huv).symm]
        have hidx : p.length - 1 - (j + 1) + 1 = p.length - 1 - j := by omega
        have hstep := hpwalk (p.length - 1 - (j + 1)) (by omega)
        simpa [hidx] using hstep
      · simp only [List.getElem_reverse]
        have hidx : p.length - 1 - (n - 2 - k) = k + 1 := by omega
        simpa [hidx] using hku
      · simp only [List.getElem_reverse]
        have hidx : p.length - 1 - (n - 2 - k + 1) = k := by omega
        simpa [hidx] using hkv
  obtain ⟨p', m, hp'len, hm, hp'nodup, hp'walk, hpm, hpm1⟩ := hgood
  -- Every consecutive edge in p' EXCEPT index m is an edge of G!
  have hother : ∀ j (hj : j + 1 < n), j ≠ m → G.adj (p'[j]'(by omega)) (p'[j + 1]'(by omega)) = true := by
    intro j hj hjm
    have hadj := hp'walk j (by omega)
    cases h : G.adj (p'[j]'(by omega)) (p'[j + 1]'(by omega))
    · simp only [addEdge, h, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hadj
      rcases hadj with ⟨hju, hjv⟩ | ⟨hjv, hju⟩
      · have heq := nodup_getElem_inj hp'nodup (by omega) (by omega) (hju.trans hpm.symm)
        exact absurd heq hjm
      · have heq1 := nodup_getElem_inj hp'nodup (by omega) (by omega) (hjv.trans hpm1.symm)
        have heq2 := nodup_getElem_inj hp'nodup (by omega) (by omega) (hju.trans hpm.symm)
        omega
    · rfl
  -- Split p' at m + 1: L = p'.take (m + 1) (ends at u), R = p'.drop (m + 1) (starts at v)
  let L := p'.take (m + 1)
  let R := p'.drop (m + 1)
  let star : Fin (n + 1) := ⟨n, by omega⟩
  let Q : List (Fin (n + 1)) := (L.reverse.map emb) ++ [star] ++ (R.reverse.map emb)
  have hLlen : L.length = m + 1 := by simp [L, hp'len]; omega
  have hRlen : R.length = n - (m + 1) := by simp [R, hp'len]
  have hQlen : Q.length = n + 1 := by
    simp [Q, hLlen, hRlen]; omega
  have hLR : L ++ R = p' := List.take_append_drop (m + 1) p'
  have hLR_nodup : (L.reverse ++ R.reverse).Nodup := by
    have hdisj : ∀ x ∈ L, x ∉ R := by
      intro x hxL hxR
      have hp_nd : (L ++ R).Nodup := hLR ▸ hp'nodup
      exact (List.nodup_append.mp hp_nd).2.2 x hxL x hxR rfl
    have hLnd : L.Nodup := (List.nodup_append.mp (hLR ▸ hp'nodup)).1
    have hRnd : R.Nodup := (List.nodup_append.mp (hLR ▸ hp'nodup)).2.1
    rw [List.nodup_append]
    refine ⟨list_nodup_reverse hLnd, list_nodup_reverse hRnd, fun x hx y hy hxy => ?_⟩
    subst hxy
    exact hdisj x (List.mem_reverse.mp hx) (List.mem_reverse.mp hy)
  have hQnodup : Q.Nodup := by
    have hmap_nd : ((L.reverse ++ R.reverse).map emb).Nodup :=
      list_nodup_map_inj_on emb hLR_nodup (fun _ _ _ _ h => emb_inj h)
    have hstar_not : ∀ x ∈ (L.reverse ++ R.reverse).map emb, x ≠ star := by
      intro x hx heq
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      have := congrArg Fin.val heq
      simp [emb, star] at this
      omega
    rw [List.map_append] at hmap_nd hstar_not
    obtain ⟨h1, h2, h12⟩ := List.nodup_append.mp hmap_nd
    simp only [Q, List.append_assoc, List.singleton_append]
    rw [List.nodup_append]
    refine ⟨h1, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨fun hmem => hstar_not star (List.mem_append.mpr (Or.inr hmem)) rfl, h2⟩
    · intro x hx y hy hxy
      subst hxy
      cases hy with
      | head => exact hstar_not star (List.mem_append.mpr (Or.inl hx)) rfl
      | tail _ h => exact h12 x hx x h rfl
  have hQ0 : Q[0]'(by omega) = emb u := by
    have hpos : 0 < (L.reverse.map emb).length := by simp [hLlen]
    have h1 : Q[0]'(by omega) = (L.reverse.map emb)[0]'hpos := by
      simp only [Q, List.append_assoc]
      rw [List.getElem_append_left hpos]
    rw [h1, List.getElem_map, List.getElem_reverse]
    have hLtake : L[L.length - 1 - 0]'(by omega) = p'[m]'(by omega) := by
      have hi : L.length - 1 - 0 = m := by omega
      simp only [hi, L, List.getElem_take]
    rw [hLtake, hpm]
  have hQn : Q[n]'(by omega) = emb v := by
    have h1len : (L.reverse.map emb ++ [star]).length = m + 2 := by simp [hLlen]
    have hge : (L.reverse.map emb ++ [star]).length ≤ n := by omega
    have h1 : Q[n]'(by omega) = (R.reverse.map emb)[n - (m + 2)]'(by simp [hRlen]; omega) := by
      simp only [Q]
      rw [List.getElem_append_right hge]
      congr 1; omega
    rw [h1, List.getElem_map, List.getElem_reverse]
    have hRdrop : R[R.length - 1 - (n - (m + 2))]'(by omega) = p'[m + 1]'(by omega) := by
      have hi : R.length - 1 - (n - (m + 2)) = 0 := by omega
      simp only [hi, R, List.getElem_drop, Nat.add_zero]
    rw [hRdrop, hpm1]
  refine ⟨Q, hQlen, hQnodup, hQ0, hQn, ?_⟩
  intro j hj
  by_cases h1 : j + 1 < m + 1
  · have hleft1 : j < (L.reverse.map emb).length := by simp [hLlen]; omega
    have hleft2 : j + 1 < (L.reverse.map emb).length := by simp [hLlen]; omega
    have hQj : Q[j]'(by omega) = emb (p'[m - j]'(by omega)) := by
      simp only [Q, List.append_assoc]
      rw [List.getElem_append_left hleft1, List.getElem_map, List.getElem_reverse]
      have hLtake : L[L.length - 1 - j]'(by omega) = p'[m - j]'(by omega) := by
        have hi : L.length - 1 - j = m - j := by omega
        simp only [hi, L, List.getElem_take]
      rw [hLtake]
    have hQj1 : Q[j + 1]'(by omega) = emb (p'[m - (j + 1)]'(by omega)) := by
      simp only [Q, List.append_assoc]
      rw [List.getElem_append_left hleft2, List.getElem_map, List.getElem_reverse]
      have hLtake : L[L.length - 1 - (j + 1)]'(by omega) = p'[m - (j + 1)]'(by omega) := by
        have hi : L.length - 1 - (j + 1) = m - (j + 1) := by omega
        simp only [hi, L, List.getElem_take]
      rw [hLtake]
    rw [hQj, hQj1, adjPlus_emb, G.symm]
    have hidx : m - (j + 1) + 1 = m - j := by omega
    have hstep := hother (m - (j + 1)) (by omega) (by omega)
    simpa [hidx] using hstep
  · by_cases h2 : j = m
    · subst j
      have hleft : m < (L.reverse.map emb).length := by simp [hLlen]
      have hQm : Q[m]'(by omega) = emb (p'[0]'(by omega)) := by
        simp only [Q, List.append_assoc]
        rw [List.getElem_append_left hleft, List.getElem_map, List.getElem_reverse]
        have hLtake : L[L.length - 1 - m]'(by omega) = p'[0]'(by omega) := by
          have hi : L.length - 1 - m = 0 := by omega
          simp only [hi, L, List.getElem_take]
        rw [hLtake]
      have hQm1 : Q[m + 1]'(by omega) = star := by
        simp only [Q, List.append_assoc]
        rw [List.getElem_append_right (by simp [hLlen])]
        have hsub : m + 1 - (L.reverse.map emb).length = 0 := by simp [hLlen]
        simp only [hsub, List.singleton_append, List.getElem_cons_zero]
      rw [hQm, hQm1]
      exact adjPlus_star_right G _
    · by_cases h3 : j = m + 1
      · subst j
        have hQm1 : Q[m + 1]'(by omega) = star := by
          simp only [Q, List.append_assoc]
          rw [List.getElem_append_right (by simp [hLlen])]
          have hsub : m + 1 - (L.reverse.map emb).length = 0 := by simp [hLlen]
          simp only [hsub, List.singleton_append, List.getElem_cons_zero]
        have h1len : (L.reverse.map emb ++ [star]).length = m + 2 := by simp [hLlen]
        have hQm2 : Q[m + 2]'(by omega) = emb (p'[n - 1]'(by omega)) := by
          simp only [Q]
          rw [List.getElem_append_right (by omega)]
          have hsub : m + 2 - (L.reverse.map emb ++ [star]).length = 0 := by omega
          simp only [hsub, List.getElem_map, List.getElem_reverse]
          have hRdrop : R[R.length - 1 - 0]'(by omega) = p'[n - 1]'(by omega) := by
            have hi : R.length - 1 - 0 = n - m - 2 := by omega
            simp only [hi, R, List.getElem_drop]
            congr 1; omega
          rw [hRdrop]
        rw [hQm1, hQm2]
        exact adjPlus_star_left G _
      · have h1len : (L.reverse.map emb ++ [star]).length = m + 2 := by simp [hLlen]
        have hQj : Q[j]'(by omega) = emb (p'[n + m + 1 - j]'(by omega)) := by
          simp only [Q]
          rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_reverse]
          have hRdrop : R[R.length - 1 - (j - (L.reverse.map emb ++ [star]).length)]'(by omega) =
              p'[n + m + 1 - j]'(by omega) := by
            have hi : R.length - 1 - (j - (L.reverse.map emb ++ [star]).length) = n - j := by omega
            simp only [hi, R, List.getElem_drop]
            congr 1; omega
          rw [hRdrop]
        have hQj1 : Q[j + 1]'(by omega) = emb (p'[n + m - j]'(by omega)) := by
          simp only [Q]
          rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_reverse]
          have hRdrop : R[R.length - 1 - (j + 1 - (L.reverse.map emb ++ [star]).length)]'(by omega) =
              p'[n + m - j]'(by omega) := by
            have hi : R.length - 1 - (j + 1 - (L.reverse.map emb ++ [star]).length) = n - (j + 1) := by omega
            simp only [hi, R, List.getElem_drop]
            congr 1; omega
          rw [hRdrop]
        rw [hQj, hQj1, adjPlus_emb, G.symm]
        have hidx : n + m - j + 1 = n + m + 1 - j := by omega
        have hstep := hother (n + m - j) (by omega) (by omega)
        simpa [hidx] using hstep

/-- Pósa/Ore flip: a Hamiltonian path `Q` of `G+` from `u` to `v` cannot have an index `k < n`
    with `Q[k]` adjacent to `v` and `Q[k+1]` adjacent to `u`, else `G` has a Hamiltonian path. -/
theorem no_posa_flip (G : SimpleGraph n) (Q : List (Fin (n + 1)))
    (hQlen : Q.length = n + 1) (hQnodup : Q.Nodup)
    (hQwalk : ∀ (j : Nat) (hj : j + 1 < Q.length), G.adjPlus Q[j] Q[j + 1] = true)
    (hno : ¬ G.HasHamiltonianPath)
    (k : Nat) (hk : k < n)
    (hv : G.adjPlus Q[k] Q[n] = true)
    (hu : G.adjPlus Q[0] Q[k + 1] = true) : False := by
  -- Form Hamiltonian cycle C = Q.take (k+1) ++ (Q.drop (k+1)).reverse of G+
  let A := Q.take (k + 1)
  let B := Q.drop (k + 1)
  let C := A ++ B.reverse
  have hAlen : A.length = k + 1 := by simp [A, hQlen]; omega
  have hBlen : B.length = n - k := by simp [B, hQlen]
  have hClen : C.length = n + 1 := by simp [C, hAlen, hBlen]; omega
  have hAB : A ++ B = Q := List.take_append_drop (k + 1) Q
  have hCnodup : C.Nodup := by
    have hQnd := hAB ▸ hQnodup
    obtain ⟨hAnd, hBnd, hdisj⟩ := List.nodup_append.mp hQnd
    rw [List.nodup_append]
    refine ⟨hAnd, list_nodup_reverse hBnd, fun x hx y hy hxy => hdisj x hx y (List.mem_reverse.mp hy) hxy⟩
  -- Check adjacency of consecutive elements in C
  have hCwalk : ∀ (j : Nat) (hj : j + 1 < C.length), G.adjPlus C[j] C[j + 1] = true := by
    intro j hj
    by_cases h1 : j + 1 < k + 1
    · have hjA : j < A.length := by omega
      have hj1A : j + 1 < A.length := by omega
      simp only [C, List.getElem_append_left hjA, List.getElem_append_left hj1A, A, List.getElem_take]
      exact hQwalk j (by omega)
    · by_cases h2 : j = k
      · subst j
        have hjA : k < A.length := by omega
        have hCj : C[k]'(by omega) = Q[k]'(by omega) := by
          simp only [C, List.getElem_append_left hjA, A, List.getElem_take]
        have hCj1 : C[k + 1]'(by omega) = Q[n]'(by omega) := by
          simp only [C, List.getElem_append_right (by omega : A.length ≤ k + 1),
            List.getElem_reverse, B, List.getElem_drop]
          congr 1; simp [hAlen]; omega
        rw [hCj, hCj1]; exact hv
      · -- Both j and j + 1 are in B.reverse
        have hCj : C[j]'(by omega) = Q[n + k + 1 - j]'(by omega) := by
          simp only [C, List.getElem_append_right (by omega : A.length ≤ j),
            List.getElem_reverse, B, List.getElem_drop]
          congr 1; simp [hAlen]; omega
        have hCj1 : C[j + 1]'(by omega) = Q[n + k - j]'(by omega) := by
          simp only [C, List.getElem_append_right (by omega : A.length ≤ j + 1),
            List.getElem_reverse, B, List.getElem_drop]
          congr 1; simp [hAlen]; omega
        rw [hCj, hCj1, adjPlus_symm]
        have hidx : n + k - j + 1 = n + k + 1 - j := by omega
        have hstep := hQwalk (n + k - j) (by omega)
        simpa [hidx] using hstep
  have hCwrap : G.adjPlus (C[n]'(by omega)) (C[0]'(by omega)) = true := by
    have hC0 : C[0]'(by omega) = Q[0]'(by omega) := by
      simp only [C, List.getElem_append_left (by omega : 0 < A.length), A, List.getElem_take]
    have hCn : C[n]'(by omega) = Q[k + 1]'(by omega) := by
      simp only [C, List.getElem_append_right (by omega : A.length ≤ n),
        List.getElem_reverse, B, List.getElem_drop]
      congr 1; simp [hAlen]; omega
    rw [hC0, hCn, adjPlus_symm]; exact hu
  -- star = ⟨n, _⟩ must appear in C (since C has n+1 distinct elements of Fin (n+1))
  let star : Fin (n + 1) := ⟨n, by omega⟩
  have hstar_mem : star ∈ C := by
    apply Classical.byContradiction; intro hnot
    have hle := nodup_length_le_countFin C hCnodup (fun x => !decide (x = star)) (fun x hx => by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro h; subst h; exact hnot hx)
    have h1 := countFin_add_not (n + 1) (fun x => decide (x = star))
    have h2 := countFin_single (n + 1) star
    omega
  obtain ⟨r, hr, hCr⟩ := List.getElem_of_mem hstar_mem
  -- Delete star at index r and rotate: Rlist = C.drop (r+1) ++ C.take r
  let Rlist := C.drop (r + 1) ++ C.take r
  have hRlen : Rlist.length = n := by simp [Rlist, hClen]; omega
  -- Every element of Rlist is ≠ star, hence has val < n
  have hRnot_star : ∀ x ∈ Rlist, x.val < n := by
    intro x hx
    have hne : x ≠ star := by
      intro heq; subst heq
      rw [List.mem_append] at hx
      rcases hx with h1 | h2
      · obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem h1
        rw [List.length_drop] at hj
        rw [List.getElem_drop] at hxj
        have hinj := nodup_getElem_inj hCnodup (by omega) hr (hxj.trans hCr.symm)
        omega
      · obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem h2
        rw [List.length_take] at hj
        rw [List.getElem_take] at hxj
        have hinj := nodup_getElem_inj hCnodup (by omega) hr (hxj.trans hCr.symm)
        omega
    have := x.isLt
    have hvn : x.val ≠ n := fun h => hne (Fin.ext h)
    omega
  have hRnodup : Rlist.Nodup := by
    have hCeq : C = C.take r ++ C[r] :: C.drop (r + 1) := by
      have h1 := List.take_append_drop r C
      have h2 : C.drop r = C[r] :: C.drop (r + 1) := List.drop_eq_getElem_cons hr
      rw [← h2]; exact h1.symm
    have hCnd := hCeq ▸ hCnodup
    obtain ⟨h1, h2, h12⟩ := List.nodup_append.mp hCnd
    rw [List.nodup_cons] at h2
    rw [List.nodup_append]
    exact ⟨h2.2, h1, fun x hx y hy hxy => h12 y hy x (List.mem_cons_of_mem _ hx) hxy.symm⟩
  -- Every consecutive pair in Rlist is adjacent in G+
  have hRwalk : ∀ (j : Nat) (hj : j + 1 < Rlist.length), G.adjPlus Rlist[j] Rlist[j + 1] = true := by
    intro j hj
    have hdlen : (C.drop (r + 1)).length = n - r := by simp [hClen]
    by_cases h1 : j + 1 < n - r
    · simp only [Rlist, List.getElem_append_left (by omega : j < (C.drop (r + 1)).length),
        List.getElem_append_left (by omega : j + 1 < (C.drop (r + 1)).length), List.getElem_drop]
      have hidx : r + 1 + (j + 1) = (r + 1 + j) + 1 := by omega
      simpa [hidx] using hCwalk (r + 1 + j) (by omega)
    · by_cases h2 : j + 1 = n - r
      · have hRj : Rlist[j]'(by omega) = C[n]'(by omega) := by
          simp only [Rlist, List.getElem_append_left (by omega : j < (C.drop (r + 1)).length),
            List.getElem_drop]
          congr 1; omega
        have hRj1 : Rlist[j + 1]'(by omega) = C[0]'(by omega) := by
          simp only [Rlist, List.getElem_append_right (by omega : (C.drop (r + 1)).length ≤ j + 1),
            List.getElem_take]
          congr 1; omega
        rw [hRj, hRj1]; exact hCwrap
      · simp only [Rlist, List.getElem_append_right (by omega : (C.drop (r + 1)).length ≤ j),
          List.getElem_append_right (by omega : (C.drop (r + 1)).length ≤ j + 1), List.getElem_take]
        have hidx : j + 1 - (C.drop (r + 1)).length = (j - (C.drop (r + 1)).length) + 1 := by omega
        have hstep := hCwalk (j - (C.drop (r + 1)).length) (by omega)
        have heq1 : C[j + 1 - (C.drop (r + 1)).length]'(by omega) =
            C[(j - (C.drop (r + 1)).length) + 1]'(by omega) := by congr 1
        rw [heq1]; exact hstep
  -- Project Rlist down to List (Fin n)
  let proj : Fin (n + 1) → Fin n := fun x =>
    if hx : x.val < n then ⟨x.val, hx⟩ else ⟨0, by omega⟩
  let P := Rlist.map proj
  apply hno
  refine ⟨P, by simp [P, hRlen], ?_, ?_⟩
  · -- P.Nodup
    exact list_nodup_map_inj_on proj hRnodup (fun x hx y hy hxy => by
      have hxl := hRnot_star x hx
      have hyl := hRnot_star y hy
      have hval : x.val = y.val := by simpa [proj, hxl, hyl] using congrArg Fin.val hxy
      exact Fin.ext hval)
  · -- G.IsWalk P
    intro j hj
    simp only [P, List.length_map] at hj
    simp only [P, List.getElem_map]
    have hx := hRnot_star (Rlist[j]'(by omega)) (List.getElem_mem ..)
    have hy := hRnot_star (Rlist[j + 1]'hj) (List.getElem_mem ..)
    have hadj := hRwalk j hj
    have heq1 : emb (proj (Rlist[j]'(by omega))) = Rlist[j]'(by omega) := by
      apply Fin.ext; simp [emb, proj, hx]
    have heq2 : emb (proj (Rlist[j + 1]'hj)) = Rlist[j + 1]'hj := by
      apply Fin.ext; simp [emb, proj, hy]
    rw [← adjPlus_emb, heq1, heq2]
    exact hadj

/-- Chvátal's Extremal Lemma for maximal non-traceable connected graphs on `n ≥ 4` vertices. -/
theorem chvatal_extremal (G : SimpleGraph n) (hn : 4 ≤ n) (hconn : G.IsConnected)
    (hno : ¬ G.HasHamiltonianPath)
    (hmax : ∀ u v : Fin n, (huv : u ≠ v) → G.adj u v = false → (G.addEdge u v huv).HasHamiltonianPath) :
    ∃ i : Nat, 2 ≤ i ∧ 2 * i ≤ n ∧
      i ≤ countFin n (fun x => decide (G.deg x ≤ i - 1)) ∧
      n + 1 - i ≤ countFin n (fun x => decide (G.deg x ≤ n - 1 - i)) := by
  -- G is not complete (a complete graph has Hamiltonian path finRange n)
  have hex_non : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ G.adj p.1 p.2 = false := by
    apply Classical.byContradiction; intro hall
    apply hno
    refine ⟨List.finRange n, List.length_finRange, List.nodup_finRange n, fun k hk => ?_⟩
    rw [List.length_finRange] at hk
    have hne : (List.finRange n)[k]'(by omega) ≠ (List.finRange n)[k + 1]'(by omega) := by
      intro heq
      have hval : k = k + 1 := by simpa [List.getElem_finRange] using congrArg Fin.val heq
      omega
    cases h : G.adj ((List.finRange n)[k]'(by omega)) ((List.finRange n)[k + 1]'(by omega))
    · exact absurd ⟨(_, _), hne, h⟩ hall
    · rfl
  -- Pick a non-edge (u, v) maximizing deg u + deg v
  let allPairs : List (Fin n × Fin n) :=
    (List.finRange n).flatMap (fun a => (List.finRange n).map (fun b => (a, b)))
  let nonEdges := allPairs.filter (fun p => decide (p.1 ≠ p.2) && !G.adj p.1 p.2)
  have hne_nonempty : nonEdges ≠ [] := by
    obtain ⟨p, hne, hadj⟩ := hex_non
    have hmem : p ∈ nonEdges := by
      rw [List.mem_filter]
      refine ⟨?_, by simp [hne, hadj]⟩
      rw [List.mem_flatMap]
      exact ⟨p.1, List.mem_finRange _, List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩⟩
    intro hemp; rw [hemp] at hmem; simp at hmem
  -- Find maximum element of a nonempty list under a Nat score
  have hmax_list : ∀ (l : List (Fin n × Fin n)) (score : Fin n × Fin n → Nat),
      l ≠ [] → ∃ m ∈ l, ∀ p ∈ l, score p ≤ score m := by
    intro l score hl
    induction l with
    | nil => exact absurd rfl hl
    | cons x xs ih =>
      cases xs with
      | nil => exact ⟨x, List.mem_cons_self .., fun p hp => by simp at hp; subst hp; omega⟩
      | cons y ys =>
        obtain ⟨m, hm, hmax_m⟩ := ih (by simp)
        by_cases hxm : score m ≤ score x
        · refine ⟨x, List.mem_cons_self .., fun p hp => ?_⟩
          cases hp with
          | head => omega
          | tail _ h => have := hmax_m p h; omega
        · refine ⟨m, List.mem_cons_of_mem x hm, fun p hp => ?_⟩
          cases hp with
          | head => omega
          | tail _ h => exact hmax_m p h
  obtain ⟨⟨u0, v0⟩, huv0_mem, huv0_max⟩ :=
    hmax_list nonEdges (fun p => G.deg p.1 + G.deg p.2) hne_nonempty
  have huv0_prop : u0 ≠ v0 ∧ G.adj u0 v0 = false := by
    have := (List.mem_filter.mp huv0_mem).2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact this
  have hmax_all : ∀ a b : Fin n, a ≠ b → G.adj a b = false →
      G.deg a + G.deg b ≤ G.deg u0 + G.deg v0 := by
    intro a b hab hnon
    have hmem : (a, b) ∈ nonEdges := by
      rw [List.mem_filter]
      refine ⟨?_, by simp [hab, hnon]⟩
      rw [List.mem_flatMap]
      exact ⟨a, List.mem_finRange _, List.mem_map.mpr ⟨b, List.mem_finRange _, rfl⟩⟩
    exact huv0_max (a, b) hmem
  -- Orient (u, v) so deg u ≤ deg v
  let u := if G.deg u0 ≤ G.deg v0 then u0 else v0
  let v := if G.deg u0 ≤ G.deg v0 then v0 else u0
  have huv : u ≠ v := by
    by_cases h : G.deg u0 ≤ G.deg v0 <;> simp [u, v, h, huv0_prop.1, Ne.symm huv0_prop.1]
  have huv_non : G.adj u v = false := by
    by_cases h : G.deg u0 ≤ G.deg v0
    · simp [u, v, h, huv0_prop.2]
    · simp [u, v, h, G.symm, huv0_prop.2]
  have hdeg_le : G.deg u ≤ G.deg v := by
    by_cases h : G.deg u0 ≤ G.deg v0 <;> simp [u, v, h] <;> omega
  have huv_max : ∀ a b : Fin n, a ≠ b → G.adj a b = false → G.deg a + G.deg b ≤ G.deg u + G.deg v := by
    intro a b hab hnon
    have := hmax_all a b hab hnon
    by_cases h : G.deg u0 ≤ G.deg v0 <;> simp [u, v, h] <;> omega
  -- Apply exists_hamPath_plus to (u, v)
  obtain ⟨Q, hQlen, hQnodup, hQ0, hQn, hQwalk⟩ :=
    G.exists_hamPath_plus u v huv hno (hmax u v huv huv_non)
  -- Define index predicates on Fin n:
  -- Su(k) := adjPlus (emb u) Q[k+1]
  -- Sv(k) := adjPlus Q[k] (emb v)
  let Su : Fin n → Bool := fun k => G.adjPlus (emb u) (Q[k.val + 1]'(by omega))
  let Sv : Fin n → Bool := fun k => G.adjPlus (Q[k.val]'(by omega)) (emb v)
  -- Su and Sv are disjoint by no_posa_flip!
  have hdisj : ∀ k ∈ List.finRange n, !(Su k && Sv k) = true := by
    intro k _
    by_cases hSu : Su k = true
    · by_cases hSv : Sv k = true
      · exfalso
        have hu' : G.adjPlus (Q[0]'(by omega)) (Q[k.val + 1]'(by omega)) = true := by
          rw [hQ0]; exact hSu
        have hv' : G.adjPlus (Q[k.val]'(by omega)) (Q[n]'(by omega)) = true := by
          rw [hQn]; exact hSv
        exact G.no_posa_flip Q hQlen hQnodup hQwalk hno k.val k.isLt hv' hu'
      · simp [hSu, hSv]
    · simp [hSu]
  -- Helper: count of neighbors of emb x in Q is deg x + 1
  have hdeg_plus : ∀ x : Fin n, countFin (n + 1) (fun y => G.adjPlus (emb x) y) = G.deg x + 1 := by
    intro x
    -- Split over y = star vs y.val < n
    let star : Fin (n + 1) := ⟨n, by omega⟩
    have hsplit := list_countP_add_split (List.finRange (n + 1))
      (fun y => G.adjPlus (emb x) y) (fun y => decide (y = star))
    have hstar1 : (List.finRange (n + 1)).countP (fun y => G.adjPlus (emb x) y && decide (y = star)) = 1 := by
      have heq := list_countP_eq_of_eq (List.finRange (n + 1))
        (fun y => G.adjPlus (emb x) y && decide (y = star))
        (fun y => decide (y = star)) (fun y _ => by
          by_cases h : y = star
          · subst h; simp [star, adjPlus_star_right]
          · simp [h])
      rw [heq]
      exact countFin_single (n + 1) star
    have hrest : (List.finRange (n + 1)).countP (fun y => G.adjPlus (emb x) y && !decide (y = star)) = G.deg x := by
      -- Bijection between {y : Fin (n+1) | y ≠ star} and Fin n via emb
      let L1 := (List.finRange n).filter (fun z => G.adj x z)
      let L2 := (List.finRange (n + 1)).filter (fun y => G.adjPlus (emb x) y && !decide (y = star))
      have hlen1 : L1.length = G.deg x := by
        simp [L1, deg, countFin, list_length_filter_eq_countP]
      have hlen2 : L2.length =
          (List.finRange (n + 1)).countP (fun y => G.adjPlus (emb x) y && !decide (y = star)) := by
        simp [L2, list_length_filter_eq_countP]
      have hle1 : (L1.map emb).length ≤ L2.length := by
        have hnd : (L1.map emb).Nodup :=
          list_nodup_map_inj_on emb ((List.nodup_finRange n).filter _) (fun _ _ _ _ h => emb_inj h)
        have hsub : ∀ y ∈ L1.map emb, y ∈ L2 := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
          have hxz := (List.mem_filter.mp hz).2
          rw [List.mem_filter]
          refine ⟨List.mem_finRange _, ?_⟩
          have hns : emb z ≠ star := by
            intro h; have hv : z.val = n := by simpa [emb, star] using congrArg Fin.val h
            have := z.isLt; omega
          simp [adjPlus_emb, hxz, hns]
        have h := list_nodup_subset_countP (L1.map emb) L2 hnd hsub (fun _ => true) (fun _ _ => rfl)
        rw [list_countP_eq_of_forall_true _ _ (fun _ _ => rfl)] at h
        exact h
      have hle2 : L2.length ≤ L1.length := by
        let proj : Fin (n + 1) → Fin n := fun y =>
          if hy : y.val < n then ⟨y.val, hy⟩ else ⟨0, by omega⟩
        have hnd2 : L2.Nodup := (List.nodup_finRange (n + 1)).filter _
        have hlt2 : ∀ y ∈ L2, y.val < n := by
          intro y hy
          have h := (List.mem_filter.mp hy).2
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
          have hv : y.val ≠ n := fun hv => h.2 (Fin.ext hv)
          have := y.isLt; omega
        have hndp : (L2.map proj).Nodup :=
          list_nodup_map_inj_on proj hnd2 (fun a ha b hb hab => by
            have hal := hlt2 a ha; have hbl := hlt2 b hb
            have hval : a.val = b.val := by simpa [proj, hal, hbl] using congrArg Fin.val hab
            exact Fin.ext hval)
        have hsub2 : ∀ z ∈ L2.map proj, z ∈ L1 := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          have hyl := hlt2 y hy
          have hadj := (Bool.and_eq_true .. |>.mp (List.mem_filter.mp hy).2).1
          rw [List.mem_filter]
          refine ⟨List.mem_finRange _, ?_⟩
          have heq : emb (proj y) = y := by apply Fin.ext; simp [emb, proj, hyl]
          rw [← adjPlus_emb, heq]; exact hadj
        have h := list_nodup_subset_countP (L2.map proj) L1 hndp hsub2 (fun _ => true) (fun _ _ => rfl)
        rw [list_countP_eq_of_forall_true _ _ (fun _ _ => rfl), List.length_map] at h
        exact h
      rw [List.length_map] at hle1
      omega
    unfold countFin
    omega
  -- Count of Q satisfying P equals countFin (n + 1) P (since Q is a permutation of Fin (n + 1))
  have hQ_count : ∀ P : Fin (n + 1) → Bool, Q.countP P = countFin (n + 1) P := by
    intro P
    have hle1 : Q.countP P ≤ countFin (n + 1) P := by
      have h := nodup_length_le_countFin (Q.filter P) (hQnodup.filter P) P
        (fun x hx => (List.mem_filter.mp hx).2)
      rw [list_length_filter_eq_countP] at h
      exact h
    have hle2 : Q.countP (fun x => !P x) ≤ countFin (n + 1) (fun x => !P x) := by
      have h := nodup_length_le_countFin (Q.filter (fun x => !P x)) (hQnodup.filter _)
        (fun x => !P x) (fun x hx => (List.mem_filter.mp hx).2)
      rw [list_length_filter_eq_countP] at h
      exact h
    have h1 := list_countP_add_not Q P
    have h2 := countFin_add_not (n + 1) P
    omega
  -- Compute countFin n Su = deg u + 1
  have hSu_cnt : countFin n Su = G.deg u + 1 := by
    have hQeq : Q = Q[0]'(by omega) :: (List.finRange n).map (fun k => Q[k.val + 1]'(by omega)) := by
      apply List.ext_getElem
      · simp [hQlen]
      · intro idx h1 h2
        cases idx with
        | zero => simp
        | succ j => simp [List.getElem_finRange]
    have h1 : Q.countP (fun y => G.adjPlus (emb u) y) = countFin n Su := by
      conv => lhs; rw [hQeq]
      rw [List.countP_cons, hQ0, adjPlus_irrefl]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      unfold countFin Su
      rw [List.countP_map]
      rfl
    rw [← h1, hQ_count, hdeg_plus]
  -- Compute countFin n Sv = deg v + 1
  have hSv_cnt : countFin n Sv = G.deg v + 1 := by
    have hQeq : Q = (List.finRange n).map (fun k => Q[k.val]'(by omega)) ++ [Q[n]'(by omega)] := by
      apply List.ext_getElem
      · simp [hQlen]
      · intro idx h1 h2
        by_cases hlt : idx < n
        · rw [List.getElem_append_left (by simp; omega), List.getElem_map]
          simp [List.getElem_finRange]
        · have heq : idx = n := by omega
          subst heq
          rw [List.getElem_append_right (by simp)]
          simp
    have h1 : Q.countP (fun y => G.adjPlus y (emb v)) = countFin n Sv := by
      conv => lhs; rw [hQeq]
      rw [List.countP_append, List.countP_cons, List.countP_nil, hQn, adjPlus_irrefl]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      unfold countFin Sv
      rw [List.countP_map]
      rfl
    have h2 : countFin (n + 1) (fun y => G.adjPlus y (emb v)) = G.deg v + 1 := by
      rw [countFin_eq (n + 1) _ (fun y => G.adjPlus (emb v) y) (fun y => adjPlus_symm G y _)]
      exact hdeg_plus v
    rw [← h1, hQ_count, h2]
  -- From disjointness of Su and Sv: deg u + deg v ≤ n - 2
  have hsum_deg : G.deg u + G.deg v ≤ n - 2 := by
    have hle := list_countP_disjoint (List.finRange n) Su Sv hdisj
    rw [List.length_finRange] at hle
    unfold countFin at hSu_cnt hSv_cnt
    omega
  -- Set i = deg u + 1
  let i := G.deg u + 1
  have hi2 : 2 ≤ i := by
    have := G.pos_deg_of_connected (by omega) hconn u
    omega
  have hi_half : 2 * i ≤ n := by omega
  -- Bound 1: i ≤ countFin n (fun x => decide (G.deg x ≤ i - 1))
  -- Map each k ∈ finRange n with Su k = true to Q[k.val] (which is in Fin n and has deg ≤ deg u = i - 1!)
  have hA_bound : i ≤ countFin n (fun x => decide (G.deg x ≤ i - 1)) := by
    let Ks := (List.finRange n).filter Su
    have hKlen : Ks.length = i := by
      simp [Ks, list_length_filter_eq_countP]
      exact hSu_cnt
    have hKnodup : Ks.Nodup := (List.nodup_finRange n).filter Su
    -- Every k ∈ Ks has Q[k] ≠ star and Q[k] ≠ emb v and ¬adj Q[k] v
    have hK_lt : ∀ k ∈ Ks, (Q[k.val]'(by omega)).val < n := by
      intro k hk
      have hSu_k : Su k = true := (List.mem_filter.mp hk).2
      have hSv_f : Sv k = false := by
        have hd := hdisj k (List.mem_finRange k)
        simp [hSu_k] at hd; exact hd
      have hne_star : Q[k.val]'(by omega) ≠ ⟨n, by omega⟩ := by
        intro hstar
        have : Sv k = true := by
          simp only [Sv, hstar]; exact adjPlus_star_left G v
        rw [this] at hSv_f; cases hSv_f
      have hlt := (Q[k.val]'(by omega)).isLt
      have hvn : (Q[k.val]'(by omega)).val ≠ n := fun h => hne_star (Fin.ext h)
      omega
    let fK : Fin n → Fin n := fun k =>
      if h : (Q[k.val]'(by omega)).val < n then ⟨(Q[k.val]'(by omega)).val, h⟩ else ⟨0, by omega⟩
    let As := Ks.map fK
    have hAnodup : As.Nodup :=
      list_nodup_map_inj_on fK hKnodup (fun a ha b hb hab => by
        have hal := hK_lt a ha; have hbl := hK_lt b hb
        have hval : (Q[a.val]'(by omega)).val = (Q[b.val]'(by omega)).val := by
          simpa [fK, hal, hbl] using congrArg Fin.val hab
        have hQeq : Q[a.val]'(by omega) = Q[b.val]'(by omega) := Fin.ext hval
        have hidx := nodup_getElem_inj hQnodup (by omega) (by omega) hQeq
        exact Fin.ext hidx)
    have hAdeg : ∀ x ∈ As, decide (G.deg x ≤ i - 1) = true := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hkl := hK_lt k hk
      have hSu_k : Su k = true := (List.mem_filter.mp hk).2
      have hSv_f : Sv k = false := by
        have hd := hdisj k (List.mem_finRange k)
        simp [hSu_k] at hd; exact hd
      have hemb : emb (fK k) = Q[k.val]'(by omega) := by
        apply Fin.ext; simp [emb, fK, hkl]
      have hne_v : fK k ≠ v := by
        intro heq
        have hQeq : Q[k.val]'(by omega) = Q[n]'(by omega) := by
          rw [← hemb, heq, hQn]
        have := nodup_getElem_inj hQnodup (by omega) (by omega) hQeq
        omega
      have hnon_v : G.adj (fK k) v = false := by
        rw [← adjPlus_emb, hemb]; exact hSv_f
      have hle_sum := huv_max (fK k) v hne_v hnon_v
      simp only [decide_eq_true_eq]
      omega
    have h := nodup_length_le_countFin As hAnodup _ hAdeg
    simp only [As, List.length_map, hKlen] at h
    exact h
  -- Bound 2: n + 1 - i ≤ countFin n (fun x => decide (G.deg x ≤ n - 1 - i))
  -- Every vertex w with ¬G.adj u w (including w = u!) has deg w ≤ n - 1 - i
  have hB_bound : n + 1 - i ≤ countFin n (fun x => decide (G.deg x ≤ n - 1 - i)) := by
    have h1 : countFin n (fun w => !G.adj u w) = n - G.deg u := by
      have := countFin_add_not n (fun w => G.adj u w)
      unfold deg at *; omega
    have hle : countFin n (fun w => !G.adj u w) ≤
        countFin n (fun w => decide (G.deg w ≤ n - 1 - i)) := by
      apply countFin_mono
      intro w hw
      simp only [Bool.not_eq_true'] at hw
      simp only [decide_eq_true_eq]
      by_cases hwu : w = u
      · subst hwu; omega
      · have hle_sum := huv_max u w (Ne.symm hwu) hw
        omega
    omega
  exact ⟨i, hi2, hi_half, hA_bound, hB_bound⟩

/-! ## Section 5: Degree-Sum Lower Bound and Quadratic Arithmetic -/

theorem chvatal_compEdge_bound (G : SimpleGraph n) (i : Nat) (hi1 : 1 ≤ i) (hi_half : 2 * i ≤ n)
    (hA : i ≤ countFin n (fun x => decide (G.deg x ≤ i - 1)))
    (hB : n + 1 - i ≤ countFin n (fun x => decide (G.deg x ≤ n - 1 - i))) :
    i * (2 * n + 1 - 3 * i) ≤ 2 * G.compEdgeCount := by
  rw [G.two_mul_compEdgeCount]
  let PA : Fin n → Bool := fun x => decide (G.deg x ≤ i - 1)
  let PB : Fin n → Bool := fun x => decide (G.deg x ≤ n - 1 - i)
  have hsub : ∀ x : Fin n, PA x = true → PB x = true := by
    intro x hx
    simp only [PA, PB, decide_eq_true_eq] at hx ⊢
    omega
  -- Pointwise lower bound on degComp x:
  -- if PA x then n - i, else if PB x then i, else 0
  let lb : Fin n → Nat := fun x =>
    (if PA x then n - 2 * i else 0) + (if PB x then i else 0)
  have hpt : ∀ x : Fin n, lb x ≤ G.degComp x := by
    intro x
    have hdc := G.deg_add_degComp x
    by_cases h1 : PA x = true
    · have h2 : PB x = true := hsub x h1
      simp only [lb, h1, h2, ↓reduceIte]
      simp only [PA, decide_eq_true_eq] at h1
      omega
    · simp only [Bool.not_eq_true] at h1
      by_cases h2 : PB x = true
      · simp only [lb, h1, h2, Bool.false_eq_true, ↓reduceIte]
        simp only [PB, decide_eq_true_eq] at h2
        omega
      · simp only [Bool.not_eq_true] at h2
        simp [lb, h1, h2]
  have hsum_le := sumFin_le n lb (fun x => G.degComp x) hpt
  have hsum_lb : sumFin n lb = countFin n PA * (n - 2 * i) + countFin n PB * i := by
    unfold lb sumFin countFin
    rw [list_sum_map_add, list_sum_map_ite_const, list_sum_map_ite_const]
  have hmul1 : i * (n - 2 * i) ≤ countFin n PA * (n - 2 * i) :=
    Nat.mul_le_mul_right (n - 2 * i) hA
  have hmul2 : (n + 1 - i) * i ≤ countFin n PB * i :=
    Nat.mul_le_mul_right i hB
  have hid : i * (2 * n + 1 - 3 * i) = i * (n - 2 * i) + (n + 1 - i) * i := by
    have h1 : i * (2 * n + 1 - 3 * i) = i * ((n - 2 * i) + (n + 1 - i)) := by
      congr 1; omega
    rw [h1, Nat.mul_add, Nat.mul_comm i (n + 1 - i)]
  omega

/-- Pure quadratic inequality: for all `n ≥ 4`, `2 ≤ i ≤ n / 2`, either
    `i * (2n + 1 - 3i) > 6 * (n / 2) - 4` or `(n, i)` is one of the 4 finite exceptions
    `(4, 2), (6, 2), (6, 3), (8, 4)`. -/
theorem quadratic_dichotomy (n i : Nat) (hn : 4 ≤ n) (hi2 : 2 ≤ i) (hi_half : 2 * i ≤ n) :
    6 * (n / 2) - 4 < i * (2 * n + 1 - 3 * i) ∨
    (n = 4 ∧ i = 2) ∨ (n = 6 ∧ i = 2) ∨ (n = 6 ∧ i = 3) ∨ (n = 8 ∧ i = 4) := by
  let m := n / 2
  have hm_ge : 2 ≤ m := by omega
  have him : i ≤ m := by omega
  -- First show i * (2n + 1 - 3i) ≥ min(f(2), f(m))
  have hf_ge : 2 * (2 * n + 1 - 6) ≤ i * (2 * n + 1 - 3 * i) ∨
      m * (2 * n + 1 - 3 * m) ≤ i * (2 * n + 1 - 3 * i) := by
    by_cases h3i : 3 * i ≤ 2 * n - 5
    · left
      -- f(i) - f(2) = (i - 2) * (2n - 5 - 3i) ≥ 0
      have h1 : 2 * (2 * n + 1 - 6) + (i - 2) * (2 * n - 5 - 3 * i) = i * (2 * n + 1 - 3 * i) := by
        have hstep : 2 * (2 * n - 5) + (i - 2) * (2 * n - 5 - 3 * i) + 3 * i * i =
            i * (2 * n + 1) := by
          have : (i - 2) * (2 * n - 5 - 3 * i) + 3 * i * (i - 2) = (i - 2) * (2 * n - 5) := by
            rw [Nat.mul_comm (3 * i) (i - 2), ← Nat.mul_add]
            have : 2 * n - 5 - 3 * i + 3 * i = 2 * n - 5 := by omega
            rw [this]
          have : 2 * (2 * n - 5) + (i - 2) * (2 * n - 5) = i * (2 * n - 5) := by
            rw [← Nat.add_mul]; congr 1; omega
          have : i * (2 * n - 5) + 6 * i = i * (2 * n + 1) := by
            rw [Nat.mul_comm 6 i, ← Nat.mul_add]; congr 1; omega
          have : 3 * i * i = 3 * i * (i - 2) + 6 * i := by
            have : 3 * i * (i - 2) + 3 * i * 2 = 3 * i * i := by
              rw [← Nat.mul_add]; congr 1; omega
            omega
          omega
        have : i * (2 * n + 1 - 3 * i) + 3 * i * i = i * (2 * n + 1) := by
          have : i * (2 * n + 1 - 3 * i) + i * (3 * i) = i * (2 * n + 1) := by
            rw [← Nat.mul_add]; congr 1; omega
          have : i * (3 * i) = 3 * i * i := by
            rw [← Nat.mul_assoc, Nat.mul_comm i 3]
          omega
        omega
      omega
    · right
      -- When 3i ≥ 2n - 4, show f(m) ≤ f(i):
      -- f(i) - f(m) = (m - i) * (3i + 3m - 2n - 1) ≥ 0 (since n ≥ 5 here; n=4 has i=m=2!)
      by_cases him_eq : i = m
      · subst him_eq; exact Nat.le_refl _
      · have hn5 : 5 ≤ n := by omega
        have hpos : 2 * n + 1 ≤ 3 * i + 3 * m := by omega
        have hdiff : m * (2 * n + 1 - 3 * m) + (m - i) * (3 * i + 3 * m - (2 * n + 1)) =
            i * (2 * n + 1 - 3 * i) := by
          have ha : m * (2 * n + 1 - 3 * m) + 3 * m * m = m * (2 * n + 1) := by
            have h1 : m * (2 * n + 1 - 3 * m) + m * (3 * m) = m * (2 * n + 1) := by
              rw [← Nat.mul_add]; congr 1; omega
            have h2 : m * (3 * m) = 3 * m * m := by rw [← Nat.mul_assoc, Nat.mul_comm m 3]
            omega
          have hb : i * (2 * n + 1 - 3 * i) + 3 * i * i = i * (2 * n + 1) := by
            have h1 : i * (2 * n + 1 - 3 * i) + i * (3 * i) = i * (2 * n + 1) := by
              rw [← Nat.mul_add]; congr 1; omega
            have h2 : i * (3 * i) = 3 * i * i := by rw [← Nat.mul_assoc, Nat.mul_comm i 3]
            omega
          have hc : (m - i) * (3 * i + 3 * m - (2 * n + 1)) + (m - i) * (2 * n + 1) =
              (m - i) * (3 * i + 3 * m) := by
            rw [← Nat.mul_add]; congr 1; omega
          have hd : (m - i) * (3 * i + 3 * m) + 3 * i * i = 3 * m * m := by
            have h1 : (m - i) * (3 * i + 3 * m) = 3 * ((m - i) * (m + i)) := by
              have : 3 * i + 3 * m = 3 * (m + i) := by omega
              rw [this, Nat.mul_left_comm]
            have h2 : (m - i) * (m + i) + i * i = m * m := by
              rw [Nat.mul_add, Nat.add_assoc]
              have h3 : (m - i) * i + i * i = m * i := by
                rw [← Nat.add_mul]; congr 1; omega
              rw [h3]
              have h4 : (m - i) * m + m * i = m * m := by
                rw [Nat.mul_comm (m - i) m, ← Nat.mul_add]; congr 1; omega
              exact h4
            omega
          have he : i * (2 * n + 1) + (m - i) * (2 * n + 1) = m * (2 * n + 1) := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        omega
  -- Now dispatch n = 4, 5, 6, 7, 8, 9 directly and n ≥ 10 algebraically!
  by_cases hn10 : n < 10
  · -- Finite check for 4 ≤ n ≤ 9 and 2 ≤ i ≤ n/2
    have hcases : (n = 4 ∧ i = 2) ∨ (n = 5 ∧ i = 2) ∨
        (n = 6 ∧ i = 2) ∨ (n = 6 ∧ i = 3) ∨
        (n = 7 ∧ i = 2) ∨ (n = 7 ∧ i = 3) ∨
        (n = 8 ∧ i = 2) ∨ (n = 8 ∧ i = 3) ∨ (n = 8 ∧ i = 4) ∨
        (n = 9 ∧ i = 2) ∨ (n = 9 ∧ i = 3) ∨ (n = 9 ∧ i = 4) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  · -- For n ≥ 10: m ≥ 5, so BOTH f(2) > 6m - 4 AND f(m) > 6m - 4!
    left
    have hm5 : 5 ≤ m := by omega
    rcases hf_ge with hf2 | hfm
    · omega
    · -- f(m) = m * (2n + 1 - 3m) ≥ m * (m + 1) ≥ 5 * (m + 1) + (m - 5) * ... > 6m - 4!
      have hge1 : m * (m + 1) ≤ m * (2 * n + 1 - 3 * m) :=
        Nat.mul_le_mul_left m (by omega)
      have hge2 : 6 * m - 4 < m * (m + 1) := by
        have h1 : 5 * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right (m + 1) hm5
        -- Actually for m ≥ 5: (m - 5) * m ≥ 0, wait: m*(m+1) = m^2 + m ≥ 5m + m = 6m > 6m - 4!
        have h2 : 5 * m ≤ m * m := Nat.mul_le_mul_right m hm5
        rw [Nat.mul_add, Nat.mul_one]
        omega
      omega

/-! ## Section 6: Subset Edge-Counting Identity and the 4 Finite Exceptions -/

/-- Exact edge partition for a subset `S` of `Fin n`:
    `2 * edgeCount G = 2 * sum_{x ∈ S} deg x - 2 * e(S) + 2 * e(B)`. -/
theorem edgeCount_partition (G : SimpleGraph n) (inS : Fin n → Bool) :
    let eS := sumFin n (fun u => countFin n (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v))
    let eB := sumFin n (fun u => countFin n (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v))
    let degS := sumFin n (fun u => if inS u then G.deg u else 0)
    2 * G.edgeCount + 2 * eS = 2 * degS + 2 * eB := by
  intro eS eB degS
  -- Define directed counts:
  -- dSS = ∑_{u ∈ S} |{v ∈ S : adj u v}| = 2 * eS
  -- dSB = ∑_{u ∈ S} |{v ∉ S : adj u v}|
  -- dBS = ∑_{u ∉ S} |{v ∈ S : adj u v}| = dSB
  -- dBB = ∑_{u ∉ S} |{v ∉ S : adj u v}| = 2 * eB
  let dSS := sumFin n (fun u => countFin n (fun v => inS u && inS v && G.adj u v))
  let dSB := sumFin n (fun u => countFin n (fun v => inS u && !inS v && G.adj u v))
  let dBS := sumFin n (fun u => countFin n (fun v => !inS u && inS v && G.adj u v))
  let dBB := sumFin n (fun u => countFin n (fun v => !inS u && !inS v && G.adj u v))
  have hdSB_eq : dSB = dBS := by
    unfold dSB dBS
    rw [sumFin_swap n (fun u v => inS u && !inS v && G.adj u v)]
    apply sumFin_eq; intro u; apply countFin_eq; intro v
    rw [G.symm v u]
    cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
  have h2eS : 2 * eS = dSS := by
    have hswap : eS = sumFin n (fun u => countFin n (fun v => decide (v.val < u.val) && inS u && inS v && G.adj u v)) := by
      unfold eS
      rw [sumFin_swap n (fun u v => decide (u.val < v.val) && inS u && inS v && G.adj u v)]
      apply sumFin_eq; intro u; apply countFin_eq; intro v
      rw [G.symm v u]
      cases decide (v.val < u.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
    have hadd : eS + eS = dSS := by
      conv => lhs; arg 2; rw [hswap]
      unfold eS dSS
      rw [← sumFin_add]
      apply sumFin_eq; intro u
      have hsp := list_countP_add_split (List.finRange n)
        (fun v => inS u && inS v && G.adj u v) (fun v => decide (u.val < v.val))
      have h1 : countFin n (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (inS u && inS v && G.adj u v) && decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        cases decide (u.val < v.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
      have h2 : countFin n (fun v => decide (v.val < u.val) && inS u && inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (inS u && inS v && G.adj u v) && !decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        by_cases huv : u = v
        · subst huv; simp [G.irrefl]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          by_cases hlt : u.val < v.val
          · have hgt : ¬(v.val < u.val) := by omega
            simp [hlt, hgt]
          · have hgt : v.val < u.val := by omega
            simp [hlt, hgt]
      rw [h1, h2, hsp]; rfl
    omega
  have h2eB : 2 * eB = dBB := by
    have hswap : eB = sumFin n (fun u => countFin n (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v)) := by
      unfold eB
      rw [sumFin_swap n (fun u v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v)]
      apply sumFin_eq; intro u; apply countFin_eq; intro v
      rw [G.symm v u]
      cases decide (v.val < u.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
    have hadd : eB + eB = dBB := by
      conv => lhs; arg 2; rw [hswap]
      unfold eB dBB
      rw [← sumFin_add]
      apply sumFin_eq; intro u
      have hsp := list_countP_add_split (List.finRange n)
        (fun v => !inS u && !inS v && G.adj u v) (fun v => decide (u.val < v.val))
      have h1 : countFin n (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (!inS u && !inS v && G.adj u v) && decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        cases decide (u.val < v.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
      have h2 : countFin n (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (!inS u && !inS v && G.adj u v) && !decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        by_cases huv : u = v
        · subst huv; simp [G.irrefl]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          by_cases hlt : u.val < v.val
          · have hgt : ¬(v.val < u.val) := by omega
            simp [hlt, hgt]
          · have hgt : v.val < u.val := by omega
            simp [hlt, hgt]
      rw [h1, h2, hsp]; rfl
    omega
  have hdegS : degS = dSS + dSB := by
    unfold degS dSS dSB
    rw [← sumFin_add]
    apply sumFin_eq; intro u
    cases hSu : inS u
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      have h0 : countFin n (fun _ => false) = 0 := (countFin_eq_zero_iff n _).mpr (fun _ => rfl)
      omega
    · simp only [↓reduceIte, Bool.true_and]
      have hsp := list_countP_add_split (List.finRange n) (fun v => G.adj u v) inS
      have h1 : countFin n (fun v => inS v && G.adj u v) =
          (List.finRange n).countP (fun v => G.adj u v && inS v) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _; exact Bool.and_comm ..
      have h2 : countFin n (fun v => !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => G.adj u v && !inS v) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _; exact Bool.and_comm ..
      rw [h1, h2, hsp]; rfl
  have hdegB : sumFin n (fun u => if !inS u then G.deg u else 0) = dBS + dBB := by
    unfold dBS dBB
    rw [← sumFin_add]
    apply sumFin_eq; intro u
    cases hSu : inS u
    · simp only [Bool.not_false, ↓reduceIte, Bool.true_and]
      have hsp := list_countP_add_split (List.finRange n) (fun v => G.adj u v) inS
      have h1 : countFin n (fun v => inS v && G.adj u v) =
          (List.finRange n).countP (fun v => G.adj u v && inS v) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _; exact Bool.and_comm ..
      have h2 : countFin n (fun v => !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => G.adj u v && !inS v) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _; exact Bool.and_comm ..
      rw [h1, h2, hsp]; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      have h0 : countFin n (fun _ => false) = 0 := (countFin_eq_zero_iff n _).mpr (fun _ => rfl)
      omega
  have htotal : 2 * G.edgeCount = degS + sumFin n (fun u => if !inS u then G.deg u else 0) := by
    rw [G.two_mul_edgeCount]
    unfold degS
    rw [← sumFin_add]
    apply sumFin_eq; intro u
    cases inS u <;> simp
  omega

/-- Upper bound `2 * e(B) ≤ |B| * (|B| - 1)`. -/
theorem two_mul_eB_le (G : SimpleGraph n) (inS : Fin n → Bool) :
    let eB := sumFin n (fun u => countFin n (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v))
    let b := countFin n (fun u => !inS u)
    2 * eB ≤ b * (b - 1) := by
  intro eB b
  -- 2 * eB = ∑_{u ∉ S} |{v ∉ S : adj u v}| ≤ ∑_{u ∉ S} (b - 1) = b * (b - 1)
  let dBB := sumFin n (fun u => countFin n (fun v => !inS u && !inS v && G.adj u v))
  have h2eB : 2 * eB = dBB := by
    have hswap : eB = sumFin n (fun u => countFin n (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v)) := by
      unfold eB
      rw [sumFin_swap n (fun u v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v)]
      apply sumFin_eq; intro u; apply countFin_eq; intro v
      rw [G.symm v u]
      cases decide (v.val < u.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
    have hadd : eB + eB = dBB := by
      conv => lhs; arg 2; rw [hswap]
      unfold eB dBB
      rw [← sumFin_add]
      apply sumFin_eq; intro u
      have hsp := list_countP_add_split (List.finRange n)
        (fun v => !inS u && !inS v && G.adj u v) (fun v => decide (u.val < v.val))
      have h1 : countFin n (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (!inS u && !inS v && G.adj u v) && decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        cases decide (u.val < v.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
      have h2 : countFin n (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v) =
          (List.finRange n).countP (fun v => (!inS u && !inS v && G.adj u v) && !decide (u.val < v.val)) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        by_cases huv : u = v
        · subst huv; simp [G.irrefl]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          by_cases hlt : u.val < v.val
          · have hgt : ¬(v.val < u.val) := by omega
            simp [hlt, hgt]
          · have hgt : v.val < u.val := by omega
            simp [hlt, hgt]
      rw [h1, h2, hsp]; rfl
    omega
  rw [h2eB]
  have hle : dBB ≤ sumFin n (fun u => if !inS u then b - 1 else 0) := by
    apply sumFin_le; intro u
    cases hSu : inS u
    · simp only [Bool.not_false, ↓reduceIte, Bool.true_and]
      have h1 : countFin n (fun v => !inS v && G.adj u v) ≤
          countFin n (fun v => !inS v && !decide (v = u)) := by
        apply countFin_mono; intro v hv
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv ⊢
        refine ⟨hv.1, fun h => by subst h; rw [G.irrefl] at hv; cases hv.2⟩
      have hsp := list_countP_add_split (List.finRange n) (fun v => !inS v) (fun v => decide (v = u))
      have hsingle : (List.finRange n).countP (fun v => !inS v && decide (v = u)) = 1 := by
        have heq := list_countP_eq_of_eq (List.finRange n)
          (fun v => !inS v && decide (v = u)) (fun v => decide (v = u)) (fun v _ => by
            by_cases h : v = u
            · subst h; simp [hSu]
            · simp [h])
        rw [heq]; exact countFin_single n u
      unfold b countFin at *
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      have : countFin n (fun _ => false) = 0 := (countFin_eq_zero_iff n _).mpr (fun _ => rfl)
      omega
  have hrhs : sumFin n (fun u => if !inS u then b - 1 else 0) = b * (b - 1) := by
    unfold sumFin b countFin
    exact list_sum_map_ite_const (List.finRange n) (fun u => !inS u) (b - 1)
  omega

/-- If a matching has size `> |B|`, then at least one matching edge lies completely inside `S`. -/
theorem matching_edge_in_S (G : SimpleGraph n) (inS : Fin n → Bool)
    (M : List (Fin n × Fin n)) (hM : G.IsMatching M)
    (hgt : countFin n (fun x => !inS x) < M.length) :
    ∃ e ∈ M, inS e.1 = true ∧ inS e.2 = true := by
  apply Classical.byContradiction; intro hno
  -- Every edge e ∈ M has at least one endpoint in B = !inS
  let pickB : Fin n × Fin n → Fin n := fun e => if !inS e.1 then e.1 else e.2
  let Bs := M.map pickB
  have hBmem : ∀ e ∈ M, !inS (pickB e) = true := by
    intro e he
    by_cases h1 : inS e.1 = true
    · by_cases h2 : inS e.2 = true
      · exact absurd ⟨e, he, h1, h2⟩ hno
      · simp [pickB, h1, h2]
    · simp [pickB, h1]
  -- Bs is Nodup because each pickB e is one of the two endpoints of e, and flatMap is Nodup!
  have hBnodup : Bs.Nodup := by
    have hnd := hM.2
    clear hBmem hno hgt
    induction M with
    | nil => simp [Bs]
    | cons e es ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd
      obtain ⟨he1_not, he2_not, hes_nd⟩ := hnd
      simp only [Bs, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih ⟨fun x hx => hM.1 x (List.mem_cons_of_mem e hx), hes_nd⟩ hes_nd⟩
      intro hmem
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hmem
      have he'_in : pickB e' ∈ es.flatMap (fun p => [p.1, p.2]) := by
        rw [List.mem_flatMap]
        refine ⟨e', he', ?_⟩
        cases h1 : inS e'.1 <;> simp [pickB, h1]
      rw [heq] at he'_in
      by_cases h1 : !inS e.1
      · simp only [pickB, h1, ↓reduceIte] at he'_in
        exact he1_not (List.mem_cons_of_mem _ he'_in)
      · simp only [pickB, h1] at he'_in
        exact he2_not he'_in
  have hle := nodup_length_le_countFin Bs hBnodup (fun x => !inS x) (fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hBmem e he)
  simp only [Bs, List.length_map] at hle
  omega

/-- Exception 1: `n = 4, i = 2` is impossible. -/
theorem case_n4_i2 (G : SimpleGraph 4) (hconn : G.IsConnected)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber)
    (hB : 3 ≤ countFin 4 (fun x => decide (G.deg x ≤ 1))) : False := by
  have hcomp_lb : 6 ≤ 2 * G.compEdgeCount := by
    -- 3 vertices have deg ≤ 1, hence degComp ≥ 2
    rw [G.two_mul_compEdgeCount]
    have hpt : ∀ x : Fin 4, (if decide (G.deg x ≤ 1) then 2 else 0) ≤ G.degComp x := by
      intro x
      have := G.deg_add_degComp x
      by_cases h : G.deg x ≤ 1 <;> simp [h] <;> omega
    have h1 : sumFin 4 (fun x => if decide (G.deg x ≤ 1) then 2 else 0) ≤
        sumFin 4 (fun x => G.degComp x) := sumFin_le 4 _ _ hpt
    have h2 : sumFin 4 (fun x => if decide (G.deg x ≤ 1) then 2 else 0) =
        countFin 4 (fun x => decide (G.deg x ≤ 1)) * 2 :=
      list_sum_map_ite_const (List.finRange 4) _ 2
    rw [h2] at h1
    omega
  have hmu2 : 2 ≤ G.matchingNumber := by omega
  obtain ⟨⟨M, hM, hMlen⟩, _⟩ := G.matchingNumber_spec_aux
  let inS : Fin 4 → Bool := fun x => decide (G.deg x ≤ 1)
  have hBsz : countFin 4 (fun x => !inS x) ≤ 1 := by
    have hB' : 3 ≤ countFin 4 inS := hB
    have := countFin_add_not 4 inS; omega
  obtain ⟨e, heM, he1, he2⟩ := G.matching_edge_in_S inS M hM (by omega)
  exact G.no_isolated_edge_of_connected (by omega) hconn e.1 e.2 (hM.1 e heM)
    (of_decide_eq_true he1) (of_decide_eq_true he2)

/-- Exception 2: `n = 6, i = 2` is impossible. -/
theorem case_n6_i2 (G : SimpleGraph 6) (hconn : G.IsConnected)
    (hno : ¬ G.HasHamiltonianPath)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber)
    (hA : 2 ≤ countFin 6 (fun x => decide (G.deg x ≤ 1)))
    (hB : 5 ≤ countFin 6 (fun x => decide (G.deg x ≤ 3))) : False := by
  have hcomp_lb := G.chvatal_compEdge_bound 2 (by omega) (by omega) hA hB
  -- hcomp_lb : 14 ≤ 2 * compEdgeCount; combined with 2 * μ ≤ 6 and 3 + 2*ē ≤ 6*μ:
  have hmu_le := G.two_mul_matchingNumber_le
  have hmu3 : G.matchingNumber = 3 := by omega
  have hebar7 : G.compEdgeCount = 7 := by omega
  obtain ⟨a1, a2, ha12, hda1, hda2⟩ := exists_of_countFin_ge_two _ hA
  have hda1' : G.deg a1 = 1 := by
    have h1 := of_decide_eq_true hda1
    have h2 := G.pos_deg_of_connected (by omega) hconn a1
    omega
  have hda2' : G.deg a2 = 1 := by
    have h1 := of_decide_eq_true hda2
    have h2 := G.pos_deg_of_connected (by omega) hconn a2
    omega
  -- a1 and a2 are NOT adjacent (else isolated edge in connected graph on 6 vertices)
  have hnon12 : G.adj a1 a2 = false := by
    cases h : G.adj a1 a2
    · rfl
    · exact absurd (G.no_isolated_edge_of_connected (by omega) hconn a1 a2 h (by omega) (by omega))
        (fun x => x)
  -- Get unique neighbor b1 of a1 and b2 of a2
  obtain ⟨b1, hb1⟩ := (countFin_pos_iff 6 _).mp (by omega : 0 < G.deg a1)
  obtain ⟨b2, hb2⟩ := (countFin_pos_iff 6 _).mp (by omega : 0 < G.deg a2)
  have huniq1 : ∀ x : Fin 6, G.adj a1 x = true → x = b1 := by
    intro x hax; apply Classical.byContradiction; intro hne
    have h2 := nodup_length_le_countFin [b1, x] (by simp [Ne.symm hne]) (fun v => G.adj a1 v)
      (fun v hv => by simp at hv; rcases hv with rfl | rfl; exact hb1; exact hax)
    change 2 ≤ G.deg a1 at h2; omega
  have huniq2 : ∀ x : Fin 6, G.adj a2 x = true → x = b2 := by
    intro x hax; apply Classical.byContradiction; intro hne
    have h2 := nodup_length_le_countFin [b2, x] (by simp [Ne.symm hne]) (fun v => G.adj a2 v)
      (fun v hv => by simp at hv; rcases hv with rfl | rfl; exact hb2; exact hax)
    change 2 ≤ G.deg a2 at h2; omega
  have hb1_ne_a1 : b1 ≠ a1 := fun h => by subst h; rw [G.irrefl] at hb1; cases hb1
  have hb1_ne_a2 : b1 ≠ a2 := fun h => by subst h; rw [hnon12] at hb1; cases hb1
  have hb2_ne_a2 : b2 ≠ a2 := fun h => by subst h; rw [G.irrefl] at hb2; cases hb2
  have hb2_ne_a1 : b2 ≠ a1 := fun h => by subst h; rw [G.symm, hnon12] at hb2; cases hb2
  -- b1 ≠ b2 because G has a matching of size 3 (perfect matching on 6 vertices)!
  have hb12 : b1 ≠ b2 := by
    intro heq; subst heq
    obtain ⟨⟨M, hM, hMlen⟩, _⟩ := G.matchingNumber_spec_aux
    -- Every vertex of Fin 6 must be an endpoint of M (since 2*3 = 6 distinct endpoints!)
    let eps := M.flatMap (fun e => [e.1, e.2])
    have heps_len : eps.length = 6 := by
      have hlen : ∀ l : List (Fin 6 × Fin 6), (l.flatMap (fun e => [e.1, e.2])).length = 2 * l.length := by
        intro l; induction l with | nil => simp | cons e es ih => simp [List.flatMap_cons, ih]; omega
      rw [hlen M]; omega
    have hmem_all : ∀ x : Fin 6, x ∈ eps := by
      intro x; apply Classical.byContradiction; intro hnot
      have hle := nodup_length_le_countFin eps hM.2 (fun y => !decide (y = x))
        (fun y hy => by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; intro h; subst h; exact hnot hy)
      have h1 := countFin_add_not 6 (fun y => decide (y = x))
      have h2 := countFin_single 6 x
      omega
    -- Both a1 and a2 are in eps, so both are matched to their unique neighbor b1!
    obtain ⟨e1, he1M, ha1_e1⟩ := List.mem_flatMap.mp (hmem_all a1)
    obtain ⟨e2, he2M, ha2_e2⟩ := List.mem_flatMap.mp (hmem_all a2)
    have he1_b1 : b1 ∈ [e1.1, e1.2] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha1_e1 ⊢
      rcases ha1_e1 with h | h
      · exact Or.inr (huniq1 e1.2 (h ▸ hM.1 e1 he1M)).symm
      · exact Or.inl (huniq1 e1.1 (by rw [G.symm, h]; exact hM.1 e1 he1M)).symm
    have he2_b1 : b1 ∈ [e2.1, e2.2] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha2_e2 ⊢
      rcases ha2_e2 with h | h
      · exact Or.inr (huniq2 e2.2 (h ▸ hM.1 e2 he2M)).symm
      · exact Or.inl (huniq2 e2.1 (by rw [G.symm, h]; exact hM.1 e2 he2M)).symm
    have he12_ne : e1 ≠ e2 := by
      intro heq; subst heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha1_e1 ha2_e2 he1_b1
      rcases ha1_e1 with h1 | h1 <;> rcases ha2_e2 with h2 | h2 <;> rcases he1_b1 with h3 | h3
      · exact ha12 (h1.trans h2.symm)
      · exact ha12 (h1.trans h2.symm)
      · exact hb1_ne_a1 (h3.trans h1.symm)
      · exact hb1_ne_a2 (h3.trans h2.symm)
      · exact hb1_ne_a2 (h3.trans h2.symm)
      · exact hb1_ne_a1 (h3.trans h1.symm)
      · exact ha12 (h1.trans h2.symm)
      · exact ha12 (h1.trans h2.symm)
    -- Two distinct edges in M both contain b1, contradicting eps.Nodup!
    have hdup : ∀ l : List (Fin 6 × Fin 6), (l.flatMap (fun e => [e.1, e.2])).Nodup →
        ∀ x ∈ l, ∀ y ∈ l, x ≠ y → b1 ∈ [x.1, x.2] → b1 ∈ [y.1, y.2] → False := by
      intro l hnd
      induction l with
      | nil => intro x hx; simp at hx
      | cons z zs ih =>
        rw [List.flatMap_cons, List.nodup_append] at hnd
        intro x hx y hy hxy hbx hby
        cases hx with
        | head =>
          cases hy with
          | head => exact hxy rfl
          | tail _ hy' =>
            exact hnd.2.2 b1 hbx b1 (List.mem_flatMap.mpr ⟨y, hy', hby⟩) rfl
        | tail _ hx' =>
          cases hy with
          | head =>
            exact hnd.2.2 b1 hby b1 (List.mem_flatMap.mpr ⟨x, hx', hbx⟩) rfl
          | tail _ hy' =>
            exact ih hnd.2.1 x hx' y hy' hxy hbx hby
    exact hdup M hM.2 e1 he1M e2 he2M he12_ne he1_b1 he2_b1
  -- Every pair in V \ {a1, a2} MUST be an edge of G!
  -- Because using edgeCount_partition with S = {a1, a2}:
  -- degS = 2, eS = 0, so 2 * edgeCount G = 4 + 2 * eB.
  -- Since compEdgeCount G = 7, 2 * edgeCount G = 30 - 14 = 16, so 2 * eB = 12 = 4 * 3!
  let inS : Fin 6 → Bool := fun x => decide (x = a1) || decide (x = a2)
  have hpart := G.edgeCount_partition inS
  have heS0 : sumFin 6 (fun u => countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v)) = 0 := by
    have hzero : ∀ u : Fin 6, countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v) = 0 := by
      intro u
      rw [countFin_eq_zero_iff]
      intro v
      by_cases hu1 : u = a1
      · rw [hu1]; by_cases hv1 : v = a1
        · rw [hv1]; simp [G.irrefl]
        · by_cases hv2 : v = a2
          · rw [hv2]; simp [hnon12]
          · simp [inS, hv1, hv2]
      · by_cases hu2 : u = a2
        · rw [hu2]; by_cases hv1 : v = a1
          · rw [hv1]; simp [G.symm, hnon12]
          · by_cases hv2 : v = a2
            · rw [hv2]; simp [G.irrefl]
            · simp [inS, hv1, hv2]
        · simp [inS, hu1, hu2]
    rw [sumFin_eq 6 _ (fun _ => 0) hzero, sumFin_const]
  have hdegS2 : sumFin 6 (fun u => if inS u then G.deg u else 0) = 2 := by
    have heq : ∀ u : Fin 6, (if inS u then G.deg u else 0) = if inS u then 1 else 0 := by
      intro u
      by_cases h1 : u = a1
      · subst h1; simp [inS, hda1']
      · by_cases h2 : u = a2
        · subst h2; simp [inS, hda2']
        · simp [inS, h1, h2]
    rw [sumFin_eq 6 _ _ heq]
    unfold sumFin
    rw [list_sum_map_ite_const]
    have hcnt : (List.finRange 6).countP inS = 2 := by
      have hle := nodup_length_le_countFin [a1, a2] (by simp [ha12]) inS
        (fun v hv => by simp at hv; rcases hv with rfl | rfl <;> simp [inS])
      have hge := list_countP_or_le (List.finRange 6)
        (fun v => decide (v = a1)) (fun v => decide (v = a2))
      have s1 := countFin_single 6 a1; have s2 := countFin_single 6 a2
      unfold countFin at hle s1 s2; simp only [List.length_cons, List.length_nil] at hle
      change (List.finRange 6).countP inS ≤ _ at hge
      omega
    omega
  have h2e : 2 * G.edgeCount = 16 := by
    have := G.two_mul_edge_add_comp; omega
  have h2eB : 2 * sumFin 6 (fun u => countFin 6 (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v)) = 12 := by
    dsimp only at hpart; omega
  have hb4_all : countFin 6 (fun v => !inS v) = 4 := by
    have h1 := countFin_add_not 6 inS
    have hle := nodup_length_le_countFin [a1, a2] (by simp [ha12]) inS
      (fun v hv => by simp at hv; rcases hv with rfl | rfl <;> simp [inS])
    have hge := list_countP_or_le (List.finRange 6)
      (fun v => decide (v = a1)) (fun v => decide (v = a2))
    have s1 := countFin_single 6 a1; have s2 := countFin_single 6 a2
    unfold countFin at h1 hle s1 s2; simp only [List.length_cons, List.length_nil] at hle
    change (List.finRange 6).countP inS ≤ _ at hge
    unfold countFin; omega
  -- Hence every pair of distinct vertices outside {a1, a2} is adjacent!
  have hclique : ∀ x y : Fin 6, inS x = false → inS y = false → x ≠ y → G.adj x y = true := by
    intro x y hx hy hxy
    apply Classical.byContradiction; intro hnot
    have hfalse : G.adj x y = false := by cases h : G.adj x y; rfl; exact absurd h hnot
    let eB := sumFin 6 (fun u => countFin 6 (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v))
    have hlt_x : countFin 6 (fun v => !inS x && !inS v && G.adj x v) ≤ 2 := by
      have hsub : countFin 6 (fun v => !inS x && !inS v && G.adj x v) ≤
          countFin 6 (fun v => !inS v && !decide (v = x) && !decide (v = y)) := by
        apply countFin_mono; intro v hv
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv ⊢
        refine ⟨⟨hv.1.2, fun h => by subst h; rw [G.irrefl] at hv; cases hv.2⟩,
          fun h => by subst h; rw [hfalse] at hv; cases hv.2⟩
      have hxy_inB : countFin 6 (fun v => !inS v && (decide (v = x) || decide (v = y))) = 2 := by
        have hle := nodup_length_le_countFin [x, y] (by simp [hxy])
          (fun v => !inS v && (decide (v = x) || decide (v = y)))
          (fun v hv => by simp at hv; rcases hv with rfl | rfl; simp [hx]; simp [hy])
        have hge : countFin 6 (fun v => !inS v && (decide (v = x) || decide (v = y))) ≤ 2 := by
          have h1 : countFin 6 (fun v => !inS v && (decide (v = x) || decide (v = y))) ≤
              countFin 6 (fun v => decide (v = x) || decide (v = y)) :=
            countFin_mono 6 _ _ (fun v hv => (Bool.and_eq_true .. |>.mp hv).2)
          have h2 := list_countP_or_le (List.finRange 6)
            (fun v => decide (v = x)) (fun v => decide (v = y))
          have s1 := countFin_single 6 x; have s2 := countFin_single 6 y
          unfold countFin at h1 s1 s2 ⊢; omega
        simp only [List.length_cons, List.length_nil] at hle; omega
      have hsp := list_countP_add_split (List.finRange 6) (fun v => !inS v)
        (fun v => decide (v = x) || decide (v = y))
      have heq' : countFin 6 (fun v => !inS v && !decide (v = x) && !decide (v = y)) =
          (List.finRange 6).countP (fun v => !inS v && !(decide (v = x) || decide (v = y))) := by
        unfold countFin; apply list_countP_eq_of_eq; intro v _
        cases inS v <;> cases decide (v = x) <;> cases decide (v = y) <;> rfl
      unfold countFin at hb4_all hxy_inB
      omega
    have hdBB_eq : 2 * eB = sumFin 6 (fun u => countFin 6 (fun v => !inS u && !inS v && G.adj u v)) := by
      have hswap : eB = sumFin 6 (fun u => countFin 6 (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v)) := by
        unfold eB
        rw [sumFin_swap 6 (fun u v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v)]
        apply sumFin_eq; intro u; apply countFin_eq; intro v
        rw [G.symm v u]
        cases decide (v.val < u.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
      have hadd : eB + eB = sumFin 6 (fun u => countFin 6 (fun v => !inS u && !inS v && G.adj u v)) := by
        conv => lhs; arg 2; rw [hswap]
        unfold eB; rw [← sumFin_add]; apply sumFin_eq; intro u
        have hsp := list_countP_add_split (List.finRange 6)
          (fun v => !inS u && !inS v && G.adj u v) (fun v => decide (u.val < v.val))
        have h1 : countFin 6 (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v) =
            (List.finRange 6).countP (fun v => (!inS u && !inS v && G.adj u v) && decide (u.val < v.val)) := by
          unfold countFin; apply list_countP_eq_of_eq; intro v _
          cases decide (u.val < v.val) <;> cases inS u <;> cases inS v <;> cases G.adj u v <;> rfl
        have h2 : countFin 6 (fun v => decide (v.val < u.val) && !inS u && !inS v && G.adj u v) =
            (List.finRange 6).countP (fun v => (!inS u && !inS v && G.adj u v) && !decide (u.val < v.val)) := by
          unfold countFin; apply list_countP_eq_of_eq; intro v _
          by_cases huv : u = v
          · subst huv; simp [G.irrefl]
          · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
            by_cases hlt : u.val < v.val
            · have hgt : ¬(v.val < u.val) := by omega
              simp [hlt, hgt]
            · have hgt : v.val < u.val := by omega
              simp [hlt, hgt]
        rw [h1, h2, hsp]; rfl
      omega
    have hbound : ∀ u : Fin 6, countFin 6 (fun v => !inS u && !inS v && G.adj u v) ≤
        if !inS u then 3 else 0 := by
      intro u; cases hSu : inS u
      · simp only [Bool.not_false, ↓reduceIte, Bool.true_and]
        have h1 : countFin 6 (fun v => !inS v && G.adj u v) ≤ countFin 6 (fun v => !inS v && !decide (v = u)) := by
          apply countFin_mono; intro v hv
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv ⊢
          exact ⟨hv.1, fun h => by subst h; rw [G.irrefl] at hv; cases hv.2⟩
        have hsp := list_countP_add_split (List.finRange 6) (fun v => !inS v) (fun v => decide (v = u))
        have hs1 : (List.finRange 6).countP (fun v => !inS v && decide (v = u)) = 1 := by
          rw [list_countP_eq_of_eq _ _ (fun v => decide (v = u)) (fun v _ => by
            by_cases h : v = u; subst h; simp [hSu]; simp [h])]
          exact countFin_single 6 u
        unfold countFin at hb4_all h1 ⊢; omega
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        have : countFin 6 (fun _ => false) = 0 := (countFin_eq_zero_iff 6 _).mpr (fun _ => rfl)
        omega
    have hstrict : ∀ (l : List (Fin 6)) (f g : Fin 6 → Nat),
        (∀ z ∈ l, f z ≤ g z) → (∃ a ∈ l, f a < g a) → (l.map f).sum < (l.map g).sum := by
      intro l f g hle_l ⟨a, ha, hlt_a⟩
      induction l with
      | nil => simp at ha
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons]
        cases ha with
        | head => have := list_sum_map_le zs f g (fun w hw => hle_l w (List.mem_cons_of_mem a hw)); omega
        | tail _ hm => have := hle_l z (List.mem_cons_self ..); have := ih (fun w hw => hle_l w (List.mem_cons_of_mem z hw)) hm; omega
    have hlt_x' : countFin 6 (fun v => !inS x && !inS v && G.adj x v) < if !inS x then 3 else 0 := by
      conv => rhs; simp only [hx, Bool.not_false, ↓reduceIte]
      omega
    have hlt_sum := hstrict (List.finRange 6) _ _ (fun u _ => hbound u) ⟨x, List.mem_finRange x, hlt_x'⟩
    have hrhs : ((List.finRange 6).map (fun u => if !inS u then 3 else 0)).sum = 12 := by
      rw [list_sum_map_ite_const]
      unfold countFin at hb4_all; omega
    unfold sumFin at hdBB_eq
    omega
  -- Pick the two remaining vertices c1, c2 outside {a1, a2, b1, b2}!
  let inFour : Fin 6 → Bool := fun x =>
    decide (x = a1) || decide (x = a2) || decide (x = b1) || decide (x = b2)
  have hfour_cnt : countFin 6 inFour = 4 := by
    have hnd4 : [a1, a2, b1, b2].Nodup := by
      simp [ha12, Ne.symm hb1_ne_a1, Ne.symm hb1_ne_a2, Ne.symm hb2_ne_a1, Ne.symm hb2_ne_a2, hb12]
    have hle := nodup_length_le_countFin [a1, a2, b1, b2] hnd4 inFour (fun v hv => by
      simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> simp [inFour])
    have hge : countFin 6 inFour ≤ 4 := by
      unfold countFin inFour
      have h1 := list_countP_or_le (List.finRange 6)
        (fun x => decide (x = a1) || decide (x = a2) || decide (x = b1))
        (fun x => decide (x = b2))
      have h2 := list_countP_or_le (List.finRange 6)
        (fun x => decide (x = a1) || decide (x = a2))
        (fun x => decide (x = b1))
      have h3 := list_countP_or_le (List.finRange 6)
        (fun x => decide (x = a1)) (fun x => decide (x = a2))
      have s1 := countFin_single 6 a1; have s2 := countFin_single 6 a2
      have s3 := countFin_single 6 b1; have s4 := countFin_single 6 b2
      unfold countFin at s1 s2 s3 s4; omega
    simp only [List.length_cons, List.length_nil] at hle; omega
  have hrem2 : countFin 6 (fun x => !inFour x) = 2 := by
    have := countFin_add_not 6 inFour; omega
  obtain ⟨c1, c2, hc12, hc_spec⟩ := exists_of_countFin_eq_two _ hrem2
  have hc1_not : inFour c1 = false := by
    have := (hc_spec c1).mpr (Or.inl rfl); simp at this; exact this
  have hc2_not : inFour c2 = false := by
    have := (hc_spec c2).mpr (Or.inr rfl); simp at this; exact this
  have hc1_ne : c1 ≠ a1 ∧ c1 ≠ a2 ∧ c1 ≠ b1 ∧ c1 ≠ b2 := by
    simp only [inFour, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc1_not
    exact ⟨hc1_not.1.1.1, hc1_not.1.1.2, hc1_not.1.2, hc1_not.2⟩
  have hc2_ne : c2 ≠ a1 ∧ c2 ≠ a2 ∧ c2 ≠ b1 ∧ c2 ≠ b2 := by
    simp only [inFour, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc2_not
    exact ⟨hc2_not.1.1.1, hc2_not.1.1.2, hc2_not.1.2, hc2_not.2⟩
  -- Construct the Hamiltonian path [a1, b1, c1, c2, b2, a2]!
  apply hno
  refine ⟨[a1, b1, c1, c2, b2, a2], rfl, ?_, ?_⟩
  · simp [ha12, hb1_ne_a2, hb2_ne_a2, Ne.symm hb1_ne_a1, Ne.symm hb2_ne_a1,
      hb12, hc12, hc1_ne.2.1, hc1_ne.2.2.2, hc2_ne.2.1, hc2_ne.2.2.2,
      Ne.symm hc1_ne.1, Ne.symm hc1_ne.2.2.1, Ne.symm hc2_ne.1, Ne.symm hc2_ne.2.2.1]
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp at hk; omega
    have hb1_B : inS b1 = false := by simp [inS, hb1_ne_a1, hb1_ne_a2]
    have hb2_B : inS b2 = false := by simp [inS, hb2_ne_a1, hb2_ne_a2]
    have hc1_B : inS c1 = false := by simp [inS, hc1_ne.1, hc1_ne.2.1]
    have hc2_B : inS c2 = false := by simp [inS, hc2_ne.1, hc2_ne.2.1]
    rcases hk' with rfl | rfl | rfl | rfl | rfl
    · exact hb1
    · exact hclique b1 c1 hb1_B hc1_B (Ne.symm hc1_ne.2.2.1)
    · exact hclique c1 c2 hc1_B hc2_B hc12
    · exact hclique c2 b2 hc2_B hb2_B hc2_ne.2.2.2
    · rw [G.symm]; exact hb2

/-- Exception 3: `n = 6, i = 3` is impossible. -/
theorem case_n6_i3 (G : SimpleGraph 6)
    (hno : ¬ G.HasHamiltonianPath)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber)
    (hB : 4 ≤ countFin 6 (fun x => decide (G.deg x ≤ 2))) : False := by
  obtain ⟨inS, hS_sub, hS_cnt⟩ := exists_subset_of_countFin_ge _ 4 hB
  have hS_deg : ∀ x : Fin 6, inS x = true → G.deg x ≤ 2 :=
    fun x hx => of_decide_eq_true (hS_sub x hx)
  have hB_cnt : countFin 6 (fun x => !inS x) = 2 := by
    have := countFin_add_not 6 inS; omega
  have hpart := G.edgeCount_partition inS
  have heB_le := G.two_mul_eB_le inS
  let eS := sumFin 6 (fun u => countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v))
  let eB := sumFin 6 (fun u => countFin 6 (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v))
  let degS := sumFin 6 (fun u => if inS u then G.deg u else 0)
  have hdegS_le : degS ≤ 8 := by
    have h1 : degS ≤ sumFin 6 (fun u => if inS u then 2 else 0) :=
      sumFin_le 6 _ _ (fun u => by cases h : inS u; simp; simp [hS_deg u h])
    have h2 : sumFin 6 (fun u => if inS u then 2 else 0) = countFin 6 inS * 2 :=
      list_sum_map_ite_const (List.finRange 6) inS 2
    omega
  have heB_le2 : 2 * eB ≤ 2 := by
    dsimp only at heB_le; rw [hB_cnt] at heB_le; exact heB_le
  have h2e_add := G.two_mul_edge_add_comp
  -- So 2 * compEdgeCount ≥ 30 - (16 + 2 - 2*eS) = 12 + 2*eS!
  have hcomp_lb : 12 + 2 * eS ≤ 2 * G.compEdgeCount := by
    dsimp only at hpart; omega
  have hmu_le := G.two_mul_matchingNumber_le
  have hmu3 : G.matchingNumber = 3 := by omega
  -- Since μ = 3 > 2 = |B|, some matching edge lies inside S, so eS ≥ 1!
  obtain ⟨⟨M, hM, hMlen⟩, _⟩ := G.matchingNumber_spec_aux
  obtain ⟨e0, he0M, he01, he02⟩ := G.matching_edge_in_S inS M hM (by omega)
  have he0_adj : G.adj e0.1 e0.2 = true := hM.1 e0 he0M
  have he0_ne : e0.1 ≠ e0.2 := fun h => by rw [h, G.irrefl] at he0_adj; cases he0_adj
  -- Orient (a1, a2) with a1.val < a2.val
  let a1 := if e0.1.val < e0.2.val then e0.1 else e0.2
  let a2 := if e0.1.val < e0.2.val then e0.2 else e0.1
  have ha12_lt : a1.val < a2.val := by
    have : e0.1.val ≠ e0.2.val := fun h => he0_ne (Fin.ext h)
    by_cases h : e0.1.val < e0.2.val <;> simp [a1, a2, h] <;> omega
  have ha12_ne : a1 ≠ a2 := fun h => by rw [h] at ha12_lt; omega
  have ha1S : inS a1 = true := by by_cases h : e0.1.val < e0.2.val <;> simp [a1, h, he01, he02]
  have ha2S : inS a2 = true := by by_cases h : e0.1.val < e0.2.val <;> simp [a2, h, he01, he02]
  have ha12_adj : G.adj a1 a2 = true := by
    by_cases h : e0.1.val < e0.2.val
    · simp [a1, a2, h, he0_adj]
    · simp [a1, a2, h, G.symm, he0_adj]
  have heS_pos : 1 ≤ eS := by
    have h1 : 1 ≤ countFin 6 (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v) := by
      have hp : 0 < countFin 6 (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v) :=
        (countFin_pos_iff 6 _).mpr ⟨a2, by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨ha12_lt, ha1S⟩, ha2S⟩, ha12_adj⟩⟩
      omega
    have hmem := List.mem_finRange a1
    have hle : ∀ (l : List (Fin 6)) (f : Fin 6 → Nat), a1 ∈ l → f a1 ≤ (l.map f).sum := by
      intro l f hm; induction l with
      | nil => simp at hm
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons]
        cases hm with
        | head => omega
        | tail _ h => have := ih h; omega
    have := hle (List.finRange 6) (fun u => countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v)) hmem
    unfold eS sumFin; omega
  -- Combined with 3 + 2 * compEdgeCount ≤ 18 → 2 * compEdgeCount ≤ 14 → eS = 1 AND degS = 8!
  have heS1 : eS = 1 := by omega
  have hdegS8 : degS = 8 := by dsimp only at hpart; omega
  -- Therefore EVERY vertex x ∈ S has deg x = 2!
  have hall_deg2 : ∀ x : Fin 6, inS x = true → G.deg x = 2 := by
    have h2 := list_sum_eq_const_imp (List.finRange 6) inS G.deg 2
      (fun x _ hx => hS_deg x hx) (by unfold degS sumFin at hdegS8; unfold countFin at hS_cnt; omega)
    intro x hx; exact h2 x (List.mem_finRange x) hx
  -- Moreover (a1, a2) is the UNIQUE unordered edge inside S!
  have huniq_eS : ∀ x y : Fin 6, inS x = true → inS y = true → G.adj x y = true →
      (x = a1 ∧ y = a2) ∨ (x = a2 ∧ y = a1) := by
    intro x y hx hy hxy
    have hne : x ≠ y := fun h => by rw [h, G.irrefl] at hxy; cases hxy
    apply Classical.byContradiction; intro hnot
    -- Orient (x', y') with x'.val < y'.val
    let x' := if x.val < y.val then x else y
    let y' := if x.val < y.val then y else x
    have hxy'_lt : x'.val < y'.val := by
      have : x.val ≠ y.val := fun h => hne (Fin.ext h)
      by_cases h : x.val < y.val <;> simp [x', y', h] <;> omega
    have hx'S : inS x' = true := by by_cases h : x.val < y.val <;> simp [x', h, hx, hy]
    have hy'S : inS y' = true := by by_cases h : x.val < y.val <;> simp [y', h, hx, hy]
    have hxy'_adj : G.adj x' y' = true := by
      by_cases h : x.val < y.val
      · simp [x', y', h, hxy]
      · simp [x', y', h, G.symm, hxy]
    have hpair_ne : (x', y') ≠ (a1, a2) := by
      intro heq
      have h1 : x' = a1 := congrArg Prod.fst heq
      have h2 : y' = a2 := congrArg Prod.snd heq
      by_cases h : x.val < y.val
      · simp [x', y', h] at h1 h2; exact hnot (Or.inl ⟨h1, h2⟩)
      · simp [x', y', h] at h1 h2; exact hnot (Or.inr ⟨h2, h1⟩)
    -- Then eS ≥ 2, contradicting eS = 1!
    have hmem_le_sum : ∀ (l : List (Fin 6)) (f : Fin 6 → Nat) (w : Fin 6), w ∈ l → f w ≤ (l.map f).sum := by
      intro l f w hw; induction l with
      | nil => simp at hw
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons]
        cases hw with | head => omega | tail _ h => have := ih h; omega
    have heS2 : 2 ≤ eS := by
      by_cases hx'a1 : x' = a1
      · have hy'a2 : y' ≠ a2 := fun h => hpair_ne (by rw [hx'a1, h])
        have h2 := nodup_length_le_countFin [a2, y'] (by simp [Ne.symm hy'a2])
          (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v)
          (fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨⟨ha12_lt, ha1S⟩, ha2S⟩, ha12_adj⟩
            · simp only [Bool.and_eq_true, decide_eq_true_eq]
              rw [← hx'a1]
              exact ⟨⟨⟨hxy'_lt, hx'S⟩, hy'S⟩, hxy'_adj⟩)
        have hle := hmem_le_sum (List.finRange 6)
          (fun u => countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v))
          a1 (List.mem_finRange a1)
        simp only [List.length_cons, List.length_nil] at h2
        unfold eS sumFin; omega
      · have h1p : 0 < countFin 6 (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v) :=
          (countFin_pos_iff 6 _).mpr ⟨a2, by
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨⟨ha12_lt, ha1S⟩, ha2S⟩, ha12_adj⟩⟩
        have h2p : 0 < countFin 6 (fun v => decide (x'.val < v.val) && inS x' && inS v && G.adj x' v) :=
          (countFin_pos_iff 6 _).mpr ⟨y', by
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨⟨hxy'_lt, hx'S⟩, hy'S⟩, hxy'_adj⟩⟩
        have hsum2 : ∀ (l : List (Fin 6)) (f : Fin 6 → Nat) (u w : Fin 6), l.Nodup → u ∈ l → w ∈ l → u ≠ w →
            f u + f w ≤ (l.map f).sum := by
          intro l f u w hnd hu hw hne'
          induction l with
          | nil => simp at hu
          | cons z zs ih =>
            rw [List.nodup_cons] at hnd
            simp only [List.map_cons, List.sum_cons]
            by_cases huz : u = z
            · subst huz
              have hw_zs : w ∈ zs := by
                cases hw with | head => exact absurd rfl hne' | tail _ h => exact h
              have := hmem_le_sum zs f w hw_zs; omega
            · have hu_zs : u ∈ zs := by
                cases hu with | head => exact absurd rfl huz | tail _ h => exact h
              by_cases hwz : w = z
              · subst hwz
                have := hmem_le_sum zs f u hu_zs; omega
              · have hw_zs : w ∈ zs := by
                  cases hw with | head => exact absurd rfl hwz | tail _ h => exact h
                have := ih hnd.2 hu_zs hw_zs; omega
        have := hsum2 (List.finRange 6)
          (fun u => countFin 6 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v))
          a1 x' (List.nodup_finRange 6) (List.mem_finRange a1) (List.mem_finRange x') (Ne.symm hx'a1)
        unfold eS sumFin; omega
    omega
  -- Name the 2 vertices of B = {b1, b2} and the 2 remaining vertices of S \ {a1, a2} = {a3, a4}
  obtain ⟨b1, b2, hb12, hb_spec⟩ := exists_of_countFin_eq_two _ hB_cnt
  have hb1_notS : inS b1 = false := by have := (hb_spec b1).mpr (Or.inl rfl); simp at this; exact this
  have hb2_notS : inS b2 = false := by have := (hb_spec b2).mpr (Or.inr rfl); simp at this; exact this
  let inSrem : Fin 6 → Bool := fun x => inS x && !decide (x = a1) && !decide (x = a2)
  have hSrem_cnt : countFin 6 inSrem = 2 := by
    have hsp := list_countP_add_split (List.finRange 6) inS (fun x => decide (x = a1) || decide (x = a2))
    have h1 : (List.finRange 6).countP (fun x => inS x && (decide (x = a1) || decide (x = a2))) = 2 := by
      have heq := list_countP_eq_of_eq (List.finRange 6)
        (fun x => inS x && (decide (x = a1) || decide (x = a2)))
        (fun x => decide (x = a1) || decide (x = a2)) (fun x _ => by
          by_cases h1 : x = a1; subst h1; simp [ha1S]
          by_cases h2 : x = a2; subst h2; simp [ha2S]
          simp [h1, h2])
      rw [heq]
      have hle := nodup_length_le_countFin [a1, a2] (by simp [ha12_ne]) (fun x => decide (x = a1) || decide (x = a2))
        (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> simp)
      have hge : countFin 6 (fun x => decide (x = a1) || decide (x = a2)) ≤ 2 := by
        unfold countFin
        have : (List.finRange 6).countP (fun x => decide (x = a1) || decide (x = a2)) ≤
            (List.finRange 6).countP (fun x => decide (x = a1)) +
            (List.finRange 6).countP (fun x => decide (x = a2)) := by
          induction List.finRange 6 with | nil => simp | cons z zs ih => simp only [List.countP_cons]; cases decide (z = a1) <;> cases decide (z = a2) <;> simp <;> omega
        have s1 := countFin_single 6 a1; have s2 := countFin_single 6 a2; unfold countFin at s1 s2; omega
      unfold countFin at hle hge; simp at hle; omega
    have h2 : countFin 6 inSrem = (List.finRange 6).countP (fun x => inS x && !(decide (x = a1) || decide (x = a2))) := by
      unfold countFin inSrem; apply list_countP_eq_of_eq; intro x _
      cases inS x <;> cases decide (x = a1) <;> cases decide (x = a2) <;> rfl
    unfold countFin at hS_cnt; omega
  obtain ⟨a3, a4, ha34, ha34_spec⟩ := exists_of_countFin_eq_two _ hSrem_cnt
  have ha3_prop : inS a3 = true ∧ a3 ≠ a1 ∧ a3 ≠ a2 := by
    have h := (ha34_spec a3).mpr (Or.inl rfl)
    simp only [inSrem, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have ha4_prop : inS a4 = true ∧ a4 ≠ a1 ∧ a4 ≠ a2 := by
    have h := (ha34_spec a4).mpr (Or.inr rfl)
    simp only [inSrem, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  -- Both a3 and a4 have NO neighbors in S, and deg = 2, so both are adjacent to BOTH b1 and b2!
  have hrem_adj : ∀ z : Fin 6, inS z = true → z ≠ a1 → z ≠ a2 →
      G.adj z b1 = true ∧ G.adj z b2 = true := by
    intro z hzS hz1 hz2
    have hnoS : ∀ w : Fin 6, G.adj z w = true → !inS w = true := by
      intro w hzw
      cases hwS : inS w
      · rfl
      · exfalso
        rcases huniq_eS z w hzS hwS hzw with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hz1 h1
        · exact hz2 h1
    have hdz := hall_deg2 z hzS
    -- Neighbors of z form a subset of {b1, b2} of size 2, hence both b1 and b2 are neighbors!
    have hsubB : ∀ w : Fin 6, G.adj z w = true → w = b1 ∨ w = b2 :=
      fun w hzw => (hb_spec w).mp (hnoS w hzw)
    constructor
    · apply Classical.byContradiction; intro hnot
      have hf : G.adj z b1 = false := by cases h : G.adj z b1; rfl; exact absurd h hnot
      have hle : G.deg z ≤ 1 := by
        have h1 : G.deg z ≤ countFin 6 (fun w => decide (w = b2)) :=
          countFin_mono 6 _ _ (fun w hw => by
            rcases hsubB w hw with rfl | rfl
            · rw [hf] at hw; cases hw
            · simp)
        rw [countFin_single] at h1; exact h1
      omega
    · apply Classical.byContradiction; intro hnot
      have hf : G.adj z b2 = false := by cases h : G.adj z b2; rfl; exact absurd h hnot
      have hle : G.deg z ≤ 1 := by
        have h1 : G.deg z ≤ countFin 6 (fun w => decide (w = b1)) :=
          countFin_mono 6 _ _ (fun w hw => by
            rcases hsubB w hw with rfl | rfl
            · simp
            · rw [hf] at hw; cases hw)
        rw [countFin_single] at h1; exact h1
      omega
  obtain ⟨ha3b1, ha3b2⟩ := hrem_adj a3 ha3_prop.1 ha3_prop.2.1 ha3_prop.2.2
  obtain ⟨ha4b1, ha4b2⟩ := hrem_adj a4 ha4_prop.1 ha4_prop.2.1 ha4_prop.2.2
  -- a1 has deg = 2 and its ONLY neighbor in S is a2, so a1 is adjacent to b1 or b2!
  have ha1_B : G.adj a1 b1 = true ∨ G.adj a1 b2 = true := by
    apply Classical.byContradiction; intro hnone
    have hf1 : G.adj a1 b1 = false := by cases h : G.adj a1 b1; rfl; exact absurd (Or.inl h) hnone
    have hf2 : G.adj a1 b2 = false := by cases h : G.adj a1 b2; rfl; exact absurd (Or.inr h) hnone
    have hle : G.deg a1 ≤ 1 := by
      have h1 : G.deg a1 ≤ countFin 6 (fun w => decide (w = a2)) :=
        countFin_mono 6 _ _ (fun w hw => by
          cases hwS : inS w
          · rcases (hb_spec w).mp (by simp [hwS]) with rfl | rfl
            · rw [hf1] at hw; cases hw
            · rw [hf2] at hw; cases hw
          · rcases huniq_eS a1 w ha1S hwS hw with ⟨_, rfl⟩ | ⟨h1, _⟩
            · simp
            · exact absurd h1 ha12_ne)
      rw [countFin_single] at h1; exact h1
    have := hall_deg2 a1 ha1S
    omega
  -- Distinctness of all 6 vertices (S and B are disjoint!)
  have hdisj_SB : ∀ x y : Fin 6, inS x = true → inS y = false → x ≠ y := by
    intro x y hx hy heq; subst heq; rw [hx] at hy; cases hy
  -- Build Hamiltonian path [a2, a1, b_hit, a3, b_other, a4]!
  apply hno
  rcases ha1_B with ha1b1 | ha1b2
  · refine ⟨[a2, a1, b1, a3, b2, a4], rfl, ?_, ?_⟩
    · simp [Ne.symm ha12_ne, ha34,
        Ne.symm ha3_prop.2.1, Ne.symm ha3_prop.2.2,
        Ne.symm ha4_prop.2.1, Ne.symm ha4_prop.2.2,
        hb12,
        hdisj_SB a2 b1 ha2S hb1_notS, hdisj_SB a2 b2 ha2S hb2_notS,
        hdisj_SB a1 b1 ha1S hb1_notS, hdisj_SB a1 b2 ha1S hb2_notS,
        hdisj_SB a3 b2 ha3_prop.1 hb2_notS,
        (hdisj_SB a3 b1 ha3_prop.1 hb1_notS).symm, (hdisj_SB a4 b1 ha4_prop.1 hb1_notS).symm,
        (hdisj_SB a4 b2 ha4_prop.1 hb2_notS).symm]
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp at hk; omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl
      · rw [G.symm]; exact ha12_adj
      · exact ha1b1
      · rw [G.symm]; exact ha3b1
      · exact ha3b2
      · rw [G.symm]; exact ha4b2
  · refine ⟨[a2, a1, b2, a3, b1, a4], rfl, ?_, ?_⟩
    · simp [Ne.symm ha12_ne, ha34,
        Ne.symm ha3_prop.2.1, Ne.symm ha3_prop.2.2,
        Ne.symm ha4_prop.2.1, Ne.symm ha4_prop.2.2,
        Ne.symm hb12,
        hdisj_SB a2 b1 ha2S hb1_notS, hdisj_SB a2 b2 ha2S hb2_notS,
        hdisj_SB a1 b1 ha1S hb1_notS, hdisj_SB a1 b2 ha1S hb2_notS,
        hdisj_SB a3 b1 ha3_prop.1 hb1_notS,
        (hdisj_SB a3 b2 ha3_prop.1 hb2_notS).symm, (hdisj_SB a4 b2 ha4_prop.1 hb2_notS).symm,
        (hdisj_SB a4 b1 ha4_prop.1 hb1_notS).symm]
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp at hk; omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl
      · rw [G.symm]; exact ha12_adj
      · exact ha1b2
      · rw [G.symm]; exact ha3b2
      · exact ha3b1
      · rw [G.symm]; exact ha4b1

/-- Exception 4: `n = 8, i = 4` is impossible. -/
theorem case_n8_i4 (G : SimpleGraph 8)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber)
    (hB : 5 ≤ countFin 8 (fun x => decide (G.deg x ≤ 3))) : False := by
  obtain ⟨inS, hS_sub, hS_cnt⟩ := exists_subset_of_countFin_ge _ 5 hB
  have hS_deg : ∀ x : Fin 8, inS x = true → G.deg x ≤ 3 :=
    fun x hx => of_decide_eq_true (hS_sub x hx)
  have hB_cnt : countFin 8 (fun x => !inS x) = 3 := by
    have := countFin_add_not 8 inS; omega
  have hpart := G.edgeCount_partition inS
  have heB_le := G.two_mul_eB_le inS
  let eS := sumFin 8 (fun u => countFin 8 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v))
  let eB := sumFin 8 (fun u => countFin 8 (fun v => decide (u.val < v.val) && !inS u && !inS v && G.adj u v))
  let degS := sumFin 8 (fun u => if inS u then G.deg u else 0)
  have hdegS_le : degS ≤ 15 := by
    have h1 : degS ≤ sumFin 8 (fun u => if inS u then 3 else 0) :=
      sumFin_le 8 _ _ (fun u => by cases h : inS u; simp; simp [hS_deg u h])
    have h2 : sumFin 8 (fun u => if inS u then 3 else 0) = countFin 8 inS * 3 :=
      list_sum_map_ite_const (List.finRange 8) inS 3
    omega
  have heB_le6 : 2 * eB ≤ 6 := by
    dsimp only at heB_le; rw [hB_cnt] at heB_le; exact heB_le
  have h2e_add := G.two_mul_edge_add_comp
  -- So 2 * compEdgeCount ≥ 56 - (30 + 6 - 2*eS) = 20 + 2*eS!
  have hcomp_lb : 20 + 2 * eS ≤ 2 * G.compEdgeCount := by
    dsimp only at hpart; omega
  have hmu_le := G.two_mul_matchingNumber_le
  have hmu4 : G.matchingNumber = 4 := by omega
  -- Since μ = 4 > 3 = |B|, some matching edge lies inside S, so eS ≥ 1!
  obtain ⟨⟨M, hM, hMlen⟩, _⟩ := G.matchingNumber_spec_aux
  obtain ⟨e0, he0M, he01, he02⟩ := G.matching_edge_in_S inS M hM (by omega)
  have he0_adj : G.adj e0.1 e0.2 = true := hM.1 e0 he0M
  have he0_ne : e0.1 ≠ e0.2 := fun h => by rw [h, G.irrefl] at he0_adj; cases he0_adj
  let a1 := if e0.1.val < e0.2.val then e0.1 else e0.2
  let a2 := if e0.1.val < e0.2.val then e0.2 else e0.1
  have ha12_lt : a1.val < a2.val := by
    have : e0.1.val ≠ e0.2.val := fun h => he0_ne (Fin.ext h)
    by_cases h : e0.1.val < e0.2.val <;> simp [a1, a2, h] <;> omega
  have ha1S : inS a1 = true := by by_cases h : e0.1.val < e0.2.val <;> simp [a1, h, he01, he02]
  have ha2S : inS a2 = true := by by_cases h : e0.1.val < e0.2.val <;> simp [a2, h, he01, he02]
  have ha12_adj : G.adj a1 a2 = true := by
    by_cases h : e0.1.val < e0.2.val
    · simp [a1, a2, h, he0_adj]
    · simp [a1, a2, h, G.symm, he0_adj]
  have heS_pos : 1 ≤ eS := by
    have h1 : 1 ≤ countFin 8 (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v) := by
      have hp : 0 < countFin 8 (fun v => decide (a1.val < v.val) && inS a1 && inS v && G.adj a1 v) :=
        (countFin_pos_iff 8 _).mpr ⟨a2, by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨ha12_lt, ha1S⟩, ha2S⟩, ha12_adj⟩⟩
      omega
    have hle : ∀ (l : List (Fin 8)) (f : Fin 8 → Nat), a1 ∈ l → f a1 ≤ (l.map f).sum := by
      intro l f hm; induction l with
      | nil => simp at hm
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons]
        cases hm with | head => omega | tail _ h => have := ih h; omega
    have := hle (List.finRange 8) (fun u => countFin 8 (fun v => decide (u.val < v.val) && inS u && inS v && G.adj u v)) (List.mem_finRange a1)
    unfold eS sumFin; omega
  -- 22 ≤ 2 * compEdgeCount ≤ 20: contradiction!
  omega

/-! ## Section 7: Main Theorem (Written on the Wall II — Conjecture 208) -/

theorem main_induction {n : Nat} (hn : 4 ≤ n) :
    ∀ (k : Nat) (G : SimpleGraph n),
      G.compEdgeCount = k →
      G.IsConnected →
      3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber →
      G.HasHamiltonianPath := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro G hk hconn hcond
    apply Classical.byContradiction; intro hno
    letI : Decidable (∀ u v : Fin n, (huv : u ≠ v) → G.adj u v = false →
        (G.addEdge u v huv).HasHamiltonianPath) := Classical.propDecidable _
    by_cases hmax : ∀ u v : Fin n, (huv : u ≠ v) → G.adj u v = false →
        (G.addEdge u v huv).HasHamiltonianPath
    · -- G is edge-maximal non-traceable: apply Chvátal's Extremal Lemma
      obtain ⟨i, hi2, hi_half, hA, hB⟩ := G.chvatal_extremal hn hconn hno hmax
      have hcomp_lb := G.chvatal_compEdge_bound i (by omega) hi_half hA hB
      have hmu_le := G.two_mul_matchingNumber_le
      have h6mu : 6 * G.matchingNumber ≤ 6 * (n / 2) := by omega
      rcases quadratic_dichotomy n i hn hi2 hi_half with hstrict | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · omega
      · exact G.case_n4_i2 hconn hcond hB
      · exact G.case_n6_i2 hconn hno hcond hA hB
      · exact G.case_n6_i3 hno hcond hB
      · exact G.case_n8_i4 hcond hB
    · -- Otherwise some non-edge can be added while keeping G non-traceable
      have hex : ∃ u v : Fin n, ∃ huv : u ≠ v, G.adj u v = false ∧
          ¬ (G.addEdge u v huv).HasHamiltonianPath := by
        apply Classical.byContradiction; intro h
        apply hmax; intro u v huv hnon
        apply Classical.byContradiction; intro hno'
        exact h ⟨u, v, huv, hnon, hno'⟩
      obtain ⟨u, v, huv, hnon, hno'⟩ := hex
      let G' := G.addEdge u v huv
      have hlt : G'.compEdgeCount < k := hk ▸ G.addEdge_compEdgeCount_lt u v huv hnon
      have hconn' : G'.IsConnected := G.addEdge_connected u v huv hconn
      have hmu' : G.matchingNumber ≤ G'.matchingNumber := G.addEdge_matchingNumber_le u v huv
      have hcond' : 3 + 2 * G'.compEdgeCount ≤ 6 * G'.matchingNumber := by omega
      exact hno' (ih G'.compEdgeCount hlt G' rfl hconn' hcond')

end SimpleGraph

namespace Proof

open SimpleGraph

theorem matchingNumber_spec {n : Nat} (G : SimpleGraph n) :
    G.HasMatching G.matchingNumber ∧ ∀ M, G.IsMatching M → M.length ≤ G.matchingNumber :=
  G.matchingNumber_spec_aux

theorem wowii_conjecture_208 {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber) :
    G.HasHamiltonianPath := by
  by_cases h2 : n = 2
  · subst h2; exact G.hamPath_of_n_eq_2 hconn
  · by_cases h3 : n = 3
    · subst h3; exact G.hamPath_of_n_eq_3 hconn
    · exact SimpleGraph.main_induction (by omega) G.compEdgeCount G rfl hconn hcond

theorem wowii_conjecture_208_int {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected)
    (hcond : G.compEdgeCount + 2 ≤ 3 * G.matchingNumber) :
    G.HasHamiltonianPath :=
  wowii_conjecture_208 G hn hconn (by omega)

theorem wowii_conjecture_208_of_matching {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected) (M : List (Fin n × Fin n)) (hM : G.IsMatching M)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * M.length) :
    G.HasHamiltonianPath := by
  have hle := G.matchingNumber_spec_aux.2 M hM
  exact wowii_conjecture_208 G hn hconn (by omega)

end Proof

end WOWII208
