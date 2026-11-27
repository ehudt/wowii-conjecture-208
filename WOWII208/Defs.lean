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

/-!
# Core Definitions for Written on the Wall II — Conjecture 208

These definitions match `Challenge.lean` verbatim so that Comparator verifies exact
definitional equality between `Challenge` and `Solution`.
-/

@[expose] public section

namespace WOWII208

/-- Number of elements of `Fin n` satisfying Boolean predicate `P`. -/
def countFin (n : Nat) (P : Fin n → Bool) : Nat :=
  (List.finRange n).countP P

/-- Sum of `f x` over all `x : Fin n`. -/
def sumFin (n : Nat) (f : Fin n → Nat) : Nat :=
  ((List.finRange n).map f).sum

/-- A finite simple undirected graph on vertex set `Fin n`. -/
structure SimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  irrefl : ∀ u, adj u u = false
  symm : ∀ u v, adj u v = adj v u

namespace SimpleGraph

variable {n : Nat}

/-- Number of unordered edges `|E(Ḡ)|` in the complement graph `Ḡ`. -/
def compEdgeCount (G : SimpleGraph n) : Nat :=
  sumFin n (fun u => countFin n (fun v => decide (u.val < v.val) && !G.adj u v))

/-- A list of vertices forms a valid walk in `G` when every consecutive pair is adjacent. -/
def IsWalk (G : SimpleGraph n) (l : List (Fin n)) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length), G.adj l[k] l[k + 1] = true

/-- `G` is connected if every pair of vertices is joined by a nonempty walk. -/
def IsConnected (G : SimpleGraph n) : Prop :=
  ∀ u v : Fin n, ∃ (l : List (Fin n)) (hlen : 0 < l.length),
    G.IsWalk l ∧ l[0]'hlen = u ∧ l[l.length - 1]'(Nat.sub_lt hlen Nat.zero_lt_one) = v

/-- `G` has a Hamiltonian path: a walk of length `n` visiting every vertex of `Fin n` once. -/
def HasHamiltonianPath (G : SimpleGraph n) : Prop :=
  ∃ p : List (Fin n), p.length = n ∧ p.Nodup ∧ G.IsWalk p

/-- A matching is a list of edges of `G` whose endpoints are pairwise distinct. -/
def IsMatching (G : SimpleGraph n) (M : List (Fin n × Fin n)) : Prop :=
  (∀ e ∈ M, G.adj e.1 e.2 = true) ∧ (M.flatMap (fun e => [e.1, e.2])).Nodup

/-- `G` admits a matching of cardinality `k`. -/
def HasMatching (G : SimpleGraph n) (k : Nat) : Prop :=
  ∃ M : List (Fin n × Fin n), G.IsMatching M ∧ M.length = k

/-- Largest `k ≤ m` such that `G` has a matching of size `k`. -/
noncomputable def matchingNumberAux (G : SimpleGraph n) : Nat → Nat
  | 0 => 0
  | k + 1 => open Classical in if G.HasMatching (k + 1) then k + 1 else matchingNumberAux G k

/-- The matching number `μ(G)`: maximum cardinality of a matching of `G`. -/
noncomputable def matchingNumber (G : SimpleGraph n) : Nat :=
  matchingNumberAux G n

end SimpleGraph

end WOWII208
