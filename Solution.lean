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

public import WOWII208

/-!
# Solution: Written on the Wall II — Conjecture 208

Supplies complete, zero-`sorry` proofs for all declarations stated in `Challenge.lean`.
All proofs live in `WOWII208.Proof` and use only Lean 4 core (`Init`) with standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

namespace WOWII208

namespace SimpleGraph

variable {n : Nat}

/-- Specification certifying that `G.matchingNumber` is exact: it is attained by a valid
matching of `G` and upper-bounds every valid matching of `G`. -/
theorem matchingNumber_spec (G : SimpleGraph n) :
    G.HasMatching G.matchingNumber ∧ ∀ M, G.IsMatching M → M.length ≤ G.matchingNumber :=
  WOWII208.Proof.matchingNumber_spec G

/-- **Written on the Wall II — Conjecture 208 (Graffiti.pc, Jan 12, 2006).**

If `G` is a simple connected graph on `n > 1` vertices such that
`(1/2) * (1 + (2/3) * |E(Ḡ)|) ≤ μ(G)` (cleared of denominators:
`3 + 2 * |E(Ḡ)| ≤ 6 * μ(G)`), then `G` has a Hamiltonian path. -/
theorem wowii_conjecture_208 {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber) :
    G.HasHamiltonianPath :=
  WOWII208.Proof.wowii_conjecture_208 G hn hconn hcond

/-- Equivalent integer form: if `|E(Ḡ)| + 2 ≤ 3 * μ(G)`, then `G` has a Hamiltonian path. -/
theorem wowii_conjecture_208_int {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected)
    (hcond : G.compEdgeCount + 2 ≤ 3 * G.matchingNumber) :
    G.HasHamiltonianPath :=
  WOWII208.Proof.wowii_conjecture_208_int G hn hconn hcond

/-- Direct matching form: if `G` admits a matching `M` with `3 + 2 * |E(Ḡ)| ≤ 6 * |M|`,
then `G` has a Hamiltonian path. -/
theorem wowii_conjecture_208_of_matching {n : Nat} (G : SimpleGraph n) (hn : 1 < n)
    (hconn : G.IsConnected) (M : List (Fin n × Fin n)) (hM : G.IsMatching M)
    (hcond : 3 + 2 * G.compEdgeCount ≤ 6 * M.length) :
    G.HasHamiltonianPath :=
  WOWII208.Proof.wowii_conjecture_208_of_matching G hn hconn M hM hcond

end SimpleGraph

end WOWII208
