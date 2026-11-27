# Audit & Provenance Report — Written on the Wall II, Conjecture 208

## 1. Conjecture Metadata & Source Fidelity

Source: Live *Written on the Wall II* (Graffiti.pc) database hosted by University of Houston–Downtown (`https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json` and `definitions.json`), fetched November 26, 2026:

```json
{
  "id": 208,
  "status": "open",
  "substatus": "pendingreview",
  "statement": "<p><i>If G is a simple connected graph with n &gt; 1 such that (1/2)*[1 + (2/3)*|E(<span style=\"text-decoration: overline\">G</span>)|] &le; &mu;(G), then G has a Hamiltonian path.</i></p>",
  "comment": [],
  "counterexample-urls": [],
  "date-of-announcement": "Jan 12, 2006",
  "heuristic": "sophie",
  "batch": "Sufficient conditions for Hamiltonian Paths",
  "keywords": [],
  "definitions": [67, 31, 85, 2]
}
```

### Exact Definition Mapping
Every definition referenced by WOWII #208 (`[67, 31, 85, 2]`) matches `WOWII208.lean` verbatim:
- **DEF[67] (`E(G)`):** Edge set of $G$ (unordered pairs of adjacent vertices). Formalized as `SimpleGraph.edgeCount` / `SimpleGraph.compEdgeCount`, counting pairs `(u, v)` with `u.val < v.val`.
- **DEF[31] (`Ḡ`):** Complement graph of $G$ (same vertex set, non-edges of $G$ become edges). Formalized via `!G.adj u v` for `u.val < v.val` in `SimpleGraph.compEdgeCount`.
- **DEF[85] (Hamiltonian path):** A path visiting every vertex of $G$ exactly once. Formalized as `SimpleGraph.HasHamiltonianPath`: `∃ p : List (Fin n), p.length = n ∧ p.Nodup ∧ G.IsWalk p`.
- **DEF[2] (`μ(G)`):** Matching number (maximum number of pairwise vertex-disjoint edges of $G$). Formalized via `SimpleGraph.IsMatching` (`∀ e ∈ M, G.adj e.1 e.2 = true ∧ (M.flatMap (fun e => [e.1, e.2])).Nodup`) and `SimpleGraph.matchingNumber`, together with `matchingNumber_spec` proving it is exact (achieved by a valid matching and bounding all valid matchings).
- **Exact inequality equivalence:** Over integers $e = |E(\overline{G})| \in \mathbb{N}$ and $\mu = \mu(G) \in \mathbb{N}$,
  $$\frac{1}{2}\left(1 + \frac{2}{3}e\right) \le \mu \iff 3 + 2e \le 6\mu \iff e + 2 \le 3\mu.$$
  Both `wowii_conjecture_208` (`3 + 2 * G.compEdgeCount ≤ 6 * G.matchingNumber`) and `wowii_conjecture_208_int` (`G.compEdgeCount + 2 ≤ 3 * G.matchingNumber`), as well as the direct existential matching form `wowii_conjecture_208_of_matching`, are formally proved.

---

## 2. Novelty & Anti-Scooping Check (as of November 26, 2026)

| Source Checked | Result |
|---|---|
| Live UHD *Written on the Wall II* JSON (`wowii/files/conjectures.json`) | Listed as `status: "open"` (`substatus: "pendingreview"`, `comment: []`, zero references/proofs linked). Note: several other `pendingreview` items from 2004–2006 (e.g., #84, #142, #160, #217) remained unpublished for ~20 years and are treated as open by DeepMind `formal-conjectures` and `therefore.academy`. |
| `google-deepmind/formal-conjectures` (repo tree + all open/closed issues & PRs) | No file, issue, or PR exists for WOWII Conjecture 208. |
| Palomar Registry (`palomar-registry.org`) | Entries exist for WOWII #19, #84, #96, #213 (Nov 23, 2026), #291, #399b — **no entry for #208**. |
| `therefore.academy` | No entry for WOWII #208. |
| AI Village / `theaidigest.org` | No proof or mention of WOWII #208. |
| arXiv / Zenodo / ResearchGate / Google Scholar | No published proof or preprint found for WOWII Conjecture 208. |

**Transparency note:** Because UHD's static JSON carries `"substatus": "pendingreview"` (with `comment: []` and no attribution), it is conceivable that someone emailed DeLaViña an unpublished note years ago that was never posted or reviewed. However, no published, archived, or machine-checked proof exists publicly anywhere we could find as of November 26, 2026.

---

## 3. Lean 4 Formal Verification Audit

- **Toolchain:** `leanprover/lean4:v4.36.0` (core `Init` only — **zero Mathlib or external dependencies**).
- **Command:** `lean WOWII208.lean`
- **Exit status:** `0`
- **Errors:** `0`
- **Warnings:** `0`
- **`sorry` / `admit` count:** `0`
- **`axiom` declarations:** `0`
- **`native_decide` / `Lean.ofReduceBool` usage:** `0`
- **Axiom check (`#print axioms`):**
  - `WOWII208.SimpleGraph.wowii_conjecture_208`: `[propext, Classical.choice, Quot.sound]`
  - `WOWII208.SimpleGraph.wowii_conjecture_208_int`: `[propext, Classical.choice, Quot.sound]`
  - `WOWII208.SimpleGraph.wowii_conjecture_208_of_matching`: `[propext, Classical.choice, Quot.sound]`

## 4. Independent Computational Cross-Check (`verify.py`)

- Exhaustively checked all **27,475** labeled connected graphs on $n \in \{2, 3, 4, 5, 6\}$ (`0` violations).
- Exhaustively checked all **198,440** labeled graphs on $n = 7$ with $|E(\overline{G})| \le 7$ (`198,328` satisfying the hypothesis, `0` violations).
- Verified the Chvátal quadratic dichotomy for all $4 \le n \le 500$, confirming that the only four exceptions are $(4, 2), (6, 2), (6, 3), (8, 4)$.
- Confirmed the $n = 6$ near-sharpness witness ($|E(\overline{G})| = 8, \mu = 3$, LHS $= 19/6 \approx 3.167$).
