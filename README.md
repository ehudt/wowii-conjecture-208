# Formal Proof of *Written on the Wall II* — Conjecture 208

A zero-dependency, machine-checked **Lean 4** proof of **Conjecture 208** from Ermelinda DeLaViña's *Written on the Wall II* (Graffiti.pc, announced January 12, 2006; listed `status: open`).

> **Theorem (WOWII Conjecture 208).** If $G$ is a simple connected graph on $n > 1$ vertices such that
> $$\frac{1}{2}\left(1 + \frac{2}{3}|E(\overline{G})|\right) \le \mu(G),$$
> then $G$ has a Hamiltonian path.

Equivalently, clearing denominators over $\mathbb{N}$: $3 + 2\,|E(\overline{G})| \le 6\,\mu(G)$, or $|E(\overline{G})| + 2 \le 3\,\mu(G)$.

---

## Verify in 15 Seconds (Zero Dependencies)

No Mathlib download, no external packages, no `sorry` in the proof, no `native_decide` — just bare Lean 4 core (`v4.36.0`):

```bash
lake build
```

Verify axioms on `Solution`:

```bash
lake env lean --stdin <<'EOF'
import Solution
#print axioms WOWII208.SimpleGraph.matchingNumber_spec
#print axioms WOWII208.SimpleGraph.wowii_conjecture_208
#print axioms WOWII208.SimpleGraph.wowii_conjecture_208_int
#print axioms WOWII208.SimpleGraph.wowii_conjecture_208_of_matching
EOF
```

Expected output (standard axioms only):

```text
'WOWII208.SimpleGraph.matchingNumber_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'WOWII208.SimpleGraph.wowii_conjecture_208' depends on axioms: [propext, Classical.choice, Quot.sound]
'WOWII208.SimpleGraph.wowii_conjecture_208_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'WOWII208.SimpleGraph.wowii_conjecture_208_of_matching' depends on axioms: [propext, Classical.choice, Quot.sound]
```

And to run the independent Python exhaustive cross-check ($n = 2..7$, 225,915 graphs + algebraic dichotomy):

```bash
python3 verify.py
```

---

## Repository Map (Palomar Registry Layout)

| File | Description |
|---|---|
| [`Challenge.lean`](Challenge.lean) | Small, human-auditable statement surface (125 lines, Lean 4 core only, deliberate `sorry`s for Comparator). |
| [`Solution.lean`](Solution.lean) | Connects the advertised declarations to the completed proof (0 `sorry`, standard axioms only). |
| [`WOWII208/Defs.lean`](WOWII208/Defs.lean) | Verbatim copy of the Challenge definitions. |
| [`WOWII208/Proof.lean`](WOWII208/Proof.lean) | Complete, self-contained proof development (zero external imports). |
| [`comparator.json`](comparator.json) | Comparator config for Palomar kernel & NanoDa/con-ron verification. |
| [`formalization.yaml`](formalization.yaml) | Palomar v0.4 provenance, metadata, and AI-automation disclosure. |
| [`PROOF.md`](PROOF.md) | Concise human-readable mathematical proof. |
| [`verify.py`](verify.py) | Independent Python exhaustive verifier ($n \le 7$) and near-sharpness witness. |
| [`AUDIT.md`](AUDIT.md) | Source provenance, definition audit, and novelty check (as of Nov 26–27, 2026). |
| [`VERIFICATION_LOG.txt`](VERIFICATION_LOG.txt) | Verbatim `lake build`, axiom audit, and Python verification logs. |
| [`LICENSE`](LICENSE) | Apache License 2.0. |

---

## Proof Sketch (30-Second Version)

1. $n = 2, 3$ follow immediately from connectedness.
2. For $n \ge 4$, pass by strong induction on $|E(\overline{G})|$ to an edge-maximal non-traceable supergraph $G$ (adding edges preserves connectedness, strictly lowers $|E(\overline{G})|$, and never decreases $\mu(G)$).
3. Take a non-edge $(u, v)$ maximizing $\deg(u) + \deg(v)$ with $\deg(u) \le \deg(v)$ and set $i = \deg(u) + 1$. Via the universal-vertex extension $G^+ = G + v^*$ and Pósa flipping, $2 \le i \le \lfloor n/2 \rfloor$, at least $i$ vertices have degree $\le i - 1$, and at least $n + 1 - i$ vertices have degree $\le n - 1 - i$.
4. Summing complement degrees gives $2|E(\overline{G})| \ge i(2n + 1 - 3i)$, which already beats $6\lfloor n/2 \rfloor - 4 \ge 6\mu(G) - 4$ for every odd $n \ge 5$, every even $n \ge 10$, and $(n, i) = (8, 3)$.
5. The four remaining pairs $(4, 2), (6, 2), (6, 3), (8, 4)$ collapse directly via matching size and explicit 6-vertex Hamiltonian paths.
