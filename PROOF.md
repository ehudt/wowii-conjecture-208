# Proof of Written on the Wall II — Conjecture 208

**Conjecture 208** (Graffiti.pc / E. DeLaViña, *Written on the Wall II*, announced January 12, 2006):

> If $G$ is a simple connected graph on $n > 1$ vertices such that
> $$\frac{1}{2}\left(1 + \frac{2}{3}|E(\overline{G})|\right) \le \mu(G),$$
> where $\overline{G}$ is the complement of $G$ and $\mu(G)$ is the matching number of $G$, then $G$ has a Hamiltonian path.

Clearing denominators over $\mathbb{N}$, the hypothesis is equivalent to:
$$3 + 2|E(\overline{G})| \le 6\mu(G) \iff |E(\overline{G})| \le 3\mu(G) - 2.$$

---

## Complete Proof

### 1. Base Cases ($n = 2, 3$)
- For $n = 2$, connectedness forces an edge between the two vertices, giving a Hamiltonian path.
- For $n = 3$, connectedness implies $\delta(G) \ge 1$. Since $\sum_v \deg(v)$ is even and at least $3$, it is at least $4$, so some vertex $b$ has degree $2$ and is adjacent to both other vertices $a, c$, giving the Hamiltonian path $(a, b, c)$.

### 2. Reduction to an Edge-Maximal Non-Traceable Graph ($n \ge 4$)
Assume $n \ge 4$ and suppose for contradiction that $G$ is a counterexample (connected, no Hamiltonian path, and $3 + 2|E(\overline{G})| \le 6\mu(G)$). Choose $G$ with minimum $|E(\overline{G})|$ (equivalently, add missing edges as long as $G$ remains non-traceable; adding an edge preserves connectedness, strictly decreases $|E(\overline{G})|$, and does not decrease $\mu(G)$). Thus $G$ is **edge-maximal non-traceable**: for every non-edge $uv$, the graph $G + uv$ has a Hamiltonian path.

### 3. Chvátal's Extremal Non-Edge Lemma
Since $K_n$ has a Hamiltonian path, $G$ has at least one non-edge. Pick a non-edge $(u, v)$ maximizing $\deg_G(u) + \deg_G(v)$, with $\deg_G(u) \le \deg_G(v)$.

Form $G^+ = G + v^*$ by adding a universal vertex $v^*$ adjacent to all vertices of $G$. Since $G + uv$ has a Hamiltonian path and $G$ does not, that path uses the edge $uv$; splitting it into $L \cdot u$ and $v \cdot R$ and forming
$$Q = (L \cdot u)^{\mathrm{rev}} \cdot v^* \cdot (v \cdot R)^{\mathrm{rev}} = (x_0, x_1, \dots, x_n)$$
yields a Hamiltonian path of $G^+$ with $x_0 = u$ and $x_n = v$.

Define two index sets in $\{0, 1, \dots, n - 1\}$:
$$S_u = \{k : u \sim_{G^+} x_{k+1}\}, \qquad S_v = \{k : x_k \sim_{G^+} v\}.$$
If $k \in S_u \cap S_v$, then $(x_0, \dots, x_k, x_n, x_{n-1}, \dots, x_{k+1})$ is a Hamiltonian cycle of $G^+$; deleting $v^*$ gives a Hamiltonian path of $G$, a contradiction. Hence $S_u \cap S_v = \emptyset$, so
$$(\deg_G(u) + 1) + (\deg_G(v) + 1) = |S_u| + |S_v| \le n \implies \deg_G(u) + \deg_G(v) \le n - 2.$$
Let $i := \deg_G(u) + 1$. Since $G$ is connected and $n > 1$, $\deg_G(u) \ge 1$, so $2 \le i \le \lfloor n/2 \rfloor$.

1. For each $k \in S_u$, we have $k \notin S_v$, so $x_k$ is non-adjacent to $v$ in $G^+$. In particular $x_k \ne v^*$ (as $v^*$ is universal) and $x_k \ne v$ (as $k < n$), so $(x_k, v)$ is a non-edge of $G$. By maximality of $\deg_G(u) + \deg_G(v)$, $\deg_G(x_k) \le \deg_G(u) = i - 1$. Thus the set $A_0 = \{x : \deg_G(x) \le i - 1\}$ has size $|A_0| \ge |S_u| = i$.
2. Every $w \in V(G)$ with $w = u$ or $uw \notin E(G)$ satisfies $\deg_G(w) \le \deg_G(v) \le n - 2 - \deg_G(u) = n - 1 - i$. There are $n - \deg_G(u) = n + 1 - i$ such vertices, so $B_0 = \{x : \deg_G(x) \le n - 1 - i\}$ has size $|B_0| \ge n + 1 - i$.

### 4. Complement-Degree Summation & Quadratic Dichotomy
Since $2i \le n$, we have $A_0 \subseteq B_0$. Every $x \in A_0$ has $\deg_{\overline{G}}(x) \ge n - i = (n - 2i) + i$, and every $x \in B_0 \setminus A_0$ has $\deg_{\overline{G}}(x) \ge i$. Summing over $V(G)$:
$$2|E(\overline{G})| = \sum_{x} \deg_{\overline{G}}(x) \ge |A_0|(n - 2i) + |B_0| \cdot i \ge i(n - 2i) + (n + 1 - i)i = i(2n + 1 - 3i).$$

On the other hand, since any matching has $2\mu(G) \le n$, the hypothesis gives
$$2|E(\overline{G})| \le 6\mu(G) - 4 \le 6\lfloor n/2 \rfloor - 4.$$
Since $f(i) = i(2n + 1 - 3i)$ is concave on $[2, \lfloor n/2 \rfloor]$, $f(i) \ge \min(f(2), f(\lfloor n/2 \rfloor))$:
- $f(2) = 4n - 10 > 6\lfloor n/2 \rfloor - 4$ for all $n \ge 7$ and $n = 5$.
- For odd $n = 2m + 1$ ($m \ge 2$): $f(m) = m^2 + 3m > 6m - 4$ for all $m$.
- For even $n = 2m$ ($m \ge 5$, i.e. $n \ge 10$): $f(m) = m^2 + m \ge 6m > 6m - 4$.

Direct check of $4 \le n \le 9$ shows that $f(i) \le 6\lfloor n/2 \rfloor - 4$ holds **only** for the four pairs:
$$(n, i) \in \{(4, 2),\; (6, 2),\; (6, 3),\; (8, 4)\}.$$

### 5. Eliminating the Four Finite Cases
For any subset $S \subseteq V(G)$ and $B = V(G) \setminus S$, double counting yields
$$2|E(G)| + 2e(S) = 2\sum_{x \in S}\deg_G(x) + 2e(B), \qquad 2e(B) \le |B|(|B| - 1),$$
and if $\mu(G) > |B|$, some matching edge lies inside $S$, forcing $e(S) \ge 1$.

1. **$(n, i) = (4, 2)$:** $|B_0| \ge 3$ vertices have degree $\le 1$, so $2|E(\overline{G})| \ge 6$, forcing $\mu(G) = 2 > 1 \ge |V \setminus B_0|$. Hence a matching edge connects two vertices of degree $\le 1$, forming an isolated $K_2$ component and contradicting connectedness.
2. **$(n, i) = (6, 2)$:** $f(2) = 14$ forces $\mu(G) = 3$ and $|E(\overline{G})| = 7$. Pick two distinct vertices $a_1, a_2 \in A_0$; by connectedness, $\deg(a_1) = \deg(a_2) = 1$ and $a_1 a_2 \notin E(G)$. Let $b_1, b_2$ be their unique neighbors. Because $G$ has a perfect matching ($\mu = 3$), $b_1 \ne b_2$. Applying the edge partition to $S = \{a_1, a_2\}$ gives $2e(B) = 2|E(G)| - 4 = 16 - 4 = 12 = 4 \cdot 3$, so $B = V \setminus \{a_1, a_2\}$ is a clique $K_4$. Naming $B \setminus \{b_1, b_2\} = \{c_1, c_2\}$, the path $(a_1, b_1, c_1, c_2, b_2, a_2)$ is Hamiltonian — contradiction.
3. **$(n, i) = (6, 3)$:** Choose $S \subseteq B_0$ with $|S| = 4$ (every $x \in S$ has $\deg(x) \le 2$) and $|B| = 2$. Then $2|E(\overline{G})| \ge 30 - (16 + 2 - 2e(S)) = 12 + 2e(S)$, which with $2|E(\overline{G})| \le 6\mu - 4$ forces $\mu = 3 > 2 = |B|$, hence $e(S) \ge 1$. Combined with $2|E(\overline{G})| \le 14$, we get $e(S) = 1$ and $\sum_{x \in S}\deg(x) = 8$, so every $x \in S$ has degree **exactly $2$** and $G[S]$ has a unique edge $a_1 a_2$. Let $S \setminus \{a_1, a_2\} = \{a_3, a_4\}$ and $B = \{b_1, b_2\}$. Then $a_3, a_4$ have no neighbors in $S$ and must each be adjacent to both $b_1$ and $b_2$, while $a_1$ has degree $2$ with unique neighbor $a_2$ in $S$, so $a_1$ is adjacent to some $b \in \{b_1, b_2\}$. Letting $b'$ be the other vertex of $B$, $(a_2, a_1, b, a_3, b', a_4)$ is a Hamiltonian path — contradiction.
4. **$(n, i) = (8, 4)$:** Choose $S \subseteq B_0$ with $|S| = 5$ (every $x \in S$ has $\deg(x) \le 3$) and $|B| = 3$. Then $2|E(\overline{G})| \ge 56 - (30 + 6 - 2e(S)) = 20 + 2e(S)$, forcing $\mu = 4 > 3 = |B|$ and hence $e(S) \ge 1$. Thus $2|E(\overline{G})| \ge 22 > 20 = 6(4) - 4$, contradicting the hypothesis. $\blacksquare$

---

## Near-Sharpness
The inequality is nearly sharp at $n = 6$: take a cut vertex $v_0$ adjacent to all five other vertices, plus two disjoint edges on $\{v_2, v_3\}$ and $\{v_4, v_5\}$ (leaving $v_1$ as a pendant leaf). Then $G$ is connected with no Hamiltonian path, $\mu(G) = 3$, and $|E(\overline{G})| = 8$, giving
$$\frac{1}{2}\left(1 + \frac{2}{3} \cdot 8\right) = \frac{19}{6} \approx 3.167 > 3 = \mu(G).$$
Changing $|E(\overline{G})|$ from $8$ to $7$ crosses the threshold $\frac{1}{2}(1 + \frac{14}{3}) = \frac{17}{6} < 3$, and as proved above, every connected graph on $6$ vertices with $|E(\overline{G})| \le 7$ and $\mu(G) = 3$ is traceable.
