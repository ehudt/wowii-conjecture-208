#!/usr/bin/env python3
"""
Independent computational verification of Written on the Wall II — Conjecture 208
(Graffiti.pc / E. DeLaViña, Jan 12, 2006).

Conjecture 208:
  If G is a simple connected graph with n > 1 such that
      (1/2) * (1 + (2/3) * |E(G_bar)|) <= mu(G),
  then G has a Hamiltonian path.

This script performs:
  1. Exhaustive verification over ALL labeled connected graphs on n = 2, 3, 4, 5, 6.
  2. Exhaustive verification over ALL labeled connected graphs on n = 7 with |E(G_bar)| <= 7
     (every graph on n = 7 that can possibly satisfy the hypothesis, since mu(G) <= 3 => |E(G_bar)| <= 7).
  3. Exact verification of the algebraic Chvátal dichotomy for all 4 <= n <= 500.
  4. Sharpness check: explicit non-traceable connected graphs showing the bound is sharp
     or nearly sharp (e.g., n = 6, |E(G_bar)| = 8, mu = 3 => LHS = 19/6 = 3.167 > 3).
"""

from fractions import Fraction
from itertools import combinations


def is_connected(n: int, adj: list[int]) -> bool:
    vis = 1
    fr = 1
    while fr:
        nxt = 0
        while fr:
            lsb = fr & -fr
            u = lsb.bit_length() - 1
            fr ^= lsb
            nxt |= adj[u]
        nxt &= ~vis
        vis |= nxt
        fr = nxt
    return vis == (1 << n) - 1


def has_hamiltonian_path(n: int, adj: list[int]) -> bool:
    full = (1 << n) - 1
    dp = [0] * (1 << n)
    for i in range(n):
        dp[1 << i] = 1 << i
    for mask in range(1, 1 << n):
        ends = dp[mask]
        if not ends:
            continue
        rem = full ^ mask
        while ends:
            lsb = ends & -ends
            u = lsb.bit_length() - 1
            ends ^= lsb
            cand = adj[u] & rem
            while cand:
                b = cand & -cand
                v = b.bit_length() - 1
                cand ^= b
                dp[mask | b] |= b
    return dp[full] != 0


def matching_number(n: int, adj: list[int]) -> int:
    dp = [0] * (1 << n)
    for mask in range(1, 1 << n):
        lsb = mask & -mask
        u = lsb.bit_length() - 1
        rest = mask ^ lsb
        best = dp[rest]
        nbr = adj[u] & rest
        while nbr:
            b = nbr & -nbr
            nbr ^= b
            cand = 1 + dp[rest ^ b]
            if cand > best:
                best = cand
        dp[mask] = best
    return dp[(1 << n) - 1]


def verify_exhaustive_small():
    print("=== 1. Exhaustive verification over ALL labeled connected graphs (n = 2..6) ===")
    for n in range(2, 7):
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        m = len(pairs)
        total_conn = 0
        sat_cond = 0
        violations = 0
        max_non_ham_mu_diff = None
        for mask in range(1 << m):
            adj = [0] * n
            ecount = mask.bit_count()
            ebar = m - ecount
            for idx, (u, v) in enumerate(pairs):
                if (mask >> idx) & 1:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            if not is_connected(n, adj):
                continue
            total_conn += 1
            # Quick check before computing matching/ham path if hypothesis is even possible
            max_possible_mu = n // 2
            lhs = Fraction(1, 2) * (1 + Fraction(2, 3) * ebar)
            if lhs > max_possible_mu:
                continue
            mu = matching_number(n, adj)
            if lhs <= mu:
                sat_cond += 1
                if not has_hamiltonian_path(n, adj):
                    violations += 1
        print(f"  n={n}: connected={total_conn}, satisfying_hypothesis={sat_cond}, violations={violations}")
        assert violations == 0


def verify_exhaustive_n7():
    print("\n=== 2. Exhaustive verification for n = 7 (all graphs with |E(G_bar)| <= 7) ===")
    n = 7
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    m = len(pairs)
    full_adj = [((1 << n) - 1) ^ (1 << i) for i in range(n)]
    tested = 0
    sat_cond = 0
    violations = 0
    for ebar in range(0, 8):
        lhs = Fraction(1, 2) * (1 + Fraction(2, 3) * ebar)
        for missing in combinations(range(m), ebar):
            tested += 1
            adj = full_adj.copy()
            for idx in missing:
                u, v = pairs[idx]
                adj[u] ^= 1 << v
                adj[v] ^= 1 << u
            if not is_connected(n, adj):
                continue
            mu = matching_number(n, adj)
            if lhs <= mu:
                sat_cond += 1
                if not has_hamiltonian_path(n, adj):
                    violations += 1
    print(f"  n=7 (|E(G_bar)| <= 7): total_checked={tested}, satisfying_hypothesis={sat_cond}, violations={violations}")
    assert violations == 0


def verify_algebraic_dichotomy():
    print("\n=== 3. Algebraic verification of Chvátal quadratic dichotomy (4 <= n <= 500) ===")
    exceptions = []
    for n in range(4, 501):
        rhs = 6 * (n // 2) - 4
        for i in range(2, n // 2 + 1):
            lhs = i * (2 * n + 1 - 3 * i)
            if lhs <= rhs:
                exceptions.append((n, i, lhs, rhs))
    print(f"  Exceptions where i*(2n+1-3i) <= 6*floor(n/2)-4: {exceptions}")
    assert [(n, i) for n, i, _, _ in exceptions] == [(4, 2), (6, 2), (6, 3), (8, 4)]


def verify_near_sharpness():
    print("\n=== 4. Near-sharpness witness (n = 6, cut vertex + 3 components of sizes 1, 2, 2) ===")
    # Vertices: 0 (cut vertex), {1}, {2, 3}, {4, 5}. Edges: 0 adjacent to all; (2,3), (4,5).
    n = 6
    edges = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (2, 3), (4, 5)]
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    ebar = n * (n - 1) // 2 - len(edges)
    mu = matching_number(n, adj)
    lhs = Fraction(1, 2) * (1 + Fraction(2, 3) * ebar)
    ham = has_hamiltonian_path(n, adj)
    print(f"  G: n={n}, |E(G)|={len(edges)}, |E(G_bar)|={ebar}, mu(G)={mu}, LHS={lhs} ({float(lhs):.4f}), has_ham_path={ham}")
    assert is_connected(n, adj) and not ham and ebar == 8 and mu == 3 and lhs == Fraction(19, 6)


if __name__ == "__main__":
    verify_exhaustive_small()
    verify_exhaustive_n7()
    verify_algebraic_dichotomy()
    verify_near_sharpness()
    print("\nALL INDEPENDENT CHECKS PASSED.")
