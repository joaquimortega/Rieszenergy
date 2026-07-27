#!/usr/bin/env python3
"""Numerics for the sum of distances of the BEMOC Section 4 point set.

The sum uses ordered pairs, as in ``sum_{i != j}``.  Points on every parallel
have phase zero, matching the convention used in the proof of Theorem 1.8.
The computation is exact up to floating-point roundoff and works ring-by-ring.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import gcd, isqrt, pi

import numpy as np

try:
    from scipy.special import ellipe
except ImportError:  # Only needed for --expected.
    ellipe = None


@dataclass(frozen=True)
class Ring:
    height: float
    count: int


def admissible_parameters(n: int) -> tuple[int, list[int]]:
    """The concrete admissible set in Lemma 1.7 (valid for n >= 16)."""
    if n < 16:
        raise ValueError("the Lemma 1.7 choice is stated for N >= 16")
    m = isqrt(n // 4)
    # isqrt(n // 4) can differ from floor(sqrt(n/4)) only through neither:
    # floor(sqrt(n/4)) = floor(sqrt(n)/2), computed robustly below.
    m = isqrt(n) // 2
    r = [4 * j - 1 for j in range(1, m)]
    r.append(n - 2 * sum(r))
    if not (m <= r[-1] <= 16 * m):
        raise AssertionError("unexpected failure of admissibility")
    return m, r


def bemoc_rings(n: int) -> list[Ring]:
    """Return all occupied parallels in the Section 4 construction."""
    m, north_r = admissible_parameters(n)
    r = north_r + north_r[-2::-1]
    band_count = len(r)  # 2M-1

    # H_0=1 and H_j=1-(2/N) sum_{k<=j} r_k; h_j=(H_{j-1}+H_j)/2.
    cumulative = np.cumsum([0] + r, dtype=np.int64)
    H = 1.0 - 2.0 * cumulative / n
    h = 0.5 * (H[:-1] + H[1:])

    tilde = [0] + [6 * (x // 6) for x in r[1:-1]] + [0]
    rings: list[Ring] = []

    # Mid-band parallels Q_{h_j}.
    for j in range(band_count):
        if j in (0, band_count - 1):
            q = r[j]
        else:
            q = 4 * tilde[j] // 6 + (r[j] - tilde[j])
        if q:
            rings.append(Ring(float(h[j]), q))

    # Shared band-boundary parallels Q_{H_j}, 1 <= j <= 2M-2.
    for j in range(1, band_count):
        q = (tilde[j - 1] + tilde[j]) // 6
        if q:
            rings.append(Ring(float(H[j]), q))

    rings.sort(key=lambda ring: ring.height, reverse=True)
    if sum(ring.count for ring in rings) != n:
        raise AssertionError("ring populations do not sum to N")
    return rings


def _cross_ring_sum(a: Ring, b: Ring) -> float:
    """Unordered sum between two aligned, equally spaced rings."""
    q, r = a.count, b.count
    g = gcd(q, r)
    period = q * r // g
    theta = 2.0 * pi * np.arange(period, dtype=float) / period
    rho_a = np.sqrt(max(0.0, 1.0 - a.height * a.height))
    rho_b = np.sqrt(max(0.0, 1.0 - b.height * b.height))
    distance = np.sqrt(
        np.maximum(
            0.0,
            2.0 - 2.0 * (a.height * b.height + rho_a * rho_b * np.cos(theta)),
        )
    )
    return float(g * distance.sum())


def _within_ring_sum(ring: Ring) -> float:
    """Unordered sum within one ring."""
    q = ring.count
    if q < 2:
        return 0.0
    rho = np.sqrt(max(0.0, 1.0 - ring.height * ring.height))
    k = np.arange(1, q, dtype=float)
    # Each angular difference occurs q times as an ordered pair.
    ordered = q * np.sum(2.0 * rho * np.sin(pi * k / q))
    return float(ordered / 2.0)


def one_energy(n: int) -> float:
    """Compute sum_{i != j} ||x_i-x_j|| for the BEMOC points."""
    rings = bemoc_rings(n)
    unordered = sum(_within_ring_sum(ring) for ring in rings)
    for i, a in enumerate(rings):
        for b in rings[i + 1 :]:
            unordered += _cross_ring_sum(a, b)
    return 2.0 * unordered


def expected_one_energy(n: int) -> float:
    """Expected energy when the phases of distinct rings are independent.

    The interaction of two different rings is integrated analytically using
    the complete elliptic integral of the second kind.  Interactions within a
    ring are unchanged by its phase.
    """
    if ellipe is None:
        raise RuntimeError("scipy is required for --expected")
    rings = bemoc_rings(n)
    unordered = sum(_within_ring_sum(ring) for ring in rings)
    for i, a in enumerate(rings):
        rho_a = np.sqrt(max(0.0, 1.0 - a.height * a.height))
        for b in rings[i + 1 :]:
            rho_b = np.sqrt(max(0.0, 1.0 - b.height * b.height))
            A = 2.0 - 2.0 * a.height * b.height
            B = 2.0 * rho_a * rho_b
            mean_distance = (2.0 / pi) * np.sqrt(A + B) * ellipe(2.0 * B / (A + B))
            unordered += a.count * b.count * mean_distance
    return 2.0 * unordered


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("N", nargs="+", type=int, help="one or more degrees")
    parser.add_argument(
        "--expected", action="store_true",
        help="average over independent uniform phases on the parallels",
    )
    args = parser.parse_args()
    print("N,rings,energy,deficit,deficit/sqrt(N),deficit/N")
    for n in args.N:
        energy = expected_one_energy(n) if args.expected else one_energy(n)
        deficit = (4.0 / 3.0) * n * n - energy
        print(
            f"{n},{len(bemoc_rings(n))},{energy:.12g},{deficit:.12g},"
            f"{deficit/np.sqrt(n):.12g},{deficit/n:.12g}"
        )


if __name__ == "__main__":
    main()
