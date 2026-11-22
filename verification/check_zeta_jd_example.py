"""Reproduce the ordinary class number in the (3, J_d) example using integers."""

from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def reduced_ideal_cycles(discriminant):
    """For the odd fundamental discriminant here, use (b + sqrt(D)) / (2a)."""
    root = isqrt(discriminant)
    ideals = set()
    for b in range(1, root + 1, 2):
        # Reduced means sqrt(D) - b < 2a < sqrt(D) + b.
        first = (root - b) // 2 + 1
        last = (root + b) // 2
        for a in range(first, last + 1):
            c, remainder = divmod(discriminant - b * b, 4 * a)
            if remainder == 0 and gcd(a, b, c) == 1:
                ideals.add((a, b))

    def successor(ideal):
        a, b = ideal
        quotient = (root + b) // (2 * a)
        next_b = 2 * a * quotient - b
        next_a, remainder = divmod(discriminant - next_b * next_b, 4 * a)
        assert remainder == 0
        return next_a, next_b

    assert {successor(ideal) for ideal in ideals} == ideals
    remaining = set(ideals)
    cycles = []
    while remaining:
        start = min(remaining)
        ideal = start
        length = 0
        while ideal in remaining:
            remaining.remove(ideal)
            length += 1
            ideal = successor(ideal)
        assert ideal == start
        cycles.append((start, length))
    return len(ideals), cycles


if __name__ == "__main__":
    q, d, t, e = 43, 325079, 10, 3
    assert prime(q) and prime(d) and d != 3
    assert q % 8 == 3 and d % 16 == 7
    assert all((d + 1) % p == 0 for p in (3, 5, 7, q))
    assert d + 1 == 2**3 * 3**3 * 5 * 7 * q
    assert 2 * t + 1 < min(q, d) and 3 <= e < t and e % 2 == 1
    discriminant = 3 * d
    count, cycles = reduced_ideal_cycles(discriminant)
    assert count == 332
    assert cycles == [((1, 987), 96), ((7, 975), 118), ((7, 985), 118)]
    print(f"D = {discriminant}, reduced ideals = {count}")
    for start, length in cycles:
        print(f"cycle starting at {start}, length = {length}")
    print(f"ordinary class number = {len(cycles)}")
    host_modulus = 16 * q * d
    test_level = (max(192 * host_modulus, 1728) - 1).bit_length()
    assert test_level == 36 and 2 ** (test_level - 1) < 192 * host_modulus <= 2**test_level
    print(f"normalized length = 1; Case II level at dyadic layer two = {test_level}")
