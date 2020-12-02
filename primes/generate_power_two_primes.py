from itertools import count
import random


def is_prime(x):
    if x == 2:
        return True
    elif x < 2:
        return False
    elif x & 1 == 0:
        return False

    for y in range(3, x, 2):
        if x % y == 0:
            return False

    return True


def is_probably_prime(x):
    return miller_rabin(x, 40)


def fermat_test(n, k):
    if n == 2:
        return True

    if n % 2 == 0:
        return False

    for i in range(k):
        a = random.randint(1, n-1)

        if pow(a, n-1) % n != 1:
            return False
    return True


def miller_rabin(n, k):
    if n == 2:
        return True

    if n % 2 == 0:
        return False

    r, s = 0, n - 1
    while s % 2 == 0:
        r += 1
        s //= 2
    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, s, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False

    return True
