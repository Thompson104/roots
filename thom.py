#!/usr/bin/env python3

"""
    Propositions, Notations and Algorithms numbering is based on the numbering
    from the book *Algorithms in Real Algebraic Geometry (2016)* by Basu,
    Pollack and Roy.
"""

import itertools
import functools
import operator
from collections import Counter
from sympy import Poly
from sympy import Symbol
from sympy import rem
from sympy import prod
from sympy import sign
from sympy import linsolve
from sympy import Matrix
from sympy import resultant
from sympy import LC
from sympy import ZZ, QQ


def pretty(M):
    """
        Useful tool to print {0,1,-1} matrices.

        >>> pretty([[0,-1],[-1,1]])
         0 -1
        -1  1

    """

    print(*map(lambda x: " ".join(("{:2d}", )
                                  * len(x)).format(*x), M), sep='\n')


def Res(P, Q, *gens, **args):
    """
        Computes the resultant of the input polynomials P and Q.

        >>> from sympy.abc import x
        >>> Res( x**2 + 1 , x**2 - 1)
        4

    """

    return resultant(P, Q, *gens, **args)


def lcof(P):
    """
        Returns the leading coefficient of the input polynomial.

        >>> lcof( 0 )
        0
        >>> lcof(1)
        1
        >>> from sympy import Poly
        >>> from sympy.abc import x
        >>> lcof( Poly( x**2 ) )
        1
        >>> lcof( Poly( x**16 ).div(Poly( 3*x**9 ))[0] )
        1/3

    """

    if type(P) is int:
        return P

    return LC(P)


def deg(P):
    """
        Returns the degree of the input polynomial.

        >>> deg(0)
        0
        >>> deg(1)
        0
        >>> from sympy import Poly, Symbol
        >>> from sympy.abc import x
        >>> deg( Poly( x**2 ) )
        2
        >>> deg( Poly( x**16 ).div(Poly( 3*x**9 ))[0] )
        7

    """

    if type(P) is int:
        return 0

    return max(0, P.degree())


def cof(j, P):
    """
        Returns the degree of the input polynomial.

        >>> cof(0,0)
        0
        >>> cof(0,1)
        1
        >>> cof(17,1)
        0
        >>> from sympy import Poly, Symbol
        >>> from sympy.abc import x
        >>> cof( 2 , Poly( x**2 + 2*x ) )
        1
        >>> cof( 1 , Poly( x**2 + 2*x ) )
        2
        >>> cof( 7 , Poly( x**16 ).div(Poly( 3*x**9 ))[0] )
        1/3
        >>> cof( 8 , Poly( x**16 ).div(Poly( 3*x**9 ))[0] )
        0
        >>> cof(-1,0)
        Traceback (most recent call last):
            ...
        Exception: index -1 out of range for 0

    """

    if j < 0:
        raise Exception('index {} out of range for {}'.format(j, P))

    if type(P) is int:

        return P if j == 0 else 0

    else:

        return P.all_coeffs()[-j - 1] if j <= P.degree() else 0


def Rem(P, Q):
    """

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P=Poly( x**3 - 2*x**2 - 4 , domain=QQ )
        >>> Q=Poly( x - 3 , domain = QQ )
        >>> Rem(P,Q)
        Poly(5, x, domain='QQ')

    """

    return rem(P, Q)


def ub(P):
    """
        Computes on upper bound on the values of the real roots of P.

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> f = x**2 - 1
        >>> P = Poly( f , x , domain=QQ)
        >>> ub( P )
        4

    """

    a = P.coeffs()
    return 2 * sum(map(abs, a)) / abs(a[0])


def lb(P):
    """
        Computes a lower bound on the values of the real roots of P.

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> f = x**2 - 1
        >>> P = Poly( f , x , domain=QQ)
        >>> lb( P )
        -4

    """

    return -ub(P)


def PTE(s, r):
    """
        Proposition 2.37 (Thom encoding).

        >>> PTE((0, -1, 1),(0, 1, 1))
        -1
        >>> PTE((0, 1, 1),(0, -1, 1))
        1
        >>> PTE((0, -1, 1),(0, -1, 1))
        0
        >>> PTE((0, 1, 1),(0, 1, 1))
        0

        >>> PTE((0,1,-1,1),(0,-1,0,1))
        -1
        >>> PTE((0,-1,0,1),(0,1,-1,1))
        1
        >>> PTE((0,-1,0,1),(0,1,1,1))
        -1
        >>> PTE((0,1,1,1),(0,-1,0,1))
        1

        >>> PTE((0,1,-1,1),(0,-1,1,1))
        -1
        >>> PTE((0,-1,1,1),(0,1,-1,1))
        1
        >>> PTE((0,-1,1,1),(0,1,1,1))
        -1
        >>> PTE((0,1,1,1),(0,-1,1,1))
        1

        >>> PTE((0,1,-1,1),(0,-1,-1,1))
        -1
        >>> PTE((0,-1,-1,1),(0,1,-1,1))
        1
        >>> PTE((0,-1,-1,1),(0,1,1,1))
        -1
        >>> PTE((0,1,1,1),(0,-1,-1,1))
        1

        >>> PTE((0,1,-1,1),(0,1,1,1))
        -1
        >>> PTE((0,1,1,1),(0,1,-1,1))
        1

    """

    d = len(s)

    if d != len(r):
        raise Exception('sign conditions must have the same length')

    if not all(map(frozenset([0, -1, 1]).__contains__, s)):
        raise Exception('s={} contains an intruder'.format(s))

    if not all(map(frozenset([0, -1, 1]).__contains__, r)):
        raise Exception('r={} contains an intruder'.format(r))

    if s == r:
        if s[0] == r[0] == 0:
            return 0
        else:
            raise Exception(
                'not roots but same sign conditions, cannot compare')

    else:
        k = 1
        while k <= d:
            if s[d - k] != r[d - k]:
                break
            k += 1

        if s[d - k + 1] == 1:
            return 1 if s[d - k] > r[d - k] else -1

        else:
            return 1 if s[d - k] < r[d - k] else -1


def Der(P):
    """
        Returns all the derivatives of P in a tuple.

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> f = x**2 - 1
        >>> P = Poly( f , x , domain=QQ)
        >>> Der( P )
        (Poly(x**2 - 1, x, domain='QQ'), Poly(2*x, x, domain='QQ'), Poly(2, x, domain='QQ'))

    """

    return tuple(P.diff((0, d)) for d in range(P.degree() + 1))


def eps(i):
    """

        >>> tuple(map(eps, range(1, 11)))
        (1, -1, -1, 1, 1, -1, -1, 1, 1, -1)

    """

    if i < 1:
        raise Exception('i must be greater or equal to 1, got {}'.format(i))

    if i not in ZZ:
        raise Exception('i must be in ZZ, got {}'.format(i))

    # SLOW IMPLEMENTATION
    # return (-1)**( ( i * ( i - 1 ) ) // 2 )

    if i % 4 == 0 or i % 4 == 1:
        return 1

    else:
        return -1


def NGPmV(s):
    """
        Notation 4.30 (Generalized Permanences minus Variations).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P1 = Poly( x , x , domain=QQ)
        >>> NGPmV(SSC(P1, P1.diff()))
        1
        >>> P2 = Poly( x**2 , x , domain=QQ)
        >>> NGPmV(SSC(P2, P2.diff()))
        1
        >>> P3 = Poly( x**3 , x , domain=QQ)
        >>> NGPmV(SSC(P3, P3.diff()))
        1
        >>> P4 = Poly( x**2 - 1 , x , domain=QQ)
        >>> NGPmV(SSC(P4, P4.diff()))
        2

    """

    p = len(s) - 1

    if s[p] == 0:
        raise Exception('s[p] must be nonzero, got {}'.format(s[p]))

    q = p - 1

    while q >= 0 and s[q] == 0:
        q -= 1

    if q < 0:
        return 0

    _s = s[:q + 1]

    if (p - q) % 2 == 1:

        return NGPmV(_s) + eps(p - q) * sign(s[p] * s[q])

    else:

        return NGPmV(_s)


def AGPmV(s):
    """
        Algorithm 9.4 (Generalized Permanences minus Variations).

        =========
        Structure
        =========

        An ordered integral domain D.

        =====
        Input
        =====

        The input s = s[0],...,s[p] is a finite list of elements in D such that
        s[p] != 0.

        ======
        Output
        ======

        PmV(s).

        ==========
        Complexity
        ==========

        O(p).

        =========
        Procedure
        =========

        1. Initialize n to 0.
        2. Compute the number l of non-zero elements of s and define the list
        (s′(1), m(1)),...,(s′(l), m(l)) = (s[p],p), (s[q],q),..., of non-zero
        elements of s with their index.
        3. For every i from 1 to l - 1, if m(i) - m(i + 1) is odd:
            3.1. n := n + eps(m(i)−m(i+1)) sign(s′(i) s′(i + 1)).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P1 = Poly( x , x , domain=QQ)
        >>> AGPmV(SSC(P1, P1.diff()))
        1
        >>> P2 = Poly( x**2 , x , domain=QQ)
        >>> AGPmV(SSC(P2, P2.diff()))
        1
        >>> P3 = Poly( x**3 , x , domain=QQ)
        >>> AGPmV(SSC(P3, P3.diff()))
        1
        >>> P4 = Poly( x**2 - 1 , x , domain=QQ)
        >>> AGPmV(SSC(P4, P4.diff()))
        2

    """

    n = 0

    sp, m = zip(*((x, i) for (i, x) in reversed(list(enumerate(s))) if x != 0))

    l = len(sp)

    for i in range(l - 1):
        d = m[i] - m[i + 1]
        if d % 2 == 1:
            n += eps(d) * sign(sp[i] * sp[i + 1])

    return n


def SSP(P, Q):
    """
        Algorithm 8.76 (Signed Subresultant Polynomials).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import a, b, c, x
        >>> f = x**4 + a * x**2 + b * x + c
        >>> P = Poly(f, x, domain=QQ[a, b, c])
        >>> tuple(reversed(SSP(P, P.diff())))
        (Poly(x**4 + a*x**2 + b*x + c, x, domain='QQ[a,b,c]'), \
Poly(4*x**3 + 2*a*x + b, x, domain='QQ[a,b,c]'), \
Poly(-8*a*x**2 - 12*b*x - 16*c, x, domain='QQ[a,b,c]'), \
Poly((-8*a**3 + 32*a*c - 36*b**2)*x - 4*a**2*b - 48*b*c, x, domain='QQ[a,b,c]'), \
Poly(16*a**4*c - 4*a**3*b**2 - 128*a**2*c**2 + 144*a*b**2*c - 27*b**4 + 256*c**3, x, domain='QQ[a,b,c]'))

        >>> f = x**4 + a * x**2 + b * x + c
        >>> P = Poly(f, x, domain=QQ[a, b, c])
        >>> SSP(P, P.diff().diff())
        (Poly(400*a**4 - 5760*a**2*c + 3456*a*b**2 + 20736*c**2, x, domain='QQ[a,b,c]'), \
Poly(1728*b*x - 240*a**2 + 1728*c, x, domain='QQ[a,b,c]'), \
Poly(-144*x**2 - 24*a, x, domain='QQ[a,b,c]'), \
Poly(12*x**2 + 2*a, x, domain='QQ[a,b,c]'), \
Poly(x**4 + a*x**2 + b*x + c, x, domain='QQ[a,b,c]'))

        >>> f = x**4 + b * x + c
        >>> P = Poly(f, x, domain=QQ[b, c])
        >>> tuple(reversed(SSP(P, P.diff())))
        (Poly(x**4 + b*x + c, x, domain='QQ[b,c]'), \
Poly(4*x**3 + b, x, domain='QQ[b,c]'), \
Poly(-12*b*x - 16*c, x, domain='QQ[b,c]'), \
Poly(-36*b**2*x - 48*b*c, x, domain='QQ[b,c]'), \
Poly(-27*b**4 + 256*c**3, x, domain='QQ[b,c]'))

    """

    # print( 'SSP' , P , Q )

    p = deg(P)
    q = deg(Q)

    if p <= q:
        raise Exception(
            'P must have strictly larger degree than Q. Got p = {}, q = {}.'.format(
                p, q))

    sResP = [None] * (p + 1)
    s = [None] * (p + 1)
    t = [None] * (p + 1)

    sResP[p] = P
    s[p] = t[p] = 1
    sResP[p - 1] = Q
    bq = cof(q, Q)
    t[p - 1] = bq
    sResP[q] = eps(p - q) * bq**(p - q - 1) * Q
    s[q] = eps(p - q) * bq**(p - q)

    for l in range(q + 1, p - 1):
        sResP[l] = s[l] = 0

    i = p + 1
    j = p

    while sResP[j - 1] != 0:

        k = sResP[j - 1].degree()

        if k < 1:
            break

        if k == j - 1:

            s[j - 1] = t[j - 1]
            sResP[k - 1] = -Rem(sResP[i - 1].mul_ground(s[j - 1]**2),
                                sResP[j - 1]).div(s[j] * t[i - 1])[0]

        elif k < j - 1:
            s[j - 1] = 0

            for d in range(1, j - k):

                t[j - d - 1] = (-1)**d * (t[j - 1] * t[j - d]) / s[j]

            s[k] = t[k]
            sResP[k] = sResP[j - 1].mul_ground(s[k] / t[j - 1])

            # typo in book, says k + 1 instead of k - 1
            for l in range(j - 2, k):
                sResP[l] = s[l] = 0

            sResP[k - 1] = -Rem(sResP[i - 1].mul_ground(t[j - 1]
                                                        * s[k]), sResP[j - 1]).div(s[j] * t[i - 1])[0]

        t[k - 1] = lcof(sResP[k - 1])

        i = j
        j = k

    for l in range(0, j - 1):
        sResP[l] = s[l] = 0

    return tuple(sResP)


def SSC(P, Q):
    """
        Algorithm 8.77 (Signed Subresultant Coefficients).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> f = 9 * x**13 - 18 * x**11 - 33 * x**10 + 102 * x**8 + 7 * x**7 \
- 36 * x**6 - 122 * x**5 + 49 * x**4 + 93 * x**3 - 42 * x**2 - 18 * x + 9
        >>> P = Poly(f, x, domain=QQ)
        >>> tuple(reversed(SSC(P, P.diff())))[:9]
        (9, 117, 37908, -72098829, -666229317948, -1663522740400320, \
-2181968897553243072, -151645911413926622112, \
-165117711302736225120)

    """
    sResP = SSP(P, Q)
    sRes = tuple(cof(i, sResPi) for (i, sResPi) in enumerate(sResP))
    return sRes


def UTQ(Q, P):
    """
        Algorithm 9.7 (Univariate Tarski-Query).

        UTQ(Q,P) = sum(Q(x) for x in Zer(P))

        C0 = len(list(x for x in Zer(P) if Q(x) == 0))
        C- = len(list(x for x in Zer(P) if Q(x) < 0))
        C+ = len(list(x for x in Zer(P) if Q(x) > 0))

        UTQ(Q,P) = C+ - C-
        UTQ(Q**2,P) = C+ + C-
        UTQ(1,P) = C0 + C+ + C-

         / 1  1  1 \   / c0 \     / UTQ( 1 , P )    \
        |  0  1 -1  | |  c+  | = |  UTQ( Q , P )     |
         \ 0  1  1 /   \ c- /     \ UTQ( Q**2 , P ) /

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly(2*x + 1, x, domain=QQ)
        >>> UTQ(P,P)
        0
        >>> P = Poly(x**2 - 2*x + 1, x, domain=QQ)
        >>> UTQ(P,P)
        0
        >>> P = Poly(x**3, x, domain=QQ)
        >>> UTQ(P,P)
        0
        >>> Q = Poly(7, x, domain=QQ)
        >>> UTQ(Q, P)
        1
        >>> Q = Poly(-7, x, domain=QQ)
        >>> UTQ(Q, P)
        -1
        >>> Q = Poly(0, x, domain=QQ)
        >>> UTQ(Q, P)
        0

    """

    if P == 0:

        raise Exception('P must be nonzero, got {}'.format(P))

    if Q == 0:

        # raise Exception('Q must be nonzero, got {}'.format(Q))
        return 0

    q = deg(Q)

    if q == 0:

        b0 = cof(0, Q)

        sRes = SSC(P, P.diff())
        PmV = AGPmV(sRes)

        return PmV if b0 > 0 else -PmV

    elif q == 1:

        b1 = cof(1, Q)
        b0 = cof(0, Q)

        p = deg(P)
        S = (P.mul_ground(p * b1) - P.diff().mul(Q)).mul(sign(b1))

        sRes = SSC(P, S)
        PmV = AGPmV(sRes)

        return PmV

    else:

        sRes = SSC(-P.diff().mul(Q), P)
        PmV = AGPmV(sRes)

        if (q - 1) % 2 == 1:
            bq = cof(q, Q)
            return PmV + sign(bq)

        else:
            return PmV


def A(S, T):

    T = tuple(T)

    for s in S:
        for t in T:
            yield s + (t,)


def X(S, T):

    T = tuple(T)

    if not S[0]:
        return (T, )

    # transpose the transpose

    return tuple(zip(*[s + (t,) for s in zip(*S) for t in T]))


def T(M1, n1, m1, M2, n2, m2):
    """
        Notation 2.83 (Modified Tensor Product)
    """

    n = n1 * n2
    m = m1 * m2

    M = [[None for j in range(m)] for i in range(n)]

    for i1 in range(n1):
        for j1 in range(m1):
            for i2 in range(n2):
                for j2 in range(m2):
                    M[n1 * i2 + i1][m2 * j1 + j2] = M1[i1][j1] * M2[i2][j2]

    return M


def TMS(s):
    """
        Notation 2.86 (Total matrix of signs).

        >>> pretty(TMS(1))
         1  1  1
         0  1 -1
         0  1  1
        >>> pretty(TMS(2))
         1  1  1  1  1  1  1  1  1
         0  0  0  1  1  1 -1 -1 -1
         0  0  0  1  1  1  1  1  1
         0  1 -1  0  1 -1  0  1 -1
         0  0  0  0  1 -1  0 -1  1
         0  0  0  0  1 -1  0  1 -1
         0  1  1  0  1  1  0  1  1
         0  0  0  0  1  1  0 -1 -1
         0  0  0  0  1  1  0  1  1

    """

    if s < 1:
        raise Exception("s must be positive, got {}".format(s))

    M1 = (
        (1, 1, 1),
        (0, 1, -1),
        (0, 1, 1),
    )

    if s == 1:

        return M1

    else:

        return T(TMS(s - 1), 3**(s - 1), 3**(s - 1), M1, 3, 3)


def NSD(Z, P, TaQ=None, mul=operator.mul):
    """
        Algorithm 10.72 (Naive Sign Determination).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly(x**2, x, domain=QQ)
        >>> NSD(P, Der(P), TaQ=UTQ, mul=mulmod(P))
        ((0, 0, 1),)
        >>> P = Poly(-x**2, x, domain=QQ)
        >>> NSD(P, Der(P), TaQ=UTQ, mul=mulmod(P))
        ((0, 0, -1),)
        >>> P = Poly(x**2 - 4, x, domain=QQ)
        >>> sorted(NSD(P, Der(P), TaQ=UTQ, mul=mulmod(P)))
        [(0, -1, 1), (0, 1, 1)]
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 5), x, domain=QQ)
        >>> NSD(Q, Der(P), TaQ=UTQ, mul=mulmod(Q))
        ((1, 1, 1),)
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 2), x, domain=QQ)
        >>> NSD(Q, Der(P), TaQ=UTQ, mul=mulmod(Q))
        ((-1, 0, 1),)
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 0), x, domain=QQ)
        >>> NSD(Q, Der(P), TaQ=UTQ, mul=mulmod(Q))
        ((1, -1, 1),)

    """

    if TaQ is None:
        raise Exception('Missing Tarski-query black-box implementation')

    if not P:
        raise Exception('P must be non-empty, got {}.'.format(P))

    prod = lambda iterable: functools.reduce(mul, iterable, 1)

    P = list(reversed(P))
    s = len(P)

    Ms = TMS(s)
    Sigma = tuple(itertools.product((0, 1, -1), repeat=s))
    A = tuple(itertools.product((0, 1, 2), repeat=s))

    # pretty( Ms )
    # print( Sigma )
    # print( A )

    TaQ_PA_Z = []
    for a in A:
        # print(' * '.join('P[{}]^{}'.format(i,a[i]) for i in range(s)))
        t = TaQ(prod(P[i]**a[i] for i in range(s)), Z)
        TaQ_PA_Z.append(t)

    # print( TaQ_PA_Z )

    # print( TaQ_PA_Z )
    symb = [Symbol("c_{}".format(s)) for s in Sigma]
    # print(symb)

    solutions = linsolve((Matrix(Ms), Matrix(TaQ_PA_Z)), symb)
    # print(solutions)
    c_SZ = next(iter(solutions))

    # print(c_SZ)
    # return tuple(itertools.compress(Sigma, map(lambda x: x != 0, c_SZ)))
    return tuple(Counter({s: x for (s, x) in zip(Sigma, c_SZ)
                          }).elements())


def BSD(Z, P, TaQ=None):
    """
        Algorithm 10.96 (Better Sign Determination).
    """

    if TaQ is None:
        raise Exception('Missing Tarski-query black-box implementation')

    if not P:
        raise Exception('P must be non-empty, got {}.'.format(P))

    s = len(P)

    _symbols = P[0].free_symbols
    _domain = P[0].domain

    _1 = Poly(1, *_symbols, domain=_domain)
    r = TaQ(_1, Z)

    if r == 0:
        return ()

    Sigma = [None] * (s + 1)
    c = [None] * (s + 1)
    Comp = [None] * (s + 1)
    Ada = [None] * (s + 1)
    t = [None] * (s + 1)
    Mat = [None] * (s + 1)

    Sigma[0] = ((),)
    c[0] = (r,)
    Comp[0] = ()
    Ada[0] = ((),)
    t[0] = (r,)
    Mat[0] = (1,)

    for i, Pi in enumerate(P, 1):

        l = TaQ(Pi, Z)
        s = TaQ(Pi**2, Z)
        # Solve the constant-size linear system
        #
        #  / 1  1  1 \   / c( Pi = 0 , Z ) \     / TaQ( Pi**0 , Z ) \
        # |  0  1 -1  | |  c( Pi > 0 , Z )  | = |  TaQ( Pi**1 , Z ) |
        #  \ 0  1  1 /   \ c( Pi < 0 , Z ) /     \ TaQ( Pi**2 , Z ) /
        #

        eq = r - s
        gt = (l + s) / 2
        lt = (s - l) / 2

        _SIGNPiZ = []

        if eq:
            _SIGNPiZ.append(0)
        if gt:
            _SIGNPiZ.append(1)
        if lt:
            _SIGNPiZ.append(-1)

        rPi = len(_SIGNPiZ)
        SIGNPiZ = tuple(_SIGNPiZ)

        if rPi == 1:

            Sigma[i] = tuple(A(Sigma[i - 1], _SIGNPiZ))
            c[i] = c[i - 1]
            Comp[i] = Comp[i - 1]
            Ada[i] = Ada[i - 1]
            t[i] = t[i - 1]
            Mat[i] = Mat[i - 1]

        else:

            # complex case :(

            Sigma_ = tuple(A((Sigma[i - 1][j] for j in Comp[i - 1]), _SIGNPiZ))
            AdaSigma_ = X(Ada[i - 1], range(len(_SIGNPiZ)))

            # MAGIC HAPPENS

            print(Sigma_)
            print(AdaSigma_)

    return r


def mulmod(Q):

    return lambda a, b: (a * b) % Q


def USD(Q, P):
    """
        Algorithm 10.97 (Univariate Sign Determination).
    """

    return NSD(Q, P, TaQ=UTQ, mul=mulmod(Q))


def ATE(P):
    """
        Algorithm 10.100 (Thom Encoding).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly(x**2, x, domain=QQ)
        >>> ATE(P)
        ((0, 0, 1),)
        >>> P = Poly(-x**2, x, domain=QQ)
        >>> ATE(P)
        ((0, 0, -1),)
        >>> P = Poly(x**2 - 4, x, domain=QQ)
        >>> ATE(P)
        ((0, -1, 1), (0, 1, 1))

    """

    if P == 0:

        raise Exception('P must be nonzero, got {}'.format(P))

    # can optimize by deducing P(x) = 0 for all roots x
    a = USD(P, Der(P))

    key = functools.cmp_to_key(PTE)

    return tuple(sorted(a, key=key))


def CRRCF(P, Q):
    """
        Algorithm 10.105 (Comparison of Roots in a Real Closed Field).
    """

    if P == 0:

        raise Exception('P must be nonzero, got {}'.format(P))

    if Q == 0:

        raise Exception('Q must be nonzero, got {}'.format(Q))

    # TA = USD(P, Der(P))
    # TB = USD(Q, Der(P))
    ap = USD(P, Der(P))
    aq = USD(P, Der(Q))
    bp = USD(Q, Der(P))
    bq = USD(Q, Der(Q))

    # print('encoding of P\'s roots in P', ap)
    # print('encoding of P\'s roots in Q', aq)
    # print('encoding of Q\'s roots in P', bp)
    # print('encoding of Q\'s roots in Q', bq)

    Ap = ((0, a) for a in ap)
    Bp = ((1, b) for b in bp)
    Aq = ((0, a) for a in aq)
    Bq = ((1, b) for b in bq)

    roots = tuple(Ap) + tuple(Bp)

    key = functools.cmp_to_key(PTE)
    return sorted(roots, key=lambda t: key(t[1]))


class Interleaving (object):

    """
        Interleaving of two polynomials.

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 5), x, domain=QQ)
        >>> Interleaving(P, Q)
        p < p < q
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 2), x, domain=QQ)
        >>> Interleaving(P, Q)
        p < q < p
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 0), x, domain=QQ)
        >>> Interleaving(P, Q)
        q < p < p
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 1), x, domain=QQ)
        >>> Interleaving(P, Q)
        p = q < p
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 3), x, domain=QQ)
        >>> Interleaving(P, Q)
        p < p = q

    """

    def __init__(self, P, Q):

        self.roots = CRRCF(P, Q)

    def __repr__(self):

        S = 'pq'
        l = '<'
        e = '='
        s = ' '

        x = self.roots[0][1]
        r = [S[self.roots[0][0]]]

        for j, x in enumerate(self.roots[1:]):

            if PTE(self.roots[j][1], x[1]) < 0:
                r.append(l)
            else:
                r.append(e)

            r.append(S[self.roots[j + 1][0]])

        return s.join(r)


if __name__ == '__main__':

    print('Run doctests with')
    print('$ python -m doctest [-v] thom.py')
