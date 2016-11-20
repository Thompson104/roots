#!/usr/bin/env python3

"""
    Propositions, Notations and Algorithms numbering is based on the numbering
    from the book *Algorithms in Real Algebraic Geometry (2016)* by Basu,
    Pollack and Roy.
"""

import itertools
import functools
import operator
import heapq
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
from sympy import oo


def Zer(P):
    """
        Let R be a real closed field. If P is a finite subset of R[X1,...,Xk],
        we write the set of zeros of P in R^k as

        Zer(P[,R^k]) = { x in R^k |   /\   p(x) = 0 }.
                                    p in P

        These are the algebraic set of R^k = Zer({0},R^k)
    """

    pass


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
        Proposition 2.7. Let P = a[p]X^p + ... + a[0], a[p] != 0, be a
        polynomial with coefficients in an ordered field F. If

        |x| > 2*sum(abs(ai/a[0]) for ai in a),

        then P(x) and a[p]x^p have the same sign.

        =======
        Summary
        =======

        Computes a non-inclusive upper bound on the values of the real roots of
        P.

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
        Computes a non-inclusive lower bound on the values of the real roots of
        P. See Proposition 2.7.

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

        Let P be a non-zero polynomial of degree d with coefficients in R. Let
        a and b be two elements of R, and denote by s and r the sign
        conditions on Der(P) realized at a and b. Then:

        1. If s = r and s(P) = r(P) = 0 then a = b.
        2. If s != r, one can decide whether a < b or a > b as follows. Let k
        be the smallest integer such that s(P.diff(d-k)) and r(P.diff(d-k)) are
        different. Then s(P.diff(d-k+1)) = r(P.diff(d-k+1)) != 0.
            2.1. If s(P.diff(d-k+1)) = r(P.diff(d-k+1)) = 1,
                a > b <=> s(P.diff(d-k)) > r(P.diff(d-k))
            2.2. If s(P.diff(d-k+1)) = r(P.diff(d-k+1)) = -1,
                a > b <=> s(P.diff(d-k)) < r(P.diff(d-k))

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
        >>> PTE((0,),())
        Traceback (most recent call last):
         ...
        Exception: sign conditions must have the same length
        >>> PTE((2,),(0,))
        Traceback (most recent call last):
         ...
        Exception: s=(2,) contains an intruder
        >>> PTE((0,),(2,))
        Traceback (most recent call last):
         ...
        Exception: r=(2,) contains an intruder
        >>> PTE((1,1,1),(1,1,1))
        Traceback (most recent call last):
         ...
        Exception: not roots but same sign conditions, cannot compare

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
        Notation 2.35 (Derivatives).

        Let P be a univariate polynomial of degree p in R[X]. We denote by
        Der(P) the list P.diff(0),P.diff(1),...,P.diff(p).

        =======
        Summary
        =======

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
        Notation 4.26 (Reversing rows).

        We denote by eps(i) the signature of the permutation reversing the
        order of i consecutive rows in a matrix, i.e.
        eps(i) = (-1)**(i*(i-1)/2). For every natural number i >= 1,

            eps(4i) = 1, eps(4i-1) = -1, eps(4i-2) = -1, eps(4i-3) = 1.

        In particular, eps(i-2j) = (-1)**j eps(i).

        >>> tuple(map(eps, range(1, 11)))
        (1, -1, -1, 1, 1, -1, -1, 1, 1, -1)
        >>> eps(0)
        Traceback (most recent call last):
            ...
        Exception: i must be greater or equal to 1, got 0
        >>> eps(3/2)
        Traceback (most recent call last):
            ...
        Exception: i must be in ZZ, got 1.5

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


def SVSP(PP):
    return SVSPab(PP, -oo, +oo)


def SVSPab(PP, a, b):
    """
        Given a and b in R U {-oo,+oo}, we denote

        Var(P;a,b) = Var(P;a) - Var(P;b)
    """

    return SVSPa(PP, a) - SVSPa(PP, b)


def SVSPa(PP, a):
    """
        Notation 2.45 (Sign variations in a sequence of polynomials at a).

        Let P = P[0],P[1],...,P[d] be a sequence of polynomials and let a be an
        element of R U {-oo,+oo}. The number of sign variations of P at a,
        denoted by Var(P;a), is Var(P[0](a),...,P[d](a)) (at -oo and +oo the
        signs to consider are the signs of the leading monomials according to
        Proposition 2.7).

        >>> from sympy import Poly
        >>> from sympy.abc import x
        >>> P = ( Poly(f,x) for f in (x**5, x**2 - 1, 0, x**2-1, x+2, 1))
        >>> SVSPa(P,1)
        0

    """

    def _eval ( P ) :

        if a == -oo :
            return P(lb(P)-1)
        elif a == +oo :
            return P(ub(P)+1)
        else:
            return P(a)

    _a = map(_eval, PP)

    return SV(_a)


def SV(a):
    """
        Notation 2.43 (Sign variations).

        The number of sign variations, Var(a), in a sequence, a = a[0],...,a[p]
        of elements in R\{0} is defined by induction on p by:

        Var(a[0]) = 0,

                              / Var(a[1],...,a[p]) + 1 if a[0]*a[1] < 0,
        Var(a[0],...,a[p]) = |
                              \ Var(a[1],...,a[p])     if a[0]*a[1] > 0.

        This definition extends to any finite sequence a of elements in R by
        considering the finite sequence b obtained by dropping the zeros in a
        and defining

                        Var(a) = Var(b), Var(emptyset) = 0.

        >>> SV((1, -1, 2, 0, 0, 3, 4, -5, -2, 0, 3))
        4

    """

    b = tuple(filter(lambda x: x != 0, a))

    if len(b) < 2:
        return 0

    return sum(1 if i * j < 0 else 0 for (i, j) in zip(b[:-1], b[1:]))


def PmVsResPQ(P, Q):
    """
        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P1 = Poly( x , x , domain=QQ)
        >>> PmVsResPQ(P1, P1.diff())
        1
        >>> P2 = Poly( x**2 , x , domain=QQ)
        >>> PmVsResPQ(P2, P2.diff())
        1
        >>> P3 = Poly( x**3 , x , domain=QQ)
        >>> PmVsResPQ(P3, P3.diff())
        1
        >>> P4 = Poly( x**2 - 1 , x , domain=QQ)
        >>> PmVsResPQ(P4, P4.diff())
        2

    """

    if Q == 0:
        return 0

    p = deg(P)
    q = deg(Q)
    R = Rem(P, Q)

    PmV = PmVsResPQ(Q, -R)

    if (p - q) % 2 == 1:
        return PmV + sign(lcof(P) * lcof(Q))
    else:
        return PmV


def PmVsResPQtco(P, Q):
    """
        Tail-call optimized version of PmVsResPQ.

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P1 = Poly( x , x , domain=QQ)
        >>> PmVsResPQtco(P1, P1.diff())
        1
        >>> P2 = Poly( x**2 , x , domain=QQ)
        >>> PmVsResPQtco(P2, P2.diff())
        1
        >>> P3 = Poly( x**3 , x , domain=QQ)
        >>> PmVsResPQtco(P3, P3.diff())
        1
        >>> P4 = Poly( x**2 - 1 , x , domain=QQ)
        >>> PmVsResPQtco(P4, P4.diff())
        2
        >>> f = 9 * x**13 - 18 * x**11 - 33 * x**10 + 102 * x**8 + 7 * x**7 \
- 36 * x**6 - 122 * x**5 + 49 * x**4 + 93 * x**3 - 42 * x**2 - 18 * x + 9
        >>> P = Poly(f, x, domain=QQ)
        >>> a = NGPmV(SSC(P, P.diff()))
        >>> b = AGPmV(SSC(P, P.diff()))
        >>> c = PmVsResPQ(P, P.diff())
        >>> d = PmVsResPQtco(P, P.diff())
        >>> a == b == c == d
        True
        >>> a = NGPmV(SSC(P, P.diff().diff()))
        >>> b = AGPmV(SSC(P, P.diff().diff()))
        >>> c = PmVsResPQ(P, P.diff().diff())
        >>> d = PmVsResPQtco(P, P.diff().diff())
        >>> a == b == c == d
        True

    """

    PmV = 0

    p = deg(P)
    q = deg(Q)

    while Q != 0:

        if (p - q) % 2 == 1:
            PmV += sign(lcof(P) * lcof(Q))

        R = Rem(P, Q)
        r = deg(R)

        P = Q
        p = q
        Q = -R
        q = r

    return PmV


def NGPmV(s):
    """
        Notation 4.30 (Generalized Permanences minus Variations).

        Let s = s[p],...,s[0] be a finite list of elements in an ordered field
        K such that s[p] != 0. Let q < p such that s[p-1] = ... = s[q+1] = 0,
        and s[q] != 0, and s' = s[q],...,s[0]. (if there exists no such q, s'
        is the empty list). We define inductively

                  / 0                                  if s' is empty,
                 |
        PmV(s) = |  PmV(s') + eps(p-q) sign(s[p]*s[q]) if p - q is odd,
                 |
                  \ PmV(s')                            if p - q is even,

        where eps(p-q) is defined in Notation 4.26.

        Note that when all element of s are non-zero, PmV(s) is the difference
        between the number of sign permanence and the number of sign variations
        in s[p],...,s[0]. Note also that when s is the sequence of coefficients
        of polynomials P = P[p],...,P[0] with deg(P[i])=i, then

                               PmV(s) = Var(P;-oo,+oo)

        (see Notation 2.45).

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
        >>> NGPmV((0,))
        Traceback (most recent call last):
            ...
        Exception: s[p] must be nonzero, got 0

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
        >>> SSP(P,P)
        Traceback (most recent call last):
            ...
        Exception: P must have strictly larger degree than Q. Got p = 4, q = 4.

    """

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

def DSRS(P,Q) :
    """
        Definition 1.15 (Signed remainder sequence).

        >>> from sympy.abc import a , b , c , x
        >>> from sympy import QQ
        >>> P = Poly(x**4 + a*x**2 + b*x + c, x, domain=QQ[a,b,c])
        >>> P.diff()
        Poly(4*x**3 + 2*a*x + b, x, domain='QQ[a,b,c]')
        >>> DSRS(P,P.diff())
        (Poly(x**4 + a*x**2 + b*x + c, x, domain='QQ[a,b,c]'), \
Poly(4*x**3 + 2*a*x + b, x, domain='QQ[a,b,c]'), \
Poly(-a/2*x**2 - 3*b/4*x - c, x, domain='QQ[a,b,c]'), \
Poly((-2*a**3 + 8*a*c - 9*b**2)/a**2*x + (-a**2*b - 12*b*c)/a**2, x, domain='QQ(a,b,c)'), \
Poly((16*a**6*c - 4*a**5*b**2 - 128*a**4*c**2 + 144*a**3*b**2*c - 27*a**2*b**4 + 256*a**2*c**3)/(16*a**6 - 128*a**4*c + 144*a**3*b**2 + 256*a**2*c**2 - 576*a*b**2*c + 324*b**4), x, domain='QQ(a,b,c)'))
        >>> DSRS(P,0)
        (Poly(x**4 + a*x**2 + b*x + c, x, domain='QQ[a,b,c]'),)
        >>> DSRS(0,P)
        (0, Poly(x**4 + a*x**2 + b*x + c, x, domain='QQ[a,b,c]'))
        >>> DSRS(0,0)
        Traceback (most recent call last):
            ...
        Exception: both polynomials 0

    """

    if P == Q == 0 :
        raise Exception( 'both polynomials 0' )

    if Q == 0 :
        return (P,)

    if P == 0 : # might be unnecessary to explicit this case
        return (0,Q)

    return (P,) + DSRS(Q,-Rem(P,Q))

def TT(Q, P, a=-oo, b=+oo):
    """
       Theorem 2.73 (Tarski).

                     TaQ(Q,P;a,b) = Var(sRem(P,P'Q);a,b).

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly(2*x + 1, x, domain=QQ)
        >>> TT(P,P)
        0
        >>> P = Poly(x**2 - 2*x + 1, x, domain=QQ)
        >>> TT(P,P)
        0
        >>> P = Poly(x**3, x, domain=QQ)
        >>> TT(P,P)
        0
        >>> Q = Poly(7, x, domain=QQ)
        >>> TT(Q, P)
        1
        >>> Q = Poly(-7, x, domain=QQ)
        >>> TT(Q, P)
        -1
        >>> Q = Poly(0, x, domain=QQ)
        >>> TT(Q, P)
        0

    """

    return SVSPab(DSRS(P,P.diff().mul(Q)),a,b)

def TS(P,a=-oo,b=+oo):
    """
        Theorem 2.62 (Sturm).

           # roots in interval (a,b) = TaQ(1,P;a,b) = Var(sRem(P,P');a,b).

        >>> from sympy import Poly, QQ, Rational
        >>> from sympy.abc import x
        >>> P = Poly((x-1)*(x-3), x, domain=QQ)
        >>> TS(P)
        2
        >>> TS(P,-oo,0)
        0
        >>> TS(P,0,2)
        1
        >>> TS(P,2,4)
        1
        >>> TS(P,4,+oo)
        0
        >>> P = Poly((x-7)**10, x, domain=QQ)
        >>> TS(P)
        1
        >>> e = Rational(1,10**9)
        >>> TS(P,-oo,7-e)
        0
        >>> TS(P,7-e,7+e)
        1
        >>> TS(P,7+e,+oo)
        0

    """

    return TT(1,P,a,b)

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
        >>> UTQ(Q, 0)
        Traceback (most recent call last):
            ...
        Exception: P must be nonzero, got 0

    """

    if P == 0:

        raise Exception('P must be nonzero, got {}'.format(P))

    if Q == 0:

        return 0

    q = deg(Q)

    if q == 0:

        b0 = cof(0, Q)

        PmV = PmVsResPQtco(P, P.diff())

        return PmV if b0 > 0 else -PmV

    elif q == 1:

        b1 = cof(1, Q)
        b0 = cof(0, Q)

        p = deg(P)
        S = (P.mul_ground(p * b1) - P.diff().mul(Q)).mul(sign(b1))

        return PmVsResPQtco(P, S)

    else:

        PmV = PmVsResPQtco(-P.diff().mul(Q), P)

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
        >>> TMS(0)
        Traceback (most recent call last):
            ...
        Exception: s must be positive, got 0
        >>> TMS(3/2)
        Traceback (most recent call last):
            ...
        Exception: s must be in ZZ, got 1.5

    """

    if s < 1:
        raise Exception("s must be positive, got {}".format(s))

    if s not in ZZ:
        raise Exception("s must be in ZZ, got {}".format(s))

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
        >>> NSD(Q, Der(P))
        Traceback (most recent call last):
            ...
        Exception: Missing Tarski-query black-box implementation
        >>> NSD(Q, (), TaQ=UTQ)
        Traceback (most recent call last):
            ...
        Exception: P must be non-empty, got ()

    """

    if TaQ is None:
        raise Exception('Missing Tarski-query black-box implementation')

    if not P:
        raise Exception('P must be non-empty, got {}'.format(P))

    prod = lambda iterable: functools.reduce(mul, iterable, 1)

    P = list(reversed(P))
    s = len(P)

    Ms = TMS(s)
    Sigma = tuple(itertools.product((0, 1, -1), repeat=s))
    A = tuple(itertools.product((0, 1, 2), repeat=s))

    TaQ_PA_Z = []
    for a in A:
        t = TaQ(prod(P[i]**a[i] for i in range(s)), Z)
        TaQ_PA_Z.append(t)

    symb = [Symbol("c_{}".format(s)) for s in Sigma]

    solutions = linsolve((Matrix(Ms), Matrix(TaQ_PA_Z)), symb)
    c_SZ = next(iter(solutions))

    return tuple(Counter({s: x for (s, x) in zip(Sigma, c_SZ)}).elements())


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

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 0), x, domain=QQ)
        >>> sorted(USD(P, Der(P)))
        [(0, -1, 1), (0, 1, 1)]
        >>> sorted(USD(Q, Der(P)))
        [(1, -1, 1)]
        >>> sorted(USD(P, Der(Q)))
        [(1, 1), (1, 1)]
        >>> sorted(USD(Q, Der(Q)))
        [(0, 1)]

    """

    return NSD(Q, P, TaQ=TT, mul=mulmod(Q))


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
        >>> ATE(0)
        Traceback (most recent call last):
            ...
        Exception: P must be nonzero, got 0

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

        >>> from sympy import Poly, QQ
        >>> from sympy.abc import x
        >>> P = Poly((x - 1) * (x - 3), x, domain=QQ)
        >>> Q = Poly((x - 5), x, domain=QQ)
        >>> CRRCF(P,Q)
        ((0, (0, -1, 1, -1, 1)), (0, (0, 1, 1, -1, 1)), (1, (1, 1, 1, 0, 1)))
        >>> CRRCF(0,Q)
        Traceback (most recent call last):
            ...
        Exception: P must be nonzero, got 0
        >>> CRRCF(P,0)
        Traceback (most recent call last):
            ...
        Exception: Q must be nonzero, got 0

    """

    if P == 0:

        raise Exception('P must be nonzero, got {}'.format(P))

    if Q == 0:

        raise Exception('Q must be nonzero, got {}'.format(Q))

    def _PTE ( r , s ) :
        try:
            return PTE(r,s)
        except:
            return 0

    DerP = Der(P)
    DerQ = Der(Q)

    TPP = USD(P, DerP)
    TPQ = USD(P, DerQ)
    TQP = USD(Q, DerP)
    TQQ = USD(Q, DerQ)

    key = functools.cmp_to_key(PTE)
    _key = functools.cmp_to_key(_PTE)

    _TPP = sorted(TPP,key=key)
    _TPQ = sorted(TPQ,key=_key)
    _TQP = sorted(TQP,key=key)
    _TQQ = sorted(TQQ,key=_key)

    _TP = ((0, t+u) for t,u in zip(_TPP,_TPQ))
    _TQ = ((1, t+u) for t,u in zip(_TQP,_TQQ))

    return tuple(heapq.merge(_TP,_TQ, key=lambda t: key(t[1])))


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

    import doctest
    doctest.testmod()
