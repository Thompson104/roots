#!/usr/bin/env python3

from sympy import *

Res = resultant

def lcof ( P ) :
    return LC( P )

def cof ( j , P ) :

    if j < 0 or j > P.degree() :
        raise Exception( 'index {} out of range for {}'.format( j , P ) )

    return P.all_coeffs()[-j-1]

def Rem ( P , Q ) :
    # print( 'Rem' , P , Q )
    return rem( P , Q , auto = False )


def ub ( P ) :
    a = P.coeffs()
    return 2 * sum( map( abs , a ) ) / abs( a[0] )


def lb ( P ) :
    return -ub( P )


def compare ( s , r ) :

    d = len( s )

    if d != len( r ) :
        raise Exception( 'sign conditions must have the same length' )

    if s == r :
        if s[0] == r[0] == 0 :
            return 0
        else :
            raise Exception( 'not roots but same sign conditions, cannot compare' )

    else :
        k = 1
        while k <= d :
            if s[d-k] != r[d-k] :
                break
            k += 1

        if s[d-k+1] == 1 :
            return 1 if s[d-k] > r[d-k] else -1

        else :
            return 1 if s[d-k] < r[d-k] else -1


def Var ( P ) :

    if b is None :
        return _Var_at( P , a )

    else :
        return _Var_at( P , a ) - _Var_at( P , b )


def _Var_at ( P , a ) :

    _a = map( lambda f : f(a) , P )

    return _Var( _a )


def _Var ( a ) :

    b = tuple( filter( lambda x : x != 0 ) )

    if len( b ) < 2 :
        return 0

    return sum( ( i*j < 0 ) for (i,j) in zip( b[:-1] , b[1:] ) )


def Der ( P ) :

    return tuple( P.diff((0,d)) for d in range( P.degree() + 1 ) )


def Zer ( P ) :
    pass

def eps ( i ) :

    if i < 1 :
        raise Exception( 'i must be greater or equal to 1, got {}'.format( i ) )

    if i not in ZZ :
        raise Exception( 'i must be in ZZ, got {}'.format( i ) )

    # return (-1)**( ( i * ( i - 1 ) ) // 2 )

    if i % 4 == 0 or i % 4 == 1 :
        return 1

    else :
        return -1


def PmV ( s ) :

    _s = tuple( reversed( s ) )

    return _Pmv( _s )

def _PmV ( s ) :

    p = len( s ) - 1

    if s[p] == 0 :
        raise Exception( 's[p] must be nonzero, got {}'.format(s[p]) )

    q = p - 1

    while q >= 0 and s[q] == 0 :
        q -= 1

    if q < 0 :
        return 0

    r = s[:q+1]

    if p - q % 2 == 1 :

        return _PmV( r ) + eps( p - q ) * sign( s[p] * s[q] )

    else :

        return _PmV( r )


def SSP ( P , Q ) :

    """
        Algorithm 8.76 (Signed Subresultant Polynomials).
    """

    # print( 'SSP' , P , Q )

    p = P.degree()
    q = Q.degree()

    if p <= q :
        raise Exception( 'P must have strictly larger degree than Q. Got p = {}, q = {}.'.format( p , q ) )

    sResP = [ None ] * ( p + 1 )
    s = [ None ] * ( p + 1 )
    t = [ None ] * ( p + 1 )

    sResP[p] = P
    s[p] = t[p] = 1
    sResP[p-1] = Q
    bq = Q.coeffs()[0]
    t[p-1] = bq
    sResP[q] = eps(p-q) * bq**(p-q-1) * Q
    s[q] = eps(p-q) * bq**(p-q)

    for l in range( q + 1 , p - 1 ) :
        sResP[l] = s[l] = 0

    i = p + 1
    j = p

    while sResP[j-1] != 0 :

        k = sResP[j-1].degree()

        if k < 1 :
            break

        if k == j - 1 :

            s[j-1] = t[j-1]
            sResP[k-1] = -Rem( sResP[i-1].mul_ground(s[j-1]**2) , sResP[j-1] ).div( s[j] * t[i-1] )[0]

        elif k < j - 1 :
            s[j-1] = 0

            for d in range ( 1 , j - k ) :

                t[j-d-1] = (-1)**d * (t[j-1]*t[j-d]) / s[j]

            s[k] = t[k]
            sResP[k] = sResP[j-1].mul_ground(s[k]/t[j-1])

            # typo in book, says k + 1 instead of k - 1
            for l in range( j - 2 , k ) :
                sResP[l] = s[l] = 0

            sResP[k-1] = -Rem(sResP[i-1].mul_ground(t[j-1]*s[k]),sResP[j-1]).div(s[j] * t[i-1])[0]

        t[k-1] = sResP[k-1].coeffs()[0]

        i = j
        j = k

    for l in range( 0 , j - 1 ) :
        sResP[l] = s[l] = 0

    return tuple( sResP )

def SSC ( P , Q ) :
    """
        Algorithm 8.77 (Signed Subresultant Coefficients).
    """
    sResP = SSP( P , Q )
    sRes = tuple( cof( i , sResPi ) for (i, sResPi) in enumerate( sResP ) )
    return sRes

def UTQ ( Q , P ) :

    """
        Univariate Tarski-Query
    """

    if P == 0 :

        raise Exception( 'P must be nonzero, got {}'.format( P ) )

    # if Q == 0 :

        # raise Exception( 'Q must be nonzero, got {}'.format( Q ) )


    q = Q.degree()

    if q == 0 :

        b0 = Q.coeffs()[0]


def SD ( Q , P , TaQ = None ) :

    """
        Sign Determination
    """

    if TaQ is None :
        raise Exception( 'Missing Tarski-query black-box implementation' )

    pass

def USD ( Q , P ) :

    """
        Univariate Sign Determination
    """

    return SD( Q , P , TaQ = UTQ )



def sort ( P , Q ) :

    if P == 0 :

        raise Exception( 'P must be nonzero, got {}'.format( P ) )

    if Q == 0 :

        raise Exception( 'Q must be nonzero, got {}'.format( Q ) )

    a = USR( P , Der( P.diff() ) + Der( Q ) )
    b = USR( Q , Der( Q.diff() ) + Der( P ) )

    result = [ ]

    # magic

    return result


if __name__ == '__main__' :

    from sympy.abc import a, b, c, x

    # TESTS

    f = x**2 - 1
    P = Poly( f , x , domain=QQ)
    assert( lb( P ) == -4 )
    assert( ub( P ) == 4 )

    t = Der( P )
    e = (Poly(x**2 - 1, x, domain='QQ'), Poly(2*x, x, domain='QQ'), Poly(2, x, domain='QQ'))
    assert( t == e )

    t = tuple( map( eps, range( 1 , 11 ) ) )

    assert( t == ( 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 ) )

    f = 9*x**13 - 18*x**11 - 33*x**10 + 102*x**8 + 7*x**7 - 36*x**6 - 122*x**5 + 49*x**4 + 93*x**3 - 42*x**2 - 18*x + 9
    P = Poly( f , x , domain=QQ)
    t = tuple( map( lcof , tuple( reversed( SSP(P,P.diff()) ) )[:9] ) )
    e = ( 9, 117, 37908, -72098829, -666229317948, -1663522740400320,
    -2181968897553243072, -151645911413926622112,
    -165117711302736225120 )
    assert( t == e )


    f = x**4 + a*x**2 + b*x + c
    P = Poly( f , x , domain=QQ[a,b,c] )
    t = tuple( reversed( SSP( P , P.diff()) ) )

    e = ( Poly(x**4 + a*x**2 + b*x + c, x, domain=QQ[a,b,c]),
    Poly(4*x**3 + 2*a*x + b, x, domain=QQ[a,b,c]),
    Poly(-8*a*x**2 - 12*b*x - 16*c, x, domain=QQ[a,b,c]),
    Poly((-8*a**3 + 32*a*c - 36*b**2)*x - 4*a**2*b - 48*b*c, x, domain=QQ[a,b,c]),
    Poly(16*a**4*c - 4*a**3*b**2 - 128*a**2*c**2 + 144*a*b**2*c - 27*b**4 +
        256*c**3, x, domain=QQ[a,b,c]))

    assert( t == e )

    f = x**4 + a*x**2 + b*x + c
    P = Poly( f , x , domain=QQ[a,b,c] )
    t = SSP( P , P.diff().diff())
    e = (Poly(400*a**4 - 5760*a**2*c + 3456*a*b**2 + 20736*c**2, x, domain=QQ[a,b,c]),
        Poly(1728*b*x - 240*a**2 + 1728*c, x, domain=QQ[a,b,c]),
        Poly(-144*x**2 - 24*a, x, domain=QQ[a,b,c]),
        Poly(12*x**2 + 2*a, x, domain=QQ[a,b,c]),
        Poly(x**4 + a*x**2 + b*x + c, x, domain=QQ[a,b,c])
    )

    assert( t == e )

