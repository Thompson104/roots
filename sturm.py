#!/usr/bin/env python3
from sympy import *
import matplotlib.pyplot as plt
import numpy as np

z = Symbol('z')
n = 2

def fn ( z , n ) :
    f = 1
    for i in range(1,n+1):
        f *= (z-i)
    return f

f=fn(z,n)

x = np.linspace(.5,n+.5,10000)

def plot ( fns , x , space ) :
    G = 0
    n = len(fns) - 1
    plots = []
    for i, fn in enumerate(fns) :
        B = i/n
        R = 1-B
        y = np.vectorize(lambdify( x , fn , 'numpy'))(space)
        plots.append(plt.plot(space,y,color = (R,G,B)))
    plt.show(plots)

fns = sturm( f , z )

plot( fns , z , x )
