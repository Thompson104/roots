#!/usr/bin/env python3
from sympy.abc import z
import matplotlib.pyplot as plt
import numpy as np


def fn(z, n):
    f = 1
    for i in range(1, n + 1):
        f *= (z - i)
    return f


def plot(fns, x, space):
    G = 0
    n = len(fns) - 1
    plots = []
    for i, fn in enumerate(fns):
        B = i / n
        R = 1 - B
        y = np.vectorize(lambdify(x, fn, 'numpy'))(space)
        plots.append(plt.plot(space, y, color=(R, G, B)))
    plt.show(plots)


def df(f, x):
    yield f
    if f != 0:
        yield from df(f.diff(x), x)


if __name__ == '__main__':

    n = 10

    f = fn(z, n)

    x = np.linspace(0, n + 1, 10000)

    fns = list(df(f, z))

    plot(fns, z, x)
