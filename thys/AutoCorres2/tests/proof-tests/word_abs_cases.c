/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * More test cases for word abstraction.
 */

void foo(unsigned x) {
  x = x + 1;
}

int callee_flat_s(int bla) {
  return bla + 1;
}
int caller_flat_s(int bla)
{
    return callee_flat_s(bla);
}

unsigned callee_flat_u_abs(unsigned bla)
{
    return bla + 1;
}
unsigned callee_flat_u_noabs(unsigned bla)
{
    return bla + 1;
}

unsigned caller_flat_u_aa(unsigned bla)
{
    return callee_flat_u_abs(bla);
}
unsigned caller_flat_u_an(unsigned bla)
{
    return callee_flat_u_noabs(bla);
}
unsigned caller_flat_u_na(unsigned bla)
{
    return callee_flat_u_abs(bla);
}
unsigned caller_flat_u_nn(unsigned bla)
{
    return callee_flat_u_noabs(bla);
}

int callee_deep_s(int bla)
{
    return callee_deep_s(bla + 1);
}
int caller_deep_s(int bla)
{
    return callee_deep_s(bla);
}

unsigned callee_deep_u(unsigned bla)
{
    return callee_deep_u(bla + 1);
}
unsigned caller_deep_u(unsigned bla)
{
    return callee_deep_u(bla);
}

int mutual_s2(int);
int mutual_s1(int bla)
{
    return mutual_s2(bla + 1);
}
int mutual_s2(int bla)
{
    return mutual_s1(bla - 1);
}

int cross(int a, int b, int c, int d)
{
    return a * c - b * d;
}
int gcd_s_rec(int a, int b)
{
    if (a < 0) {
        return gcd_s_rec(-a, b);
    }
    if (b < 0) {
        return gcd_s_rec(a, -b);
    }
    if (a > b) {
        return gcd_s_rec(b, a);
    }
    if (a == 0) {
        return b;
    }
    return gcd_s_rec(a, b % a);
}
int gcd_s_loop(int a, int b)
{
    int c;
    if (a < 0) {
        a = -a;
    }
    if (b < 0) {
        b = -b;
    }
    while (a != 0) {
        c = a;
        a = b % a;
        b = c;
    }
    return b;
}

int sum(int *a, unsigned n)
{
    int s = 0;
    unsigned i;
    for (i = 0; i < n; i++) {
        s += a[i];
    }
    return s;
}
