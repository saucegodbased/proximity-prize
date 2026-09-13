#!/usr/bin/env python3
"""Reproduce the sign audit in FIXED_SCALAR_POLE_AGGREGATION_AUDIT_6900.md."""
n = 262144
a = 180413
for w in (132103, 149776, 156003):
    print(w, a-w, a*a-n*w, n*(n-w))
