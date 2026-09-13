6900 follow-up: the F101 border closes with exactly three explicit terminal rows

Accepted score remains 6806; no candidate or score file changed.

The centered-shell factorization is now integrated back into the literal bordered map. In the faithful primary F101 chamber, source grades `<=6` have 1463 columns, rank 1461, and joint `F0/F1/F2` defect 3. Adding **only the three explicit Wronskian rows**

```text
S_i = V^(m-2) Z^(J+1-m)
        (c_i V^2 + C_i Lambda V Z + A_i Xi J1 Z),
J1 = Lambda V1-Lambda'V,
```

raises rank to 1464 and makes all three individual defects and the joint defect zero. The other 308 grade-7 monomial columns are unnecessary for this exact closure. Each `S_i` is independently checked to have `C_G=0` and `J_YRS=0`, and its raw source reconstruction is legal.

The coefficient congruence has an explicit parameterization rather than a guessed `B`:

```text
P=cQ+A Xi Lambda',  r=P mod Lambda,
B0=-r+Lambda H,
B=B0+cQ-2A Lambda Xi'.
```

This automatically makes `B+A Xi Lambda'` divisible by `Lambda`. At target widths, all `Z^k S_i`, `0<=k<=2620`, are source-legal; four raw strip families end exactly at `D-1`. The quotient polynomial `H` still has room for twelve Hermite coefficients per error (`12e=980772 < 1000109`). Python and Lean receipts are in commit `04eca1b`; target strip arithmetic is also independently formalized in `fc581a3`.

Independent universality check: both predeclared matched `n=10` chambers reproduce the same centered Wronskian form for all first three RHS, with the `V^4` coefficient degenerating to zero and no centered second-jet carrier. Commit `4f4e2d2`.

Critical scope guard: target margin through grade 82 is `-334311837024`, so one grade-83 row cannot prove the target. The open source theorem is surjectivity/solvability of the full 2621-layer lower-triangular seed trellis onto the forced-head residual. `Z1` and the typed downstream allocation remain separate after THREE-RHS. Current work is deriving the simple-error diagonal block and testing the same form under arbitrary error-direction offsets.
