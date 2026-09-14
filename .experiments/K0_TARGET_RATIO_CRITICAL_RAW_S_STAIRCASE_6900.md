# k=0 critical raw-`S` staircase and seed-zero closure

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, target-ratio
constant-`T` controls. This changes no production file, score, candidate, or
submission.

## Verdict

The raw `{1,R,S}` survivor has a sharp first filtration grade in both exact
target-ratio controls:

```text
subcritical S staircase:  X^j Y^y S Z^z, 0 <= y < m, all legal j,z
critical closing band:     X^j Y^m S,       z=0, all legal j.
```

Over raw `{1,R}`, the entire subcritical staircase adds contact rank one for
one, creates no new kernel vector, and leaves boundary gain three. Adding
only the seed-zero critical band creates the first new relative contact
kernel and immediately raises boundary gain to four.

Neither ingredient works alone: adding the whole critical `Y^m S` layer to
raw `{1,R}` without the subcritical staircase leaves gain three. This is a
genuine causal staircase interaction, not an isolated top monomial.

The exact theorem-sized target suggested by the controls is therefore:

```text
the first curvature connecting map occurs at Y-degree m and passive seed 0,
after the complete Y-degree <m raw-S staircase has been installed.
```

## 1. Exact m5 receipt

Profile:

```text
(n,w,g,m,B,s,U,L)=(11,5,8,5,2,1,8,8).
```

Raw `{1,R}` begins at

```text
columns/contact/kernel/gain = 2076 / 2038 / 38 / 3.
```

Adjoining all 860 raw `S` columns with `Y`-degree `<5` gives

```text
2936 / 2898 / 38 / 3.
```

Thus every subcritical column increases contact rank and none creates a new
kernel direction. The critical seed-zero band has the 12 columns

```text
X^j Y^5 S,  0 <= j < 12.
```

After adjoining it:

```text
2948 / 2907 / 41 / 4.
```

It adds 12 columns but only nine contact ranks, creating three new kernel
directions; their boundary image contributes the missing curvature normal.
By contrast, adjoining all three legal critical seed bands (`z=0,1,2`) to
raw `{1,R}` *without* the subcritical staircase gives

```text
2112 / 2074 / 38 / 3.
```

and creates no kernel at all.

## 2. Exact m6 receipt

Profile:

```text
(n,w,g,m,B,s,U,L)=(11,5,8,6,2,1,8,8).
```

Raw `{1,R}` begins at

```text
2724 / 2713 / 11 / 3.
```

Adjoining all 1,160 raw `S` columns with `Y`-degree `<6` gives

```text
3884 / 3873 / 11 / 3.
```

Again the whole subcritical staircase is contact-independent modulo the
base. The 15-column critical band

```text
X^j Y^6 S,  0 <= j < 15
```

then gives

```text
3899 / 3887 / 12 / 4.
```

Here it creates exactly one new kernel vector and that vector supplies the
fourth normal direction. Both legal critical bands (`z=0,1`) without the
subcritical staircase instead give

```text
2754 / 2743 / 11 / 3,
```

again no new kernel and no curvature normal.

## 3. Exact witness scope

The script extracts a normalized contact-kernel vector at the first closing
band and checks its boundary `S` coordinate is one. The canonical Flint
nullspace vectors are dense:

```text
m5: 2617 nonzero source coefficients,
    boundary (Y,R,S,Z)=(62,21,1,54),
    SHA-256 6564fe0e0cf0c4bc72208fc8b151377588102f941915f2e37b016c913836e1e3;

m6: 3220 nonzero source coefficients,
    boundary (Y,R,S,Z)=(16,71,1,7),
    SHA-256 122f9d5abd0d35db4c9260ae8a962248c20658c4fb9cf4e47a956cda1f1117ea.
```

These are exact finite certificates but not plausible symbolic formulas.
Their density is evidence that the desired proof should derive the causal
staircase recurrence rather than transcribe a selected nullspace basis.

Coordinate convention warning: the Python oracle's curvature variable is
`V2=P''`, while `LowerGeometry` uses the Hasse-scaled variable `S=P''/2`.
The rank filtration and first critical grade are invariant under this
nonzero diagonal rescaling over `F_101`. The printed finite coefficients are
not literal `LowerGeometry` coefficients; every curvature exponent and the
dual curvature coordinate must be rescaled before any formal transport.

Artifact:

```text
.experiments/k0_target_ratio_raw_s_active_filtration_6900.py

canonical SHA-256  91e08d4cf17870debae2055185c5db6da802cf31c75b8e53e3a5cace8a22967c
script SHA-256     08c9e0fcce902c53981960ff7c6b85cb714b7aa891307f7a2f49643ab75b45d0
runtime            196.7 s, 963 MiB peak RSS, 7 GiB process cap
```

## 4. Target m47 specialization

The literal critical closing band is source-legal at target scale:

```text
X^j Y^47 S,  z=0,
0 <= j < 47*180413 - 47*131071 - (131071-2)
           = 2,188,005.
```

Its active degree is `47+1=48<=U=64`, derivative weight is `2<=B=16`,
curvature degree is one, and passive-seed-plus-active degree is 48. The
suggested subcritical staircase consists of the same raw `S` shape at
`Y`-degrees `0,...,46` with every legal `X/Z` shift.

This is still not a target proof. The low `{1,R,S}` envelope has a negative
target source margin under the published rank bound, so one must extract
this semantic staircase from the complete capacity-positive source rather
than replace that source by the staircase.

## 5. Reduced-curvature profile assessment

Commit `da056e7` gives the target-green profile

```text
(m,B,s,U,L)=(47,16,6,64,5107)
```

with source margin `12,113,822` and a green consumer. The finite semantic
survivor uses only curvature exponents zero and one, and the critical
staircase itself uses exactly one `S`. Therefore removing ambient layers
`S^7,S^8` does not remove a single column of the observed `{1,R,S}` normal
mechanism. The two exact controls already work at the still shallower
ambient cap `s=1`.

`K0LineThenKill6900.normal_surjective_mono_submodule` now formally proves
that normal surjectivity on a source submodule persists after arbitrary
higher source layers are restored. Thus, if the raw `{1,R,S}` staircase is
proved universally, it embeds unchanged into both the old `s=8` and new
`s=6` profiles; higher curvature cannot regress it.

This is a **GREEN semantic compatibility check** for the reduced-curvature
profile, not its missing conormal theorem. The remaining uncertainty is the
same global recurrence/CRT statement for the subcritical staircase and
critical seed-zero closing band.

## 6. Exact next identity

The next proof should no longer target an arbitrary raw-S tower. It should
prove the following filtered connecting statement directly:

```text
Let V_<m be raw {1,R} plus every legal X^j Y^y S Z^z with y<m.

1. The boundary image of ker(contact|V_<m) is exactly S=0.
2. In V_<m + span{X^j Y^m S}, one seed-zero critical combination has contact
   trace in contact(V_<m) and boundary difference with nonzero S coordinate.
```

The controls show that replacing the seed-zero critical band by the whole
critical layer but omitting `V_<m` is false. A valid proof must retain the
causal lower-`Y` recurrence. The local `ThreeShapeLocalConnector6900`
Toeplitz determinant is consistent with this pattern, but its complete-state
and global tapered-window hypotheses are exactly what must now be supplied.

