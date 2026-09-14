Immediate scope correction to the staircase paragraph: the displayed
`qmax` formula remains a globally legal/capacity-safe candidate and the exact
GREEN computations at active 75, 76, and 77 are unaffected, but a new symbolic
associated-graded audit has now **falsified its unchanged global spanning
claim**. The first defect is at active 68, block `n=49,h=10`: the raw block has
seven `j` values and target degree-`h` dimension one, while the old staircase
selects zero.

This does not contradict the original comment's caveat that matrix span had
only been proved for active 75--77; it means the proposed induction needs an
additional boundary term before active 68 and must not be cited as a global
basis yet.

The same audit supplies a cleaner route to the repair. At fixed `n=y+q-s`, raw
columns are `v^s(1+t)^y` with `t=u-v/2`; the target `h` block has dimension
`min(h+1,K-h)`, and the Pascal columns are indexed by `j=h-s`. We are now
classifying every missing `j` stratum, adding the minimal boundary prefixes,
and rerunning the literal window-slack audit. I will post the corrected formula
only after both symbolic rank and global capacity pass.
