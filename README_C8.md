# C8 chain boundary and packet window

C8 is frozen at commit `7769545a357c0c4d24520ec7a9fc8994f3f664e7`.
It eliminates the boundary `Croot = alpha`, constructs the unit-window branch
without leaking its ONE/DET1/PARAM data, and exposes the exhaustive endpoint
`RegionU ∨ RegionD` through `ChainCore.FirstFit.c8_handoff`.

All C8 mathematical Lean files are immutable in C9. The next input is exactly
the two branch structures returned by the handoff.
