# C10 source of truth

The frozen C10 mathematical implementation is under `P21/Nonsymmetric/Chain/C10/`, with the umbrella module `P21/Nonsymmetric/Chain/C10.lean`.

The frozen reproducibility gates, certificate generator, input hashes, and source-integrity manifest are under `verification/c10/`. The authoritative completed checkpoint for Section 11 is commit `e4799d8044fd524a94b960ab19c333b08a8c93bb`.

Section 11 may import C10 but must not edit these mathematical sources.

