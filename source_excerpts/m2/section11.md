# Proof of the main theorem {#sec-11}

We now combine the conclusion for the symmetric tail, the classification of the nonsymmetric tail into three terminal configurations, and the elimination of each configuration. Starting from the contradiction hypothesis obtained by selecting four rows, we return to the cardinality bound for the full set \(Q(\Gamma)\).

## Completion of the CHAIN closure {#fr-C8.5}

[R7](#fr-R7) supplies the CORE of [C8.1](#fr-C8.1) from every actual CHAIN configuration. In [C8.2](#fr-C8.2), the boundary \(C=\alpha\) is eliminated and the strict case is divided into \(\mathcal U\vee\mathcal D\). The region \(\mathcal U\) is eliminated in [C8.3](#fr-C8.3). In [C8.4](#fr-C8.4), \(\mathcal D\) is reduced to \(q_0=2\) and \(N=\widehat\zeta+1\); if \(\theta\ge\upsilon+1\), a nonnegative representation of the same \(F\) gives a contradiction. In the remaining range \(1\le\theta\le\upsilon\), the determinant-one matrix of [E8.2.3](#fr-E8.2.3) satisfies every hypothesis of [E8](#fr-E8). The termination and terminal source-fit in [E8](#fr-E8) then produce a nonnegative representation of \(F\) in the original \(\Gamma\). Hence CHAIN cannot occur.

## Proof of the main theorem [T1](#fr-T1) {#fr-I9}

Let \(\Gamma\) be a minimally four-generated numerical semigroup satisfying the canonical condition of Sections 1–2, and suppose that
\(|Q(\Gamma)|\ge4\).

By [C2](#fr-C2), for every \(q\in Q(\Gamma)\) we have \(q+m,c_q,W\in\operatorname{Ap}(\Gamma,m)\subseteq H\), \(c_q-m\notin\Gamma\), and KEY holds. If four distinct rows are selected, the same \(\Gamma,F,m,W\), together with their actuality, pseudo-Frobenius, and complement conditions, are preserved.

We first exclude the third possibility for the tail gcd. Choose any \(q\in Q(\Gamma)\). Then

\[
m=(q+m)+(W-q)-W\in\mathbb ZH.
\]

Hence \(\gcd(n_1,n_2,n_3)\) also divides \(m\). Since \(\gcd(m,n_1,n_2,n_3)=1\), the tail gcd is one. Moreover, minimality of \(\Gamma\) implies that the three generators of the tail are themselves minimal. Thus \(H\) is a genuine minimally three-generated numerical semigroup, and is either symmetric or nonsymmetric. The signed identity above need not be called a nonnegative factorization.

If \(H\) is symmetric, [S3](#fr-S3) eliminates the contradiction hypothesis. If \(H\) is nonsymmetric, then G4, [M4](#fr-M4), and Appendix B show that the surviving configuration of the four selected rows is one of PATH, TYPE II, or CHAIN. The case of three singletons, in which the full set \(Q\) consists of only three rows, is proved separately in [G4.8](#fr-G4.8). Four-row configurations containing a corner are excluded by COLOR-CAP, and a matched pair together with a singleton is excluded in [G4.5.3](#fr-G4.5.3). This classification does not assume that the full set \(Q\) has exactly four elements.

PATH is impossible by [P5.7](#fr-P5.7), and TYPE II by [T6](#fr-T6). A CHAIN configuration has, by [R7](#fr-R7), the CORE-ROOT structure of the same configuration and passes through [C8.1](#fr-C8.1)–[C8.4](#fr-C8.4) into [E8](#fr-E8). The full color exchange of [E8](#fr-E8) preserves the original \(\Gamma,F,m,W\), and every nonterminal step strictly decreases the positive integer \(\mathcal M=E+\chi\). After finitely many steps a terminal state is reached, and replacing the packet coefficientwise inside the source of that same \(W\) yields a factorization of the original \(F\) with all coefficients nonnegative. This contradicts \(F\notin\Gamma\).

Thus every case arising from the contradiction hypothesis is impossible, and therefore

\[
\boxed{|Q(\Gamma)|\le3.}
\]

Since \(F\in PF(\Gamma)\),

\[
\boxed{t(\Gamma)=|Q(\Gamma)|+1\le4.}
\]

This proves Theorem [T1](#fr-T1) from Sections 1–2.
