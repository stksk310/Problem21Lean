# Introduction {#sec-01}

The type of a numerical semigroup is the number of its pseudo-Frobenius numbers, and it agrees with the Cohen--Macaulay type of the corresponding semigroup ring [@MS21, §1]. In this paper we control this number through the minimal generators and their nonnegative representations. Standard structure theorems are available for three-generated semigroups in both the symmetric and nonsymmetric cases, whereas in embedding dimension four one must relate the three-generated subsemigroup obtained by removing the smallest generator to the gap conditions in the original semigroup.

The condition studied here is canonical reduction. Let \(m\) denote the least positive generator and \(F\) the Frobenius number. We require \(F+m-\varphi\in\Gamma\) for every pseudo-Frobenius number \(\varphi\). This semigroup-theoretic formulation appears in §4 of Moscariello--Strazzanti [@MS21]. The corresponding condition for all nonnegative gaps has also been studied under the name positioned [@Branco2021]. We use canonical reduction as our primary terminology and prove directly in Section 2 the passage from pseudo-Frobenius numbers to all gaps. For the ring-theoretic background, see Rahimi [@Rahimi2020].

Our main result is the following.

## Type bound for canonical four-generated numerical semigroups {#fr-T1}

A numerical semigroup is a cofinite subset of the nonnegative integers that contains \(0\) and is closed under addition. Let
\[
\Gamma=\langle m,n_1,n_2,n_3\rangle,\qquad
\operatorname{edim}(\Gamma)=4,\qquad m=\min(\Gamma\setminus\{0\})
\]
with all four generators minimal; in particular, \(0<m<n_r\). Let
\(F=F(\Gamma)=\max(\mathbb Z\setminus\Gamma)\) be the Frobenius number, and define
\[
PF(\Gamma)=\{q\in\mathbb Z\setminus\Gamma:
q+s\in\Gamma\text{ for every }s\in\Gamma\setminus\{0\}\},
\qquad t(\Gamma)=|PF(\Gamma)|
\]
Under the canonical condition
\[
\boxed{F+m-\varphi\in\Gamma\quad(\forall\varphi\in PF(\Gamma))}
\tag{CANONICAL}
\]
one has
\[
\boxed{t(\Gamma)\le4}
\]
The proof is assembled in [I9](#fr-I9).


This statement has the same hypotheses and conclusion as Question 4.4 of Moscariello--Strazzanti and Problem 21 of Moscariello--Sammartano [@MS21, Question 4.4; @MoscarielloSammartano, Problem 21]. Throughout the paper, the canonical condition displayed above is used at every stage of the proof.

The proof begins with a two-layer decomposition of the Apéry set. Set \(Q(\Gamma)=PF(\Gamma)\setminus\{F\}\), and associate to each \(q\in Q(\Gamma)\) the elements \(q+m\) and \(c_q=F+m-q\). Their nonnegative representations imply that \(H=\langle n_1,n_2,n_3\rangle\) is a genuine minimally three-generated numerical semigroup. When \(H\) is symmetric, we use a stable ideal and the correspondence between its minimal generators and the Apéry set to obtain the bound.

When \(H\) is nonsymmetric, its two pseudo-Frobenius numbers give rise to six arms. The two colors of arms in the same direction have synchronized return levels, while three arms of the same color are excluded using an empty relative-lattice tetrahedron and a finite path inside a box. Combining these constraints with incomparability of the complements reduces four elements selected from a putative counterexample to one of three configurations: a path configuration, a configuration with one singleton, or a chain configuration.

The first two configurations are eliminated by comparing two returns. In the chain configuration, we maximize one coordinate over the finite factorization set of the same element \(q_A+m\), thereby constructing a unit-root relation. After treating the boundary and the range in which the relevant packets are available, two exchange relations between nonnegative representations remain. We then perform a Euclidean descent that preserves the same semigroup and the same \(W=F+m\) while decreasing the positive integer \(E+\chi\). At termination, all coefficients required for the exchange are shown to occur in representations of that same \(W\), and removing one copy of \(m\) yields the contradiction \(F\in\Gamma\).

Sections 2--4 establish the structural reductions and the classification into the three terminal configurations. Sections 5--6 eliminate the configurations involving singletons. Sections 7--10 treat the chain configuration, and Section 11 assembles the main theorem. Appendix A contains the complete case analysis for the symmetric tail, Appendix B gives the relative-lattice and box-path arguments, Appendix C records the positivity expansions, and Appendix D specifies the static full-coefficient certificates. The complete coefficient tables for the two large identities are required supplementary proof data, and their coefficient checks are computer-assisted. The argument does not rely on a finite-range scan of numerical semigroups or on a complete formalization in a proof assistant.
