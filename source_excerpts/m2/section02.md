# Preliminaries and canonical reduction {#sec-02}

We fix the hypotheses of the main theorem. In this section, the canonical condition is converted into an involution on the Apéry set and into nonnegative representations in the supported directions. Under the assumption of a counterexample, we also prove coprimality and minimality for the three-generated tail. The objects passed to the later classification are the same semigroup, the same \(F,m,W\), and actual pseudo-Frobenius numbers.

## Common notation and scope of the contradiction argument

\[
Q(\Gamma)=PF(\Gamma)\setminus\{F\},\qquad W=F+m,
\qquad H=\langle n_1,n_2,n_3\rangle,
\]
\[
\mathcal A=\operatorname{Ap}(\Gamma,m)
=\{w\in\Gamma:w-m\notin\Gamma\}.
\]
Since \(F\in PF(\Gamma)\), we have \(t=|Q(\Gamma)|+1\). From now on the contradiction hypothesis is \(|Q(\Gamma)|\ge4\). Selecting four rows does not mean that the total number of elements of \(Q\) is fixed to be four. We write \(x\le_\Gamma y\) when \(y-x\in\Gamma\). For each \(q\in Q(\Gamma)\), define its complement by \(c_q=W-q\).

In the nonsymmetric part we use
\[
SH(q)=\{r:q+n_r\in H\},\qquad D(c)=\{r:c-n_r\in H\}.
\]
The set \(Q(\Gamma)\) and a local integer denoted by \(Q\) are distinguished by type and by the point at which they are defined. Likewise, the two-generated semigroup \(T\) in the symmetric case and the matrix \(C\) in an appendix are local notation and should not be confused with the canonical CHAIN coefficient \(T=b_k+\alpha\) or the root coefficient \(C\).

## Standard external results used in the proof

The proof uses the following three standard results as external input, in exactly the forms stated here.

These results are not proved in this paper. We retain the bibliographic information for the original sources, and we have checked the precise locations in the supporting references used here. We do not assert unverified theorem numbers in the historical originals.

### Representation of symmetric three-generated semigroups {#ext-STD_SYM_GLUE}

After permuting the generators, every minimally three-generated symmetric numerical semigroup can be written as
\(H=\langle du,dv,w\rangle\), with \(d,u,v\ge2\),
\(\gcd(u,v)=\gcd(d,w)=1\), and \(w\in\langle u,v\rangle\).
This is the form corresponding to the three-generated complete-intersection theory of Herzog and Delorme; the direction used here is stated explicitly in García-Sánchez--Martín Cruz, §3.2, Theorem 6 [@Herzog1970; @Delorme1976; @GarciaMartin2020].

### Standard form for nonsymmetric three-generated semigroups {#ext-STD_HERZOG}

For every minimally three-generated nonsymmetric numerical semigroup there exist positive integers \(a_r,b_r\), with \(\rho_r=a_r+b_r\), such that the critical relations, the two pseudo-Frobenius numbers, and the formulas for the primitive tail generators given below hold. The precise forms used here follow Nari--Numata--Watanabe, §1, equation (1.1), and §2, equation (2.1.1) and Propositions 2.1--2.2 [@Herzog1970; @Nari2011]. Pairwise coprimality of the three generators is not assumed.

### Empty lattice tetrahedra {#ext-STD_WHITE}

A lattice tetrahedron containing no lattice points other than its vertices has lattice width one. Equivalently, there is a nonconstant primitive integer-valued affine functional that places all four vertices on two consecutive integer levels. We use White's theorem in this form [@White1964]. Khan--Rogers, §1, Theorems 3--4, gives the normal form required here [@Khan2016]. The application to the relative lattice, the partition of the vertices into two pairs, and the subsequent coefficient comparisons are all proved in this paper.

We fix the convention for STD_HERZOG in a cyclic order \((i,j,k)\):
\[
\rho_i n_i=b_jn_j+a_kn_k,\quad
\rho_jn_j=a_in_i+b_kn_k,\quad
\rho_kn_k=b_in_i+a_jn_j.
\tag{HCR}
\]
Each \(\rho_r\) is the least positive multiple of \(n_r\) admitting a nonnegative representation by the other two generators.
\[
f_A=(\rho_i-1)n_i+(a_j-1)n_j-n_k,
\quad f_B=(\rho_i-1)n_i-n_j+(b_k-1)n_k,
\quad PF(H)=\{f_A,f_B\}.
\]
We also use the cyclic versions of these formulas. For a primitive tail,
\[
n_1=a_2a_3+a_3b_2+b_2b_3,\quad
n_2=a_1a_3+a_1b_3+b_1b_3,\quad
n_3=a_1a_2+a_2b_1+b_1b_2.
\]
The later cross-product comparisons retain any positive common scale.

## Symmetry operations

A cyclic permutation acts simultaneously on all indices. Color reversal is the combination of an odd permutation and the interchange of all \(a\)- and \(b\)-parameters. The operation reversing the pivot in PATH and the operation interchanging \(j\) and \(k\) in CHAIN are given with their full parameter transformations in P5, [R7](#fr-R7), and [E8](#fr-E8), respectively. These operations leave \(\Gamma,F,m,W\) and the set of actual pseudo-Frobenius elements unchanged.

## Discipline for representations and proof steps

An actual factorization is a representation by the generators with all coefficients nonnegative integers. A signed equality or a completed zero identity is not, by itself, an actual factorization. Whenever the final contradiction uses a coefficient vector, its nonnegativity is stated explicitly. Herzog criticality is applied only after the coefficient of \(m\) has been completely eliminated, so that the relation lies entirely in \(H\). A support replacement is performed only when the source occurs coefficientwise within an explicitly identified factorization of the same actual element. Every extremal choice used below is accompanied by the underlying finite set or well-ordering argument.

## Scope of notation {#notation-scope}

For traceability to the source notation, we do not globally rename the principal symbols. The following symbols have local scopes and should not be identified across the different rows of the table.

| Symbol | Principal scope and meaning |
|---|---|
| \(Q\) | In Section 2, \(Q(\Gamma)=PF(\Gamma)\setminus\{F\}\) is a set. In Section 8, \(Q=U_j+1\); in the latter part of D in Section 9, \(Q=\tau_0\) is a local integer. |
| \(H\) | Throughout, the three-generated tail \(H=\langle n_1,n_2,n_3\rangle\). In Section 10, \(H_p=T+w\) is a local packet coefficient. |
| \(C\) | In Sections 7--9, the \(n_k\)-coefficient of the CORE-ROOT. In Appendix B, a \(3\times3\) matrix \(C\). |
| \(T\) | In CHAIN/CENTRAL, \(T=b_k+\alpha\). In Section 3 and Appendix A, \(T=\langle u,v\rangle\) is the two-generated semigroup in the symmetric tail. |
| \(A,B\) | In Sections 4--7, labels for the two colors and arm families. In Sections 9--10, capital \(A,B\) are local Euclidean-source coefficients. |
| \(E\) | A packet coefficient in Sections 9--10: in the initial embedding \(E=R+\upsilon\), and in the abstract theorem \(E=R+u\). It is distinct from the return labels \(EA,EB\). |
| \(L,M\) | In Sections 4 and 8, local return levels. In Section 10, the row sums \(L=p+q,\ M=s+t\) of the source matrix. |
| \(\Delta\) | Not a single global variable. Examples are \(\Delta_j,\Delta_k\) in G4 and \(\Delta_0\) in CENTRAL; each indexed local difference is read from its point of definition. |
| \(\theta\) | Appears in the initial packet of Section 9 as \(\theta=Q-fE\) and is then carried unchanged into the Euclidean package in Section 10. |
| \(\chi\) | A coefficient from the strict-packet/D analysis in Sections 8--9, embedded as a packet coefficient in Section 10. After a nonterminal transformation, \(\chi'=\theta\). |

Reuse of local notation is delimited by the definitions and anchors in the relevant sections. Equation tags, verifier keys, and JSON keys are retained unchanged for traceability.

## The two Apéry layers and supported returns {#fr-C2}

**C2.** Under the canonical condition of Sections 1--2, the following statements hold.

## Common setting

Let \(\Gamma=\langle m,n_1,n_2,n_3\rangle\) be a numerical semigroup, with \(m\) its multiplicity, \(F\) its Frobenius number, \(H=\langle n_1,n_2,n_3\rangle\), \(W=F+m\), and \(\mathcal A=\operatorname{Ap}(\Gamma,m)\). Let \(Q(\Gamma)=\operatorname{PF}(\Gamma)\setminus\{F\}\).

The canonical condition is

\[
W-\varphi\in\Gamma\quad(\varphi\in PF(\Gamma)).
\]

Every factorization of an element of \(\mathcal A\) contains no copy of \(m\), so \(\mathcal A\subseteq H\). Moreover \(W\in\mathcal A\), and for every \(w\in\mathcal A\) one has \(w-m\le F\), hence \(w\le W\).

## From the PF condition to the condition for every gap {#fr-C2.1}

Let x be a nonnegative gap. Choose the largest integer \(\varphi\) in the finite set \((x+\Gamma)\setminus\Gamma\). For every positive \(s\in\Gamma\), maximality gives \(\varphi+s\in\Gamma\). Thus \(\varphi\in PF(\Gamma)\), and \(\varphi-x\in\Gamma\).

\[
W-x=(W-\varphi)+(\varphi-x)\in\Gamma.
\]

This direction is therefore obtained directly, without invoking an external positioned-semigroup criterion.

## Exact two-layer decomposition {#fr-C2.2}

For \(w\in\mathcal A\), set \(b=W-w\ge0\). If \(w=0\), then \(b=W\in\mathcal A\). If \(w>0\), then \(x=w-m\) is a nonnegative gap, so the preceding subsection gives \(b+m=W-x\in\Gamma\).

- If \(b\in\Gamma\), then \(b-m\in\Gamma\) would imply \(w+(b-m)=F\in\Gamma\), so \(b\in\mathcal A\). In this case \(b+m\notin\mathcal A\).
- If \(b\notin\Gamma\), then \(b+m\in\Gamma\) and \((b+m)-m=b\notin\Gamma\), so \(b+m\in\mathcal A\).

Thus exactly one of the following holds: \(W-w\in\mathcal A\) or \(W+m-w\in\mathcal A\).

\[
\mathcal A_0=\{w\in \mathcal A:W-w\in \mathcal A\},\qquad \mathcal A_1=\mathcal A\setminus \mathcal A_0.
\]

If \(x\le_\Gamma y\) and \(y\in\mathcal A_0\), then \(W-x=(W-y)+(y-x)\in\Gamma\). Since its sum with the Apéry element \(x\) is \(W\), one has \(W-x\in\mathcal A\). Hence \(\mathcal A_0\) is a lower ideal and \(\mathcal A_1\) an upper filter.

On \(\mathcal A_1\), the map \(\iota(w)=W+m-w\) again takes values in \(\mathcal A_1\); moreover \(\iota^2=\mathrm{id}\) and \(\iota(x)-\iota(y)=y-x\). Thus \(\iota\) is an order-reversing involution.

The maximal elements of the Apéry set are \(PF+m\). Indeed, if \(q\in PF\), then \(q+m\in\mathcal A\); if a larger Apéry element differed from it by \(s>0\) in \(\Gamma\), then \(q+s\in\Gamma\), a contradiction. Conversely, if \(w\in\mathcal A\) is maximal, then \(q=w-m\) is a gap, and if \(q+s\) were a gap for some positive \(s\in\Gamma\), then \(w+s\in\mathcal A\), contrary to maximality.

If \(q\in Q\), then \(q<F\). The inclusion \(q+m\in\mathcal A_0\) would give \(W-(q+m)=F-q\in\Gamma\setminus\{0\}\), contradicting maximality. Together with the fact that \(\mathcal A_1\) is an upper filter, this yields

\[
\operatorname{Max}\mathcal A_1=(PF\setminus\{F\})+m,
\]
\[
\operatorname{Min}\mathcal A_1=\{W-q:q\in Q\},\qquad
|\operatorname{Min}\mathcal A_1|=|Q|=t-1.
\]

Moreover, \(\mathcal A_0=\{h\in H:W-h\in H\}\). For an element \(h\) on the right, if \(h-m\in\Gamma\) then \(F=(h-m)+(W-h)\in\Gamma\), so \(h\in\mathcal A\).

## KEY: direct proof of the support-zero return {#fr-C2.3}

Let \(q\in Q\) and \(c=W-q\in\Gamma\), and choose a direction \(i\) for which \(c-n_i\in H\). The pseudo-Frobenius property gives \(q+n_i\in\Gamma\).

If \(q+n_i-m\in\Gamma\), then

\[
F=(c-n_i)+(q+n_i-m)\in\Gamma,
\]

a contradiction. Therefore

\[
q+n_i\in \mathcal A\subset H.
\]

If a genuine \(H\)-factorization of this element had positive \(n_i\)-coefficient, removing one copy of \(n_i\) from that same factorization would put \(q\) in \(\Gamma\). Hence

\[
\boxed{c-n_i\in H\ \Longrightarrow\ q+n_i\in\langle n_j,n_k\rangle.}
\]

Since \(c=W-q>0\) lies in \(H\), the set \(D(c)\) is nonempty. Thus, with the conventions \(D(c)=\{i:c-n_i\in H\}\) and \(SH(q)=\{i:q+n_i\in H\}\), one has \(\varnothing\ne D(c)\subseteq SH(q)\). **Equality is not asserted.** No Hall-type existence theorem, factorization uniqueness, or generic connectivity is needed.

Furthermore, \(c-m=F-q\) is positive and does not lie in \(\Gamma\), so \(c\in\mathcal A\). Also \(x=c-n_i\in\mathcal A\), since \(x-m\in\Gamma\) would imply \(c-m\in\Gamma\). With \(y=q+n_i\) and \(h=q+m\),

\[
h,c,x,y\in H\cap \mathcal A,\quad h+c=W+m,\quad x+y=W.
\]

This conclusion is obtained separately for each supported direction. The classification of rows is carried out in G4.

## Tail gcd firewall {#fr-C2.4}

Assume \(Q\ne\varnothing\), and choose \(q\in Q\). Then \(q+m,W,c=W-q\) all lie in \(\mathcal A\subseteq H\). Hence

\[
m=(q+m)+(W-q)-W\in\mathbb ZH.
\]

Let \(d=\gcd(n_1,n_2,n_3)\). Then \(d\) also divides \(m\). Since \(\Gamma\) is a numerical semigroup, \(\gcd(m,n_1,n_2,n_3)=1\), and therefore \(d=1\).

The signed equality above is used only in the group \(\mathbb ZH\); it is not called a nonnegative factorization.

## Selection of four rows and minimality of the tail {#fr-C2.5}

Under the contradiction hypothesis, we may choose four distinct elements \(q_1,q_2,q_3,q_4\in Q(\Gamma)\). The Apéry and KEY statements above hold for all of \(Q\), hence simultaneously for these four selected rows. If one tail generator were a nonnegative combination of the other two, that generator would also be redundant in \(\Gamma\), contradicting \(\operatorname{edim}\Gamma=4\). Thus the tail is minimally generated. By [C2.4](#fr-C2.4), its gcd is one. Hence \(H\) is a genuine minimally three-generated numerical semigroup, and it is either symmetric or nonsymmetric.
