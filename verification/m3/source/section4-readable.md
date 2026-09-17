# Nonsymmetric factorization geometry and classification into three terminal configurations {#sec-04}

Assume that the three-generated tail is nonsymmetric. We first classify the supported directions of a pseudo-Frobenius element into six arms, then establish coexistence restrictions for pairs of rows and exclude three arms of the same color. Finally, we exhaust the possibilities for four distinct rows selected from a putative counterexample and obtain three terminal configurations with their exact coefficient ranges.

## Common setting {#fr-G4.1}

Let \(\Gamma=\langle m,n_i,n_j,n_k\rangle\), let \(m\) be the multiplicity, let \(F=F(\Gamma)\), \(W=F+m\), and \(H=\langle n_i,n_j,n_k\rangle\). Canonical reduction gives

\[
q\in Q:=PF(Γ)\setminus\{F\}\Longrightarrow c_q=W-q\in Γ
\]

For every actual \(q\), we have \(q+m,c_q\in H\), \(c_q-m\notin\Gamma\), and \(q\notin\Gamma\), by the elementary canonical lemmas.

\[
SH(q)=\{r:q+n_r\in H\},\qquad D(c)=\{r:c-n_r\in H\}.
\]

KEY says \(\varnothing\ne D(c_q)\subseteq SH(q)\); equality is not assumed. The KEY implication itself follows directly: if \(q+n_r-m\in\Gamma\), then \(F=(c_q-n_r)+(q+n_r-m)\in\Gamma\), a contradiction.

For a cyclic order (i,j,k), we use the Herzog convention

\[
ρ_i=a_i+b_i,\quad ρ_in_i=b_jn_j+a_kn_k,
\]
\[
ρ_jn_j=a_in_i+b_kn_k,\qquad ρ_kn_k=b_in_i+a_jn_j,
\tag{H}
\]

where all \(a_r,b_r\) are positive integers and \(ρ_r\) is the critical multiplier of \(n_r\) in \(H\).

By KEY, \(SH(q)\) is nonempty. A row with \(SH(q)=\{r\}\) is called a singleton \(S_r\); a row with \(|SH(q)|=2\) is called a doubleton; and a row with \(SH(q)=\{i,j,k\}\) is called a corner. For a doubleton, the missing direction \(r\) is defined by \(r\notin SH(q)\). The six-arm atlas for doubletons is given in [G4.1.1](#fr-G4.1.1):

\[
A_r(λ)=f_A-λn_r\quad(1≤λ≤a_r-1),
\]
\[
B_r(μ)=f_B-μn_r\quad(1≤μ≤b_r-1).
\]

The exact formulas for the pseudo-Frobenius corners, including all three cyclic representations, are

\[
f_A=(ρ_i-1)n_i+(a_j-1)n_j-n_k
      =-n_i+(ρ_j-1)n_j+(a_k-1)n_k,
\]
\[
f_B=(ρ_i-1)n_i-n_j+(b_k-1)n_k,
\qquad f_A-f_B=a_jn_j-b_kn_k.
\tag{PF}
\]

Two rows on the same arm, and a corner together with an arm of the same color, contradict the pseudo-Frobenius antichain property. There is at most one lower corner with triple support. A higher corner would give \(F(H)\ge F(Γ)\) while its corresponding \(q\) must satisfy \(q<F(Γ)\), a contradiction.

### Short proof of the six-arm atlas {#fr-G4.1.1}

Assume \(q\notin H\), \(q+n_j,q+n_k\in H\), and \(q+n_i\notin H\). Choose the largest integer \(\ell\ge0\) such that \(q+\ell n_i\notin H\). It exists because \(H\) is a numerical semigroup, and \(\ell\ge1\) because \(q+n_i\notin H\). Then \(f=q+\ell n_i\) satisfies \(f+n_i\in H\); moreover, adding \(\ell n_i\) to \(q+n_j,q+n_k\in H\) gives \(f+n_j,f+n_k\in H\). Hence \(f\in PF(H)=\{f_A,f_B\}\).

Suppose first that \(f=f_A\) and \(\ell\ge a_i\). The canonical formula is
\[
q+n_j=(a_i-ℓ-1)n_i+(ρ_k-1)n_k.
\]
Comparing this with a genuine H-factorization \(Xn_i+Yn_j+Zn_k\) gives
\[
(ρ_k-1-Z)n_k=(ℓ-a_i+1+X)n_i+Yn_j.
\]
The right-hand side is positive, so the coefficient on the left is positive and is strictly less than \(ρ_k\), contradicting criticality. Thus \(1\le\ell\le a_i-1\).

If \(f=f_B\), the same argument, using \(q+n_k=(b_i-\ell-1)n_i+(ρ_j-1)n_j\), gives \(\ell\le b_i-1\).

Conversely, for \(A_i(λ)\), \(1\le λ\le a_i-1\),
\[
q+n_j=(a_i-λ-1)n_i+(ρ_k-1)n_k\in H,
\]
\[
q+n_k=(ρ_i-λ-1)n_i+(a_j-1)n_j\in H.
\]
If either \(q\) or \(q+n_i\) belonged to \(H\), adding the missing nonnegative multiple of \(n_i\) would put \(f_A\) in \(H\), impossible. Thus both are gaps. The B-case follows from the corresponding two canonical formulas. The color and the depth are uniquely determined by the maximal \(\ell\) above.

This proves the six-arm atlas from STD_HERZOG.

## Basic actual antichain and coefficient constraints {#fr-G4.2}

For distinct pseudo-Frobenius rows \(q,q'\), neither \(q-q'\) nor \(q'-q\) lies in \(\Gamma\). Hence distinct complements \(c,c'\) also form a \(\Gamma\)-antichain.

For a singleton \(S_r\), KEY implies \(c_S=κ_r n_r\). If some H-factorization of \(c_S\) used another direction, then \(D(c_S)\subseteq\{r\}\) would fail. If \(κ_r\geρ_r\), relation (H) would provide such a factorization in the other directions. Therefore

\[
1≤κ_r≤ρ_r-1.
\tag{SR}
\]

There cannot be two singletons in the same direction, by comparability along the pure ray. If \(S_r\) exists, then in every H-factorization of every other complement the \(r\)-coordinate is at most \(κ_r-1\). Otherwise \(c-κ_rn_r\in H\), contradicting the complement antichain; if the difference were zero, the two rows would coincide.

Likewise, every H-factorization of \(W\) has \(r\)-coordinate at most \(κ_r-1\): if it contained \(κ_r\) copies, removing them would put \(q_S\) in \(H\). Since \(q_S+n_r\in H\), the maximum \(κ_r-1\) is attained.

The complement of an arm missing direction \(i\) uses no copy of \(n_i\) and has the form

\[
c=y n_j+z n_k,\qquad 0≤y<ρ_j,\quad0≤z<ρ_k.
\tag{CB}
\]

Indeed, if \(y\geρ_j\) or \(z\geρ_k\), relation (H) produces a representation involving \(n_i\), contradicting KEY. This two-coefficient representation is unique: the difference of two such representations would be a pure relation between \(n_j\) and \(n_k\), and any nonzero such relation would place a critical multiplier below \(ρ_j\) or \(ρ_k\) on one side.

## Critical-box uniqueness and an integer kernel basis {#fr-G4.3}

**Critical-box uniqueness.** There do not exist two distinct nonnegative factorizations for which every coordinate satisfies \(X_r<ρ_r\). Their difference would be a nonzero kernel vector. With three coordinates, one sign class consists of a single coordinate, and its absolute value is strictly below the corresponding \(ρ_r\), contradicting criticality.

**Integer basis.**

\[
r_j=(a_i,-ρ_j,b_k),\qquad r_k=(b_i,a_j,-ρ_k)
\]

form a basis of the integer kernel. They are linearly independent and span the real kernel. Given any integer kernel vector, subtract the floor multiples of its real coefficients to obtain

\[
v=xr_j+yr_k\in\mathbb Z^3,\qquad0≤x,y<1.
\]

If \(x+y>0\), then \(0<v_i<ρ_i\), \(-ρ_j<v_j<a_j\), and \(-ρ_k<v_k<b_k\). If \(v_j,v_k\le0\), criticality in direction \(i\) gives a contradiction. If \(v_j\ge0\), the negative \(k\)-coordinate has absolute value below \(ρ_k\), contradicting \(k\)-criticality. If \(v_k\ge0\), the same argument uses \(j\)-criticality. A nonzero all-nonnegative kernel vector is impossible because all \(n_r\) are positive. Therefore \(x=y=0\), and the original real coefficients were integers.

This lemma uses no hidden connectivity or global factorization uniqueness. Whenever uniqueness is invoked below, it is only the critical-box uniqueness stated explicitly above.

## Corners and singletons cannot coexist {#fr-G4.4}

Assume that the corner \(f_A\) and the singleton \(S_j\) coexist. Let \(c_0=W-f_A\in H\) and \(c_S=κn_j\), with \(κ\leρ_j-1\). For the same actual \(q_{S_j}\),

\[
q_S+n_i=f_A+c_0-κn_j+n_i
=(ρ_j-1-κ)n_j+(a_k-1)n_k+c_0\in H.
\]

Direction \(i\) is missing for \(S_j\), a contradiction. Cyclic permutation treats every singleton direction, and the case \(f_B\) follows by color reversal.

This is a stronger local coexistence exclusion than merely excluding corners among four selected rows. A corner with three arms of the opposite color and no singleton still requires the separate COLOR-CAP argument below.

## Synchronization of a matched \(A_i/B_i\) pair {#fr-G4.5}

Take actual rows \(A_i(λ),B_i(μ)\) with complements

\[
c_A=y n_j+z n_k,\qquad c_B=y'n_j+z'n_k
\]

They satisfy the bounds in (CB). Let \(Δ_j=y'-y\) and \(Δ_k=z'-z\). Then

\[
v=(μ-λ,a_j-Δ_j,-b_k-Δ_k)\in\ker_\mathbb Z(n).
\]

By [G4.3](#fr-G4.3), write \(v=u r_j+v_0 r_k\), with \(u,v_0\in\mathbb Z\). The coordinate bounds are

\[
2-a_i≤v_i≤b_i-2,
\]
\[
1-b_j≤v_j≤ρ_j+a_j-1,\qquad v_k≤a_k-1.
\]

If \(u\ge1,v_0\le0\), then the \(j\)-coordinate is at most \(-ρ_j\), impossible. If \(u\le-1,v_0\ge1\), then the \(j\)-coordinate is at least \(ρ_j+a_j\), impossible. If \(u\ge0,v_0\ge1\), then the \(i\)-coordinate is at least \(b_i\), impossible. If \(u\le-1,v_0\le0\), then the \(i\)-coordinate is at most \(-a_i\), impossible. The remaining case \(u=0,v_0\le-1\) gives \(k\geρ_k\), also impossible. Thus \(u=v_0=0\).

Therefore

\[
λ=μ,\qquad y'=y+a_j,\qquad z'=z-b_k.
\]

Putting \(g=y\ge0\) and \(α=z'\ge0\), we obtain

\[
P=ρ_i-λ,\quad R=a_j+g<ρ_j,\quad T=b_k+α<ρ_k,
\]
\[
c_A=g n_j+Tn_k,\qquad c_B=Rn_j+αn_k,
\]
\[
W=(P-1)n_i+(R-1)n_j+(T-1)n_k.
\tag{MATCH}
\]

Moreover \(P>a_i,b_i\), \(g\le b_j-1\), and \(α\le a_k-1\). We do not assume strict positivity of \(g\) or \(α\); the boundary cases \(g=0\) and \(α=0\) are included.

### Matched pair and singleton {#fr-G4.5.1}

If \(S_j\) exists, then \(κ_j<ρ_j\). The complement antichain and \(c_B=Rn_j+αn_k\) imply \(κ_j>R\) (if equality holds and \(α=0\), the complements coincide; otherwise they are comparable). For the same \(q_{S_j}\),

\[
q_{S_j}+n_k=(P-1)n_i+(R-κ_j-1)n_j+Tn_k
\]

Using \(a_in_i+b_kn_k=ρ_jn_j\) once gives

\[
q_{S_j}+n_k=(P-a_i-1)n_i+(R-κ_j-1+ρ_j)n_j+αn_k\in H.
\]

Since \(P-a_i-1=b_i-λ-1\ge0\) and \(κ_j\leρ_j-1\), all coefficients are nonnegative, contradicting the missing direction \(k\).

The case \(S_k\) is dual: \(κ_k>T\), and replacing \(b_in_i+a_jn_j\) by \(ρ_kn_k\) in \(q_{S_k}+n_j\) again gives a nonnegative H-representation. Thus the only singleton that could coexist with a matched pair at this stage is \(S_i\).

## Root-free matched-pair level rigidity {#fr-M4}

Fix the same actual matched pair of [G4.5](#fr-G4.5), with \(q_A=A_i(\lambda),q_B=B_i(\lambda)\), \(\delta=a_i-\lambda\ge1,\beta=b_i-\lambda\ge1\), and \(g,\alpha\ge0\). Let \(P=\rho_i-\lambda,R=a_j+g,T=b_k+\alpha\). Then there exist a positive integer \(L\) and nonnegative integers \(t,u\) such that
\[
q_A+n_i=Lm+(a_j+t)n_j+un_k,\qquad
q_B+n_i=Lm+tn_j+(u+b_k)n_k,
\]
\[
Pn_i=Lm+(t+1)n_j+(u+1)n_k.
\]
The proof retains the cases \(g=0\) and \(α=0\). Below, we refer to the complement representations in [G4.5](#fr-G4.5) as COMP.

## Actual positive-m returns can be chosen independently {#fr-M4.2}

By the pseudo-Frobenius property, \(E_A=q_A+n_i\) and \(E_B=q_B+n_i\) belong to \(\Gamma\). No \(\Gamma\)-factorization of either element can contain \(n_i\), since removing one copy of \(n_i\) from that same nonnegative coefficient vector would put \(q_A\) or \(q_B\) in \(\Gamma\).

Moreover, neither \(E_A\) nor \(E_B\) lies in \(H\). We give the short pure-H proofs separately.

### \(E_A\notin H\)

Suppose \(E_A=Xn_j+Yn_k\), with \(X,Y\ge0\). The canonical formula gives

\[
Pn_i=(X-a_j+1)n_j+(Y+1)n_k.
\]

If \(X\ge a_j-1\), this contradicts criticality because \(0<P<ρ_i\).

If \(X\le a_j-2\), then

\[
(Y+1)n_k=Pn_i+(a_j-1-X)n_j.
\]

Criticality gives \(Y+1\geρ_k\). Subtracting \(R_k\) once yields

\[
δn_i=(X+1)n_j+(Y+1-ρ_k)n_k.
\]

This contradicts \(0<δ<ρ_i\). The coefficient of \(m\) has been zero throughout; hence the applications of criticality are legitimate.

### \(E_B\notin H\)

Similarly, if \(E_B=Xn_j+Yn_k\), then

\[
Pn_i=(X+1)n_j+(Y-b_k+1)n_k.
\]

If \(Y\ge b_k-1\), then \(P<ρ_i\) contradicts criticality. If \(Y\le b_k-2\), then

\[
(X+1)n_j=Pn_i+(b_k-1-Y)n_k,
\]

so \(X+1\geρ_j\). Subtracting \(R_j\) gives

\[
βn_i=(X+1-ρ_j)n_j+(Y+1)n_k,
\]

contradicting \(0<β<ρ_i\).

Thus both actual elements admit positive-m returns. For each element independently, choose the least positive coefficient of \(m\) occurring in a factorization and fix one factorization that realizes it:

\[
E_A=L_A m+U_jn_j+U_kn_k,\qquad
E_B=L_B m+V_jn_j+V_kn_k,
\tag{RET}
\]

\[
L_A,L_B\ge1,\qquad U_j,U_k,V_j,V_k\ge0.
\]

These are explicit minima of nonempty subsets of the positive integers. The semigroup, \(F,W,q_A,q_B\), and the canonical coefficients remain fixed; only the two nonnegative coefficient vectors in RET are chosen.

## Four coordinate caps {#fr-M4.3}

Adding RET and COMP and removing one copy of \(m\) gives two genuine representations of the same element \(F+n_i\):

\[
F+n_i=(L_A-1)m+(U_j+g)n_j+(U_k+T)n_k,
\]
\[
F+n_i=(L_B-1)m+(V_j+R)n_j+(V_k+α)n_k
\tag{FI}
\]

For example, if \(U_j+g\geρ_j\), replace the contained block \(ρ_jn_j\) by \(a_in_i+b_kn_k\). Removing the resulting copy of \(n_i\) from the same final representation would give \(F\in\Gamma\); the condition \(a_i\ge1\) supplies that copy. The other three cases are analogous, using \(R_j\) or \(R_k\). Hence

\[
U_j+g\leρ_j-1,\quad U_k+T\leρ_k-1,
\]
\[
V_j+R\leρ_j-1,\quad V_k+α\leρ_k-1.
\tag{CAP}
\]

## Uniform exclusion of unequal levels {#fr-M4.4}

Set

\[
t=U_j-a_j,\quad K=U_k+b_k,\quad
x=V_j-t,
\quad y=K-V_k.
\]

Using the canonical difference \(E_B=E_A-a_jn_j+b_kn_k\) and RET gives

\[
(L_A-L_B)m=xn_j-yn_k.
\tag{DIFF}
\]

CAP implies in particular

\[
-ρ_j<x<ρ_j,\qquad -ρ_k<y<ρ_k.
\tag{BOX}
\]

More precisely,

\[
R+1-ρ_j\le x\leρ_j-g-1,
\quad T+1-ρ_k\le y\leρ_k-α-1.
\]

### \(L_A>L_B\) is impossible {#fr-M4.4.1}

Let \(σ=L_A-L_B\ge1\). If \(V_k\ge b_k\), then

\[
E_A=L_Bm+(V_j+a_j)n_j+(V_k-b_k)n_k
\]

is an actual positive-m return for \(E_A\) at a strictly smaller level, contradicting the minimality of \(L_A\). Thus \(V_k\le b_k-1\).

Consequently \(C:=y=U_k+b_k-V_k\ge1\), and DIFF becomes

\[
σm+C n_k=Δ n_j,
\qquad Δ:=x>0.
\]

By BOX, \(Δ<ρ_j\).

Adding \(R_j\) as a completed zero identity yields the exact representation

\[
W=(β-1)n_i+(ρ_j+R-1)n_j+(α-1)n_k
\tag{WJ}
\]

of the same number \(W\). **If \(α=0\), the \(k\)-coefficient is \(-1\), so this is only a signed intermediate equality.** Add the completed identity \(σm+C n_k-Δn_j=0\), and use \(F=W-m\). Then

\[
\boxed{F=(σ-1)m+(β-1)n_i+(ρ_j+R-1-Δ)n_j+(α+C-1)n_k\inΓ.}
\tag{ABS+}
\]

Every coefficient in this final expression is nonnegative, a contradiction. In particular, when \(α=0\), the inequality \(C\ge1\) gives \(α+C-1\ge0\). No stronger bound such as \(σ\ge3\) or \(σ\ge5\) is needed.

### \(L_B>L_A\) is impossible {#fr-M4.4.2}

Let \(σ=L_B-L_A\ge1\). If \(t\ge0\), then

\[
E_B=L_A m+t n_j+K n_k
\]

is an actual positive-m return for \(E_B\) at a lower level, contradicting the minimality of \(L_B\). Hence \(t<0\).

Thus \(Δ:=x=V_j-t\ge1\), and DIFF becomes

\[
σm+Δn_j=Cn_k,\qquad C:=y>0.
\]

By BOX, \(C<ρ_k\).

Adding \(R_k\) as a completed zero identity yields the exact representation

\[
W=(δ-1)n_i+(g-1)n_j+(ρ_k+T-1)n_k
\tag{WK}
\]

of the same number \(W\). **If \(g=0\), the \(j\)-coefficient is \(-1\), so this is only a signed intermediate equality.** Adding \(σm+Δn_j-Cn_k=0\) and using \(F=W-m\) gives

\[
\boxed{F=(σ-1)m+(δ-1)n_i+(g+Δ-1)n_j+(ρ_k+T-C-1)n_k\inΓ.}
\tag{ABS-}
\]

Again all coefficients are nonnegative. In particular, when \(g=0\), \(Δ\ge1\) gives \(g+Δ-1\ge0\). This is a contradiction.

## Equal-level matching and exclusion of PRE {#fr-M4.5}

It follows that \(L_A=L_B=:L\). Then DIFF gives \(xn_j=yn_k\).

By BOX and tail criticality, \(x=y=0\). Indeed, if one is zero then both are zero, while if they are nonzero they have the same sign and \(|x|n_j=|y|n_k\) contradicts \(0<|x|<ρ_j\).

Hence

\[
V_j=t\ge0,\qquad V_k=U_k+b_k.
\]

Putting \(u:=U_k\), we obtain

\[
\boxed{E_A=Lm+(a_j+t)n_j+u n_k,\quad
E_B=Lm+t n_j+(u+b_k)n_k,\quad t,u\ge0.}
\tag{EA/EB}
\]

Comparison with the canonical formula for \(E_A\) gives

\[
\boxed{Pn_i=Lm+(t+1)n_j+(u+1)n_k.}
\tag{P-FIBER}
\]

The right-hand side is genuine. Thus the PRE region \(t<0\) has been excluded completely.

### Matched pair and extra arms {#fr-G4.5.2}

The root-free level theorem [M4](#fr-M4), using only (MATCH) and the two actual pseudo-Frobenius rows, gives

\[
q_A+n_i=Lm+(a_j+t)n_j+u n_k,
\]
\[
q_B+n_i=Lm+t n_j+(u+b_k)n_k,
\qquad L≥1,\ t,u≥0
\tag{EA/EB}
\]

No unit-root hypothesis is used in this synchronization.

Therefore the genuine factorization \(f_A=(q_A+n_i)+(λ-1)n_i\) has \(j\)-coordinate at least \(a_j\). If an actual \(A_j(μ)\), with \(μ\le a_j-1\), were present, then removing \(μn_j\) from this same factorization would put \(A_j\) in \(\Gamma\), a contradiction. Similarly, the \(k\)-coordinate of \(f_B\) is at least \(b_k\), so \(B_k\) cannot coexist.

Thus the only additional arms compatible with a matched pair in direction \(i\) are \(B_j\) and \(A_k\). We use this coexistence restriction in the classification below.

### A matched pair cannot coexist with \(S_i\) either {#fr-G4.5.3}

From (EA/EB),
\[
Pn_i=Lm+(t+1)n_j+(u+1)n_k
\]
so \(Pn_i-m\in\Gamma\). If the complement of the singleton \(S_i\) is \(κn_i\), then the genuine representation (MATCH) of \(W\) shows that \(κ\le P-1\) would imply \(q_{S_i}\in H\). Hence \(κ\ge P\). It follows that
\[
c_{S_i}-m=(κ-P)n_i+(Pn_i-m)\in Γ,
\]
contradicting the Apéry property of the actual complement. Thus a matched pair cannot coexist with any singleton. This eliminates all configurations containing both a matched pair and a singleton.

## Exact complement geometry for two arms of the same color {#fr-G4.6}

Take actual rows \(A_i(λ),A_k(ν)\). Write \(c_i=y n_j+z n_k\) and \(c_k=x n_i+y'n_j\). Then

\[
(λ+x,y'-y,-ν-z)=u r_j+v r_k.
\]

From \(i>0,k<0\), and \(|j|<ρ_j\), we get \(u\ge0,v\ge1\). The combination \(u\le-1,v\ge1\) contradicts \(j\geρ_j+a_j\); \(u\le-1,v\le0\) contradicts \(i>0\); and \(u\ge0,v\le0\) contradicts \(k<0\).

Since \(i\leρ_i+a_i-2\), we have \(u\le1\). Since \(-k\leρ_k+a_k-2\), we have \(v\le1\). Thus the only possibilities are \((u,v)=(0,1)\) or \((1,1)\).

**Case A:**
\[
c_i=y n_j+(ρ_k-ν)n_k,
\qquad c_k=(b_i-λ)n_i+(y+a_j)n_j.
\tag{AA-A}
\]

**Case B:**
\[
c_i=(y'+b_j)n_j+(a_k-ν)n_k,
\qquad c_k=(ρ_i-λ)n_i+y'n_j.
\tag{AA-B}
\]

The displayed coefficients come from the original genuine complement factorizations and are therefore nonnegative. In particular, Case A implies \(b_i-λ\ge0\).

### The singleton in the remaining direction \(S_j\) is impossible {#fr-G4.6.1}

In Case A,
\[
W=(ρ_i-λ-1)n_i+(a_j+y-1)n_j+(ρ_k-ν-1)n_k.
\]
Use \(a_i n_i+b_k n_k=ρ_j n_j\) once in \(q_{S_j}+n_i\):
\[
q_{S_j}+n_i=(b_i-λ)n_i+(a_j+y-κ_j-1+ρ_j)n_j+(a_k-ν-1)n_k\in H.
\]
All coefficients are nonnegative, contradicting the missing direction \(i\).

In Case B,
\[
W=(ρ_i-λ-1)n_i+(ρ_j+y'-1)n_j+(a_k-ν-1)n_k.
\]
Since \(κ_j\leρ_j-1\), the element \(q_{S_j}=W-κ_jn_j\) itself belongs to \(H\), a contradiction.

### Two simultaneous singletons \(S_i,S_k\) are also impossible {#fr-G4.6.2}

Case A: if \(y=0\), then \(c_i\) lies on the pure \(k\)-ray and is comparable with \(c_{S_k}\). Thus \(y\ge1\). By antichain incomparability, \(κ_k>ρ_k-ν\). In the above expression for \(W\), replace \(b_i n_i+a_j n_j\) by \(ρ_k n_k\) in \(q_{S_k}+n_i\). This gives
\[
q_{S_k}+n_i=(a_i-λ)n_i+(y-1)n_j+(ρ_k-ν-κ_k-1+ρ_k)n_k\in H.
\]
The last coefficient is at least \(ρ_k-ν\ge1\), since \(κ_k\leρ_k-1\). This contradicts the missing direction \(i\).

Case B: if \(y'=0\), then \(c_k\) lies on the pure \(i\)-ray and is comparable with \(c_{S_i}\), so \(y'\ge1\). Replacing \(ρ_j n_j\) by \(a_i n_i+b_k n_k\) in \(q_{S_i}+n_k\) yields
\[
q_{S_i}+n_k=(ρ_i-λ+a_i-κ_i-1)n_i+(y'-1)n_j+(ρ_k-ν)n_k\in H.
\]
The first coefficient is at least \(a_i-λ\ge1\), contradicting the missing direction \(k\).

Thus two same-color arms cannot coexist with two singletons. Color reversal gives the corresponding statement for two B-arms.

## Two arms of different colors and different directions: the two orientations {#fr-G4.7}

### The orientation \(B_i(λ),A_k(ν)\) {#fr-G4.7.1}

Write \(c_{B_i}=y n_j+z n_k\) and \(c_{A_k}=x n_i+y'n_j\). Then
\[
(λ+x,a_j-y+y',-b_k-ν-z)=u r_j+v r_k.
\]

The bounds \(i>0\), \(-b_j<j<ρ_j+a_j\), \(-k<2ρ_k\), and \(i<ρ_i+b_i\) force \((u,v)=(0,1)\): mixed signs contradict either the \(j\)-bound or \(i>0\); \(u\ge1,v=1\) gives \(j\le-b_j\); \(u\ge1,v\ge2\) gives \(i\geρ_i+b_i\); and \(u=0,v\ge2\) gives \(-k\ge2ρ_k\).

Hence, with positive integers \(β=b_i-λ\), \(α=a_k-ν\), and \(R=y=y'\ge0\),
\[
c_{B_i}=R n_j+αn_k,\qquad c_{A_k}=βn_i+R n_j.
\tag{BA}
\]

An exact expression for \(W\) is
\[
W=(a_i+β-1)n_i+(R-1)n_j+(b_k+α-1)n_k
\]
If \(R=0\), however, this expression is signed. We call only the following completed expression actual:
\[
W=(β-1)n_i+(R+ρ_j-1)n_j+(α-1)n_k.
\tag{BA-W}
\]
It is obtained from \(a_i n_i+b_k n_k=ρ_j n_j\) and has all coefficients nonnegative.

If \(S_j\) existed, then \(κ_j\leρ_j-1\), and (BA-W) would imply \(q_{S_j}\in H\), a contradiction. Hence any singleton must be in direction \(i\) or \(k\).

### The opposite orientation \(A_i(λ),B_k(ν)\) {#fr-G4.7.2}

Similarly, the kernel vector is
\[
(λ+x,-a_j-y+y',b_k-ν-z)=u r_j+v r_k.
\]

The bounds \(i>0\), \(-ρ_j-a_j<j<b_j\), \(-ρ_k<k<b_k\), and \(i<ρ_i+a_i\) force \((u,v)=(1,1)\). Mixed signs violate the \(j\)- or \(k\)-bound; \(u=0\) or \(v=0\) violates the \(k\)-bound; \(u\ge2\) violates the \(i\)-bound; and \(v\ge2\) violates the \(k\)-bound.

Thus, with \(P=ρ_i-λ\), \(T=ρ_k-ν\), \(y\ge0\), and \(y'=y+a_j-b_j\ge0\),
\[
c_{A_i}=y n_j+Tn_k,\qquad c_{B_k}=Pn_i+y'n_j,
\]
\[
W=(P-1)n_i+(a_j+y-1)n_j+(T-1)n_k.
\tag{AB-reverse}
\]

Assume \(S_i\) exists. If \(y'=0\), then there is pure-ray comparability, so \(y'\ge1\). Since \(a_j+y-1=b_j+y'-1\ge b_j\) and \(T-1\ge a_k\), we may replace \(b_jn_j+a_kn_k\) by \(ρ_in_i\):
\[
W=(P+ρ_i-1)n_i+(y'-1)n_j+(b_k-ν-1)n_k.
\]
Since \(κ_i\leρ_i-1\), this gives \(q_{S_i}\in H\), a contradiction.

Assume \(S_k\) exists. If \(y=0\), there is pure-ray comparability, so \(y\ge1\). Since \(P-1\ge b_i\) and \(a_j+y-1\ge a_j\), replace \(b_i n_i+a_j n_j\) by \(ρ_k n_k\):
\[
W=(a_i-λ-1)n_i+(y-1)n_j+(T+ρ_k-1)n_k.
\]
Since \(κ_k\leρ_k-1\), this gives \(q_{S_k}\in H\), again a contradiction.

Thus the only singleton compatible with this opposite orientation is \(S_j\).

## If three singletons exist, then \(|Q|=3\) {#fr-G4.8}

Assume \(S_i,S_j,S_k\) exist. By [G4.2](#fr-G4.2), every factorization of \(W\) has all coordinates at most \(κ_r-1<ρ_r\). By critical-box uniqueness [G4.3](#fr-G4.3), \(W\) has a unique factorization. Since each maximal coordinate \(κ_r-1\) is attained,
\[
W=(κ_i-1)n_i+(κ_j-1)n_j+(κ_k-1)n_k.
\]

For any other row \(q\), antichain incomparability forces every coordinate of its complement \(c\) to be at most \(κ_r-1\). Thus any genuine factorization of \(c\) is contained coefficientwise in this same factorization of \(W\), and hence \(q=W-c\in H\), a contradiction.

No global factorization uniqueness is assumed here. The singleton caps first confine all factorizations to the critical box, and uniqueness then follows from [G4.3](#fr-G4.3).

## Excluding three same-color arms and connecting to the classification {#three-arm-bridge}

To exclude three arms of the same color, we follow the same tail pseudo-Frobenius element in the same semigroup. Let the color be \(\varepsilon\), and write the actual arms in the three directions as
\[
q_i=f_\varepsilon-\lambda_i n_i\in PF(\Gamma),\qquad
1\le\lambda_i\le\alpha_i-1
\]
Here \(\alpha_i\) is \(a_i\) for color A and \(b_i\) for color B. Choose, among nonnegative representations of \(f_\varepsilon\), one with the least positive coefficient of \(m\). Then
\[
f_\varepsilon=km+\sum_i(p_i-1)n_i,\qquad
1\le p_i\le\lambda_i\le\alpha_i-1
\]
The choice set is nonempty and the minimum exists by well-ordering of the positive integers.

In [A1.1](#fr-A1.1)--[A1.4](#fr-A1.4) of Appendix B, the three rows \(U_i\) representing the socle and the point \(p\) determine a tetrahedron in the relative lattice \(p+L_m\). A lattice point at an intermediate level would give a positive \(m\)-coefficient smaller than \(k\), while a nonvertex lattice point on the top face would imply \(f_\varepsilon\in H\). Hence the tetrahedron is empty and has relative volume \(k\). If \(k\ge2\), White's width-one theorem leaves only a partition of the four vertices into two pairs. For a class in the quotient lattice and its companion, minimality forbids simultaneous positivity of every coordinate. Writing these failure conditions for both colors produces a nonnegative weighted row vector \(v\) and a positive integer \(D\) with
\[
v\cdot n=kDm,\qquad |v|_1\ge kD
\]
contradicting \(n_i>m\). All six inequalities, weights, and coordinate sums for the two colors are recorded in [A1.5](#fr-A1.5)--[A1.8](#fr-A1.8). Therefore \(k=1\).

Orient the argument to color A. By [A1.9](#fr-A1.9), \(x=p\), \(y=a-p\), and \(z=y+b\) are positive and satisfy
\[
C=\begin{pmatrix}-x_1&z_2&y_3\\y_1&-x_2&z_3\\z_1&y_2&-x_3\end{pmatrix},
\qquad Cn=m\mathbf1
\]
Consider the operation of subtracting a row \(c_i\) inside the box \(\mathcal B=\prod_i[1,a_i-1]\cap\mathbb Z^3\). The three allowed source regions inside the box are pairwise disjoint, and each operation decreases \(u\cdot n\) by \(m\). Therefore every path is finite.

The possibility that a path terminates without an operation that exits the box while remaining positive is excluded by the exhaustive division below. In the two-color calculations, the integer-fraction separator is applied only to the initial prefix of crossings that actually succeeds. In the reciprocal-rank calculation, the dual count is first shown to correspond to points traversed by the original path, and only then are coordinate ranks counted. The relevant ranges and proofs are in [A2.3](#fr-A2.3)--[A2.4](#fr-A2.4).

| Rows used by the path | Proof excluding termination |
|---|---|
| One row only | Weighted certificate for every sink in [A2.6](#fr-A2.6) |
| Rows 1 and 2 | Last-row, pre-cross, and sink-by-sink analysis in [A2.7](#fr-A2.7) |
| Rows 1 and 3 | Last-row and sink-by-sink analysis in [A2.8](#fr-A2.8) |
| All three rows | Two directions for the first occurrence of the third color in [A2.9](#fr-A2.9) |

The weighted-certificate principle is that \(v=\lambda C\ge0\) and \(|v|_1\ge|\lambda|_1>0\) imply
\[
|\lambda|_1m=v\cdot n>|v|_1m\ge|\lambda|_1m
\]
a contradiction. Appendix B retains the margins for every sink. Hence a maximal path inside the box has a positive exit.

After a total of \(t\) operations, let \(u=p-rC\), with \(|r|_1=t\). The same element being tracked has the representation
\[
f_A=(t+1)m+\sum_i(u_i-1)n_i
\]
At a positive exit all coefficients are still nonnegative, and \(u_i\ge a_i\) for some \(i\). Hence \(u_i-1\ge a_i-1\ge\lambda_i\), and removing \(\lambda_i n_i\) from this single representation gives \(q_i\in\Gamma\), a contradiction. For color B, simultaneously exchange the indices, all \(a/b\)-parameters, the arm elements, and their ranges; the same argument applies.

Thus three arms of the same color cannot exist. Two depths on the same arm, and a corner together with an arm of the same color, are also incompatible by pseudo-Frobenius incomparability. Therefore, for each color, there are at most two corner/arm rows. This conclusion, including the cases involving a corner, is used in the four-row classification below.

## Exhaustive classification of four rows {#fr-G4.9}

Choose four distinct actual \(Q\)-rows. Let \(s\) be the number of singletons, \(c\) the number of corners, and \(a\) the number of arms.

**Case with a corner.** By [G4.4](#fr-G4.4), no singleton is present. A corner cannot coexist with an arm of the same color by antichain incomparability. Hence if \(c=1,a=3\), the three arms all have the opposite color. Duplicates of an arm are impossible, so all three directions occur. At this point we apply [Proposition B.1 (THREE-ARM / COLOR-CAP)](#prop-B1) from Appendix B.

Henceforth \(c=0\). By [G4.8](#fr-G4.8), \(s\le2\).

**\(s=2,a=2\).** By [G4.5.1](#fr-G4.5.1), a matched pair allows a singleton in at most one direction. By [G4.6](#fr-G4.6), two same-color arms cannot coexist with two singletons. The opposite orientation in [G4.7.2](#fr-G4.7.2) likewise allows a singleton in only one direction. Therefore the orientation is that of [G4.7.1](#fr-G4.7.1), with singletons in directions \(i,k\). The configuration is exactly
\[
S_i,\quad B_i(λ),\quad A_k(ν),\quad S_k
\]
which we call PATH.

**\(s=1,a=3\).** If the three arms have the same color, they occupy all three directions. Applying [G4.6.1](#fr-G4.6.1) to the two arms outside the singleton direction gives a contradiction. Thus the color distribution is \(2+1\).

If a matched pair were present, [G4.5.3](#fr-G4.5.3) would exclude coexistence with the singleton. Hence no matched pair occurs in this case.

Up to cyclic permutation and full color reversal, the remaining candidate
\[
S_i,\quad A_i(λ),\quad B_i(λ),\quad A_k(ν)
\]
contains a matched pair in direction \(i\) together with the singleton \(S_i\), and is therefore already excluded by [G4.5.3](#fr-G4.5.3). It need not be treated as an independent terminal branch.

If there is no matched pair, the three missing directions are all distinct. Write the two same-color arms as \(A_i,A_k\) and the opposite-color arm as \(B_j\). Applying the opposite-orientation pair [G4.7.2](#fr-G4.7.2) to \(A_k,B_j\) shows that the only possible singleton is \(S_i\). Thus the configuration is exactly
\[
S_i,\quad A_i(λ),\quad B_j(μ),\quad A_k(ν)
\]
which we call TYPE II.

**\(s=0,a=4\).** There are three directions, and each color contributes at most one copy of any given arm, so in some direction \(i\) both \(A_i\) and \(B_i\) occur. By [G4.5.2](#fr-G4.5.2), the only additional arms are \(B_j\) and \(A_k\). Hence the configuration is
\[
B_j(μ),\quad A_i(λ),\quad B_i(λ),\quad A_k(ν)
\]
which we call CHAIN.

Thus every actual four-row nonsymmetric counterexample reduces exhaustively to PATH, TYPE II, or CHAIN. The two coexistence restrictions for a matched pair were proved in [G4.5.2](#fr-G4.5.2)--[G4.5.3](#fr-G4.5.3).

## Extraction of the scalar input needed for the terminal proofs {#fr-G4.11}

### General singleton saturation lemma {#fr-G4.11.1}

Suppose the same actual \(W\) has the representation
\[
W=(P-1)n_i+(R-1)n_j+(T-1)n_k,
\quad1≤P≤ρ_i,\quad1≤R≤ρ_j,\quad1≤T≤ρ_k
\tag{BOX-W}
\]
and the complement of a singleton \(S_i\) is \(κ n_i\). By [G4.2](#fr-G4.2), every factorization of \(W\) has \(i\)-coordinate at most \(κ-1<ρ_i\), and the maximum \(κ-1\) is attained.

Let the difference between an arbitrary factorization of \(W\) and (BOX-W) be \(u r_j+v r_k\). If \(u\ge1,v\le0\), then the \(j\)-coordinate is at most \(R-1-ρ_j<0\). If \(u\le0,v\ge1\), then the \(k\)-coordinate is at most \(T-1-ρ_k<0\). If \(u,v\ge1\), then the \(i\)-coordinate is at least \(P-1+ρ_i\geρ_i\), contradicting the singleton cap. In the remaining case \(u,v\le0\), the \(i\)-coordinate is at most \(P-1\).

Hence the maximum is \(P-1\), so
\[
\boxed{κ=P.}
\]

The cyclic versions are identical. No global uniqueness of the factorization fiber is needed.

### The full canonical positive box for CHAIN {#fr-G4.11.2}

Take the CHAIN rows of [G4.9](#fr-G4.9). The matched pair in direction \(i\) gives (MATCH). Apply [G4.7.1](#fr-G4.7.1), in cyclic order \((j,k,i)\), to the right-oriented pair \(B_j(μ),A_i(λ)\). Then
\[
c_{A_i}=(b_j-μ)n_j+Tn_k,\qquad c_{B_j}=(a_i-λ)n_i+Tn_k.
\]
Comparison with the unique \(j/k\)-representation of the matched complement gives
\[
g=b_j-μ≥1,\quad R=ρ_j-μ.
\]
Similarly, from \(B_i(λ),A_k(ν)\),
\[
α=a_k-ν≥1,\quad T=ρ_k-ν,
\]
\[
c_{A_k}=(b_i-λ)n_i+Rn_j.
\]
Thus, with \(δ=a_i-λ≥1\) and \(β=b_i-λ≥1\),
\[
P=λ+δ+β,\quad R=a_j+g,\quad T=b_k+α
\]
and the four complements are
\[
c_{B_j}=δn_i+Tn_k,\quad c_{A_i}=g n_j+Tn_k,
\]
\[
c_{B_i}=Rn_j+αn_k,\quad c_{A_k}=βn_i+Rn_j.
\]
These positive coefficient ranges are the input for the root construction and the subsequent packet analysis in CHAIN.

### Full input for TYPE II {#fr-G4.11.3}

Take \(S_i,A_i(λ),B_j(μ),A_k(ν)\). Compare Case A/B of [G4.6](#fr-G4.6) for \(A_i,A_k\) with [G4.7.1](#fr-G4.7.1) for \(B_j,A_i\). In Case B, the \(j\)-coordinate of \(c_{A_i}\) would be simultaneously \(b_j+y'\) and \(b_j-μ\), forcing \(y'=-μ<0\), impossible. Hence Case A holds.

Consequently
\[
λ≤b_i,\quad P=ρ_i-λ,\quad R=ρ_j-μ,\quad T=ρ_k-ν,
\]
\[
c_{A_i}=(b_j-μ)n_j+Tn_k,
\]
\[
c_{A_k}=(b_i-λ)n_i+Rn_j,\qquad
c_{B_j}=(a_i-λ)n_i+Tn_k.
\]
Thus the same \(W\) has the form (BOX-W), and singleton saturation gives \(c_{S_i}=Pn_i\). Therefore
\[
q_{S_i}=-n_i+(R-1)n_j+(T-1)n_k.
\]
The arm-domain restrictions \(1\leλ\le a_i-1\), \(1\leμ\le b_j-1\), and \(1\leν\le a_k-1\), together with \(λ\le b_i\), are precisely the full input to [T6.1](#fr-T6.1).

### Canonical endpoint rays for PATH {#fr-G4.11.4}

From the PATH pair \(B_i(λ),A_k(ν)\), [G4.7.1](#fr-G4.7.1) gives \(α=a_k-ν>0\), \(β=b_i-λ>0\), and \(R\ge0\). If \(R=0\), then \(c_{A_k}=βn_i\) is comparable on the pure ray with \(c_{S_i}\), or is the same row, which is impossible. Hence \(R\ge1\).

The missing-\(i\) critical box for \(c_{B_i}\) gives \(R<ρ_j\). Thus
\[
P=a_i+β=ρ_i-λ,\quad T=b_k+α=ρ_k-ν,
\]
\[
W=(P-1)n_i+(R-1)n_j+(T-1)n_k
\]
has the form (BOX-W). Applying singleton saturation in directions \(i\) and \(k\) gives
\[
c_{S_i}=Pn_i,\qquad c_{S_k}=Tn_k.
\]
If we set \(q_L=q_{S_i},q_A=q_{A_k},q_B=q_{B_i},q_R=q_{S_k}\), then
\[
q_L+a_in_i=q_A+Rn_j,
\quad q_A+βn_i=q_B+αn_k,
\quad q_R+b_kn_k=q_B+Rn_j.
\]
This actual PATH ladder is passed to P5. Here \(q_A/q_B\) are only ladder labels and do not refer to the Herzog colors.

## How to read the input to the three terminal configurations {#terminal-input-table}

| Configuration | Four pseudo-Frobenius elements | Additional conditions used later | Eliminated in |
|---|---|---|---|
| Path | \(S_i,B_i(\lambda)\), \(A_k(\nu),S_k\) | The two endpoint complements are \(Pn_i,Tn_k\), and \(1\le R<\rho_j\) | Section 5 |
| Type II | \(S_i,A_i(\lambda)\), \(B_j(\mu),A_k(\nu)\) | \(\lambda\le b_i\), \(c_{S_i}=Pn_i\), and the full arm ranges in [G4.11.3](#fr-G4.11.3) | Section 6 |
| Chain | \(B_j(\mu),A_i(\lambda)\), \(B_i(\lambda),A_k(\nu)\) | \(\lambda,\delta,\beta,g,\alpha\ge1\), and the four complements in [G4.11.2](#fr-G4.11.2) | Sections 7--10 |

All three configurations live in the same \(\Gamma,F,m,W\). The table is only a reference to the coefficient ranges proved immediately above; the complete inputs are stated explicitly in the corresponding extraction propositions.
