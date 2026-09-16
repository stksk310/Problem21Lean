# The symmetric three-generated tail {#sec-03}

We treat the case in which the minimally three-generated tail obtained in the previous section is symmetric. The main text establishes the correspondence between a stable ideal and the Apéry set, and Appendix A excludes the possibility that all four candidates survive by a complete case analysis. The two-generated semigroup \(T=\langle u,v\rangle\) and the coefficient notation in this section are local to this section and Appendix A.

## Exclusion of the symmetric tail {#fr-S3}

Let \(\Gamma=\langle m,x,y,z\rangle\) be a minimally four-generated numerical semigroup, with multiplicity \(m\). Assume that \(H=\langle x,y,z\rangle\) is symmetric and that
\[
m+F(\Gamma)-q\in\Gamma\qquad(q\in PF(\Gamma))
\tag{CAN}
\]
Then \(t(\Gamma)\le4\).

From now on write \(F=F(\Gamma)\), \(f=F(H)\), and \(Q=PF(\Gamma)\setminus\{F\}\). A minimal generator of an ideal of a semigroup means an element from which no positive semigroup element can be subtracted while remaining in the ideal.

## Stable core and the exact bridge {#fr-S3.2}

\[
K=\{a\in H:a+nm\in H\ (n\ge0)\},\qquad h=\min K.
\]
By symmetry and \(\Gamma=H+\mathbb N m\), for every integer \(t\),
\[
t\notin\Gamma\iff f-t\in K.
\tag{GAP-K}
\]
Hence \(F=f-h\). Since \(0\notin K\) (because \(m\notin H\)), we have \(h\ge\min(H\setminus\{0\})>m\). Put
\[
r=h-m=f-F-m>0,\qquad r+nm\in H\quad(n\ge1).
\tag{FS}
\]
The set \(K\) is a \(\Gamma\)-ideal, and GAP-K shows that \(q\mapsto f-q\) is a bijection from \(PF(\Gamma)\) onto \(\operatorname{Min}_\Gamma K\). Applying CAN to these minimal generators gives
\[
J:=K-r\subseteq\Gamma,\qquad \min J=m,\qquad m\in J.
\]
Set
\[
I_r=\{c\in H:c+r\in H\}
\]
By FS, \(c\in I_r\Rightarrow c+r\in K\), and therefore \(J\cap H=I_r\).

We now prove directly that
\[
\operatorname{Min}_\Gamma J
=\{m\}\sqcup(\operatorname{Min}_H I_r\cap\operatorname{Ap}(\Gamma,m)).
\tag{BRIDGE}
\]
Let \(j\in\operatorname{Min}_\Gamma J\setminus\{m\}\). If \(j-m\in\Gamma\), then \(j=m+(j-m)\), contrary to \(m\in J\) and the minimality of \(j\). Hence \(j\) lies in the Apéry set, and its factorizations contain no \(m\), so \(j\in H\). Minimality in \(H\) follows from minimality in \(\Gamma\).

Conversely, let \(c\in\operatorname{Min}_H I_r\cap\operatorname{Ap}\). Since \(J\subseteq\Gamma\), one has \(c-m\notin J\). If \(c-n\in J\) for some \(n\in\{x,y,z\}\), then \(c-n\in\Gamma\) and \(c-n-m\notin\Gamma\), so \(c-n\in H\), hence \(c-n\in J\cap H=I_r\). This contradicts minimality in \(H\), proving the reverse inclusion.

Thus
\[
t(\Gamma)=1+|\operatorname{Min}_H I_r\cap\operatorname{Ap}|.
\tag{TYPE-BRIDGE}
\]
We now assume \(t\ge5\) and derive a contradiction.

## Exact classification of RAW4 {#fr-S3.3}

By the standard complete-intersection classification, after permuting the generators we may write
\[
x=du,\quad y=dv,\quad z=w,\quad H=\langle du,dv,w\rangle,
\quad \gcd(u,v)=\gcd(d,w)=1,\quad w\in T.
\]
Since \(H\) is minimally three-generated, \(d,u,v\ge2\). Every integer has a unique expression \(jw+dt\), with \(0\le j<d\), and membership in \(H\) is equivalent to \(t\in T\). Consequently
\[
f=(d-1)w+dF_T.
\]
Write \(r=sw+d\rho\), with \(0\le s<d\). If \(s=0\), the raw minima of \(I_r\) occur only in the layer \(j=0\), and the two-generated lemma below gives at most two of them. Henceforth assume \(1\le s\le d-1\). The only layers containing raw minima of \(I_r\) are \(j=0\) and \(j=d-s\), coming respectively from the \(T\)-minima of
\[
J_0=\{t\in T:t+\rho\in T\},\quad J_1=\{t\in T:t+\rho+w\in T\}
\]
Every other layer allows one copy of \(w\) to be subtracted.

For every \(\eta=pu+qv\), \(0\le q<u\), the set \(\{t\in T:t+\eta\in T\}\) has at most two generators. Indeed, writing \(t=au+bv\), \(0\le b<u\), the required threshold for \(a\) takes only the two values
\[
\max(0,-p)\quad(b<u-q),\qquad \max(0,-p-v)\quad(b\ge u-q)
\]
The two minima are distinct and incomparable exactly when \(0<q<u,-v<p<0\). In that case, putting
\[
A=-p, C=q, B=u-q, D=v+p,\quad A+D=v, B+C=u,
\]
the minima are \(Au\) and \(Bv\), and their images are \(Cv\) and \(Du\).

Hence \(|\operatorname{Min}_H I_r|\le4\). Since \(t\ge5\), TYPE-BRIDGE implies that all four minima exist and all four remain in the Apéry set. With positive integers \(A,B,C,D\) and their primed versions, the four pairs are
\[
(c_x,a_x)=(Ax,sw+Cy),\quad(c_y,a_y)=(By,sw+Dx),
\]
\[
(c'_x,a'_x)=((d-s)w+A'x,C'y),\quad
(c'_y,a'_y)=((d-s)w+B'y,D'x),
\tag{RAW4}
\]
where in every case \(a=c+r\), \(A+D=A'+D'=v\), and \(B+C=B'+C'=u\). Moreover
\[
\rho=uv-Au-Bv=-Au+Cv=-Bv+Du.
\]

## Cross-layer rigidity and actual pseudo-Frobenius input {#fr-S3.4}

If \(A'\ge A\), then \(c'_x-c_x=(d-s)w+(A'-A)x\in H\), contradicting raw incomparability. Hence \(\alpha:=A-A'>0\). Similarly \(\beta:=B-B'>0\). Subtracting the threshold formulas for the two layers gives
\[
\begin{aligned}
w&=\alpha u+\beta v,\quad A'=A-\alpha>0,\quad B'=B-\beta>0,\\
C'&=C+\beta,\quad D'=D+\alpha.
\end{aligned}
\tag{CROSS-LAYER}
\]

By BRIDGE, the four raw rows correspond to actual pseudo-Frobenius rows \(q=f-a\). In particular,
\[
c_x-m,c_y-m,c'_x-m,c'_y-m\notin\Gamma.
\tag{ALL-AP}
\]
If \(a_x-m\in H\), then \(a_x\in K\) implies \(a_x-m\in K\); applying CAN would then give \(c_x-m\in\Gamma\), impossible. The same argument applies on the \(y\)-side. By symmetry of \(H\),
\[
q_x+m,q_y+m\in H.
\tag{QM}
\]

## Complete division into Branch I and Branch II {#fr-S3.5}

Write \(m=ew+d\mu\), with \(0\le e<d\). Since \(m\notin H\), \(\mu\notin T\). Put \(\ell=d-1-s\) and
\[
k_0=\left\lfloor\frac{\ell+e}{d}\right\rfloor\in\{0,1\},
\qquad\theta=\mu+k_0w
\]
From the representation of \(f\),
\(q_x=\ell w+d((B-1)v-u)\) and \(q_y=\ell w+d((A-1)u-v)\). Thus QM becomes
\[
\theta+(B-1)v-u\in T,\qquad\theta+(A-1)u-v\in T.
\]
Applying 2GI to \(X=\theta+(A-1)u+(B-1)v\) gives
\[
\theta-u-v\in T\qquad\text{or}\qquad\theta-\rho-u-v\in T.
\tag{SPLIT}
\]
We call the left condition Branch I and the right condition Branch II. Their possible overlap causes no difficulty. We first exclude Branch I.

### Two-generated calculations and completion of the case analysis {#sym-branches}

The normal form and intersection formula for the two-generated semigroup used here are proved in [S3.1](#fr-S3.1) of Appendix A. It remains to exclude the assumption that all four raw minima survive in the Apéry set. The two conditions in SPLIT cover the entire range. Allowing overlap, contradictions are obtained in the following order.

| Condition | Constraint obtained from the same element | Location of the contradiction |
|---|---|---|
| Branch I | The same stable walk hits all four sets \(U_x,U_y,Z_x,Z_y\) | [S3.6](#fr-S3.6)--[S3.7](#fr-S3.7) |
| Branch II, \(k_0=1\) | Backward points of the two D-rows and the two-generated intersection formula | [S3.8](#fr-S3.8): reduction to Branch I |
| Branch II, \(k_0=0,e=0\) | The first stable coordinate is negative | [S3.9](#fr-S3.9) |
| Branch II, \(k_0=0,e>0\) | The cross-core complement identity and the actual predecessor | [S3.10](#fr-S3.10): contradiction to the pseudo-Frobenius property |

In Branch I, we first separate the case in which the return index is one. If both rectangle hits were later returns, the first stable point would be a gap, so at least one of them must be the first return. Classifying that point as X-only, Y-only, or XY, the first two possibilities lack the required \(U_x\) or \(U_y\) hit, respectively, while in the XY case the second stable point is a gap. The key point in this branch is not to apply to the first return a predecessor constraint that is valid only for later returns.

For Branch II with \(k_0=1\), we first establish positivity of the auxiliary quantity and then move backward along the two D-rows. Since both backward points are gaps, symmetry of the two-generated semigroup and the intersection formula imply the Branch I condition. When \(k_0=0\), the case \(e=0\) is excluded directly. For \(e>0\), we distinguish whether a carry occurs. Either the complement representation lies in the semigroup or the actual immediately preceding stable point is a gap; in the final step this contradicts the pseudo-Frobenius property of the same \(q_x\).

All of these calculations are given in Appendix A. Therefore the four raw minima cannot all remain in the Apéry set, and the assertion for the symmetric tail follows from BRIDGE.
