# Auxiliary calculations and complete branching for the symmetric tail {#app-A}

## Elementary two-generator facts {#fr-S3.1}

Let \(T=\langle u,v\rangle\), with \(\gcd(u,v)=1\) and \(u,v\ge2\). Every integer has a unique representation

\[
a u+b v,\qquad a\in\mathbb Z,\quad0\le b<u
\]

and membership in \(T\) is equivalent to \(a\ge0\). The difference between any two integral coefficient representations is \((kv,-ku)\). The following consequences will be used.

* \(F_T=uv-u-v\), and for every integer \(t\), \(t\notin T\iff F_T-t\in T\). Indeed, the complementary representation to the normal form above is \((-a-1)u+(u-b-1)v\).
* If \(P<v,Q<u\) and \(Pu+Qv\in T\), then \(P,Q\ge0\). A primitive shift that repairs either negative coordinate makes the other coordinate negative.
* If \(P,Q>0\), then \(uv-Pu-Qv\notin T\). Otherwise one would obtain a representation of \(uv\) with both the \(u\)- and \(v\)-coefficients positive, whereas the integral solutions of \(Xu+Yv=uv\) are exactly \(X=v(1-k),Y=uk\).
* If \(0\le P<v,0\le Q<u\), then \(Pu+Qv-uv\notin T\). In \(v\)-normal form, the \(u\)-coefficient is \(P-v<0\).

Moreover, if \(0<A<v,0<B<u\), then

\[
(Au+T)\cap(Bv+T)=(Au+Bv+T)\cup(uv+T).
\tag{2GI}
\]

Indeed, write \(X=(A+p)u+qv=ru+(B+s)v\) with \(p,q,r,s\ge0\). If the primitive shift between the two representations is zero, both coefficients contain \(A\) and \(B\). If it is positive, the first \(u\)-coefficient is at least \(v\); if it is negative, the \(v\)-coefficient in the second representation is at least \(u\). Thus \(X\in uv+T\). The reverse inclusion is immediate from \(A<v,B<u\).

## Branch I: the walk and the necessity of four hits {#fr-S3.6}

Let \(\theta=L=u+v+t_0\), where \(t_0=p_0u+q_0v\in T\). If \(k_0=0\), then \(\mu=L\in T\), so \(k_0=1\). Hence

\[
\kappa=d-e,\quad 1\le\kappa\le d-1-s,\quad
m=dL-\kappa w,\quad E=w-L>0.
\]

The final positivity follows from \(m<w\) and \(\kappa+1\le d-s<d\). Define

\[
c_n=\left\lceil\frac{n\kappa-s}{d}\right\rceil,\quad
j_n=s-n\kappa+dc_n,\quad
\tau_n=\rho+nL-c_nw.
\]

FS is equivalent to \(\tau_n\in T\ (n\ge1)\). Each adjacent step is either \(L\) or \(L-w\). A return is an index with \(j_n=0\), equivalently \(n\kappa\equiv s\pmod d\).

The \(T\)-coordinate of \(a_x-y+nm\) is \(\tau_n+Au-v\). For \(\tau\) in \(T\),

\[
\tau+Au-v\notin T\iff\tau\in U_x:=\{ju:0\le j<D\}.
\]

This follows directly from the normal form in [S3.1](#fr-S3.1). Although \(a_x-y\in H\), actual pseudo-Frobenius behavior gives \(q_x+y\in\Gamma\), while GAP-K yields \(a_x-y\notin K\). Hence a hit of \(U_x\) is required for some \(n\ge1\). Dually, a hit is required in

\[
U_y=\{jv:0\le j<C\}
\]

Likewise, for \(a_x-w+nm\), every nonreturn index automatically gives an element of \(H\). At a return, the \(T\)-coordinate becomes \(\tau_n+A'u-\beta v\). This is a gap of \(T\) precisely when the same \(\tau_n\) lies in

\[
Z_x=\{pu+qv:0\le p<D',\ 0\le q<\beta\}
\]

Since \(a_x-w\in H\) and \(q_x+w\in\Gamma\), such a return hit is necessary. Dually, at a return one also needs a hit in

\[
Z_y=\{pu+qv:0\le p<\alpha,\ 0\le q<C'\}
\]

All four hits arise from the same actual pseudo-Frobenius pair and the same walk.

## Branch I: the four hits are incompatible {#fr-S3.7}

Write \(a=A'>0,b=B'>0\). Let \(\rho=uv-w-au-bv\). At a return index \(N\), one has \(c_{N-1}=c_N\) and \(c_{N+1}=c_N+1\). Thus, if \(N>1\),

\[
\tau_{N-1}=\tau_N-L\in T.
\]

If \(\tau_N=pu+qv\in Z_x\) or \(Z_y\), then \(p<v,q<u\). Hence [S3.1](#fr-S3.1) gives

\[
p\ge p_0+1,\qquad q\ge q_0+1.
\tag{LOWER}
\]

We do not impose this restriction when \(N=1\).

If both the \(Z_x\)- and \(Z_y\)-hits occur at indices \(N>1\), then \(R=\alpha-p_0-1>0\) and \(Q=\beta-q_0-1>0\). But \(c_1\in\{0,1\}\), and

\[
\tau_1=uv-(a+R)u-(b+Q)v-c_1w\notin T
\]

(after substituting the positive coefficient representation of \(w\) and applying [S3.1](#fr-S3.1)). Hence one of the return hits must occur at \(N=1\), and in particular \(\kappa=s\). The base point \(\tau_1\) splits into the three cases X-only, Y-only, and XY.

In general, a later hit \(\tau_N=ju\), \(j<D\), in \(U_x\) must occur through a carry. Without a carry,
\(\tau_{N-1}=(j-p_0-1)u-(q_0+1)v\notin T\). The dual statement holds for \(U_y\).

**X-only.** The \(Z_y\)-hit is later, so LOWER gives \(p_0\le\alpha-2,q_0\le u-b-2\). Put \(R=\alpha-p_0-1>0\) and \(S=q_0+1-\beta\). Then

\[
w-L=Ru-Sv,\qquad\tau_1=(v-a-R)u+(S-b)v.
\]

Both coefficients lie below the upper edge of the fundamental strip, so FS implies \(S\ge b\). Also \(1\le R\le\alpha-1,1\le S<u\). For the base point to lie in \(U_x\), one would need \(S=b\), but then its \(u\)-coefficient \(v-a-R\ge D+1\) is too large. If there were a later \(U_x\)-hit, its carry predecessor would be \((j+R)u-Sv\); however, \(j+R\le v-a-2<v\) and \(0<S<u\), so this is a \(T\)-gap. Hence there is no \(U_x\)-hit.

**Y-only.** The same argument, with \(u\leftrightarrow v\), \(A\leftrightarrow B\), \(\alpha\leftrightarrow\beta\), and \(a\leftrightarrow b\), shows that there is no \(U_y\)-hit.

**XY.** The coordinate representation in both rectangles is unique in the range \(p<v,q<u\), so

\[
\tau_1=pu+qv,\quad 0\le p<\alpha,\quad 0\le q<\beta.
\]

\[
E=uv-(a+p)u-(b+q)v,\qquad
\tau_2=(2p+a)u+(2q+b)v-uv.
\]

If the \(U_x\)-hit occurs at the base point, then also \(p\le D-1\), and hence \(2p+a\le(\alpha-1)+(D-1)+a=v-2\). If a later hit is \(ju\) with \(j<D\), then its carry predecessor is

\[
ju+E=uv-(a+p-j)u-(b+q)v.
\]

The interior-gap criterion from [S3.1](#fr-S3.1) gives \(j\ge a+p\). Together with \(p\le\alpha-1\), this again yields \(2p+a<v\). Dually, the \(U_y\)-hit forces \(2q+b<u\). Therefore the final gap criterion in [S3.1](#fr-S3.1) gives \(\tau_2\notin T\), contradicting FS.

Thus the four hits are incompatible in all three cases, and Branch I is eliminated.

## Branch II, \(k_0=1\): D-row drop or Branch I {#fr-S3.8}

Let \(\theta=\rho+u+v+t_0\), with \(t_0\in T\). If \(k_0=1\), then \(e\ge s+1\), \(\kappa=d-e>0\), and

\[
\mu=\theta-w,\qquad m=d\theta-\kappa w,\qquad
\kappa w<d\theta<(\kappa+1)w.
\]

Set \(g=w-u-v-t_0=w-\theta+\rho\). We record explicitly that \(g>0\): from \(r>0\), \(\rho>-sw/d\), and from \(m<w\), \(\theta<(\kappa+1)w/d\). Hence

\[
\theta-\rho<\frac{\kappa+s+1}{d}w\le w.
\tag{K1-g}
\]

The backward points of the two D-rows are

\[
a'_x-m=\kappa w+d(A'u+g),\qquad
a'_y-m=\kappa w+d(B'v+g).
\]

If either lies in \(H\), then it lies in \(K\), and CAN gives the corresponding \(c'-m\in\Gamma\), contradicting ALL-AP. Thus both are gaps of \(H\), so \(A'u+g,B'v+g\notin T\). By symmetry of \(T\),

\[
F_T-g\in(A'u+T)\cap(B'v+T).
\]

Apply 2GI. Since \(g>0\), one has \(F_T-g<uv\), so the \(uv+T\) component is impossible. Therefore

\[
F_T-g-A'u-B'v=\rho+t_0=\theta-u-v\in T.
\]

This is precisely Branch I, already eliminated. Hence the case \(k_0=1\) is also impossible.

## Branch II, \(k_0=0,e=0\) {#fr-S3.9}

Here \(\theta=\mu\notin T\) and \(m=d\theta\). By multiplicity,
\(0<\theta<\min(u,v)\). Since \(c_1=\lfloor(s+e)/d\rfloor=0\), the first stable coordinate is

\[
\tau_1=\rho+\theta=2\theta-u-v-t_0<0.
\]

This contradicts FS.

## Branch II, \(k_0=0,e>0\): cross-core exclusion {#fr-S3.10}

Write \(t_0=pu+qv\). Since \(\theta=\rho+u+v+t_0\notin T\), one has \(p\le A-2,q\le B-2\). Hence

\[
P=A-1-p>0,\quad R=B-1-q>0,\quad Q=u-R,\quad S=v-P,
\]
\[
\theta=-Pu+Qv=Su-Rv<0.
\tag{K0}
\]

The final inequality follows from \(m=ew+d\theta<w\) and \(e\ge1\). We have \(P\le A-1,R\le B-1\) and \(0<Q<u,0<S<v\).

Let \(k=d-s\), \(c_n=\lfloor(s+ne)/d\rfloor\), and \(\tau_n=\rho+n\theta+c_nw\in T\). If \(c_1=0\), then \(\rho+\theta<0\), so \(e\ge k\). Put \(L_0=u+v+t_0\). Then \(\tau_1=2\theta+w-L_0\ge0\). With \(h_0=-\theta>0\), this gives \(2h_0\le w-L_0<w\). Together with \(m<w\),

\[
(e-1)w<dh_0<dw/2,\qquad 2e\le d+1.
\tag{PHASE}
\]

Let \(\lambda_n=\lceil ne/d\rceil\) and \(\varepsilon_n=\lambda_n-c_n\in\{0,1\}\). If \(Y_n\) denotes the \(T\)-coordinate in the \(H\)-normal form of \(c_y-nm\), direct calculation gives

\[
Y_n+\tau_n=Du-\varepsilon_n w.
\tag{COMP}
\]

By ALL-AP, \(c_y-nm\notin H\) for every \(n\ge1\), hence \(Y_n\notin T\).

On the other hand, the \(T\)-coordinate of \(a_x-y+nm\) is \(\tau_n+Au-v\). If this were a \(T\)-gap, the translation criterion from [S3.6](#fr-S3.6) would force \(\tau_n=ju\), with \(0\le j<D\).

* If \(\varepsilon_n=0\), then COMP gives \(Y_n=(D-j)u\in T\), a contradiction.
* Suppose \(\varepsilon_n=1\). Write \(ne=qd+r\), \(0\le r<d\). Then \(1\le r<k\). Since \(e\ge k\), one has \(n\ge2\). Moreover,
  \[
  (n-1)e=(q-1)d+(d+r-e),\quad d+r-e\ge k
  \]
  by PHASE, because \(d+r-e-k\ge d+1-e-k\ge d+1-2e\ge0\). Hence \(c_{n-1}=c_n=q\). The preceding stable point is
  \[
  \tau_{n-1}=\tau_n-\theta=(j+P)u-Qv.
  \]
  But \(j+P\le D-1+A-1=v-2\) and \(0<Q<u\), so this is a \(T\)-gap, contradicting FS.

Therefore \(a_x-y+nm\in H\) for every \(n\ge0\), so \(a_x-y\in K\). GAP-K then gives \(q_x+y\notin\Gamma\), contradicting the actual pseudo-Frobenius consequence \(q_x+y\in\Gamma\).

This eliminates every \(k_0/e\)-case in Branch II. Hence not all RAW4 rows can remain in the Apéry set, and TYPE-BRIDGE yields

\[
\boxed{t(\Gamma)\le4}.
\]
