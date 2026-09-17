# The relative lattice of three arms and the in-box path argument {#app-B}

In this appendix, \(C\) denotes a local \(3\times3\) matrix and is unrelated to the CORE-ROOT coefficient \(C\).

## Input and the socle matrix {#fr-A1.1}

Let \(H=\langle n_1,n_2,n_3\rangle\) be a nonsymmetric three-generated numerical semigroup, and let

\[
\Gamma=\langle m,n_1,n_2,n_3\rangle,\qquad 0<m<\min_i n_i.
\]

We use the standard Herzog package with the following convention. All \(a_i,b_i\) are positive integers, and

\[
\rho_i=a_i+b_i,
\quad
\rho_1n_1=b_2n_2+a_3n_3,
\quad
\rho_2n_2=a_1n_1+b_3n_3,
\quad
\rho_3n_3=b_1n_1+a_2n_2.
\]

These are the true critical relations, and we use the primitive integer-kernel lattice. The standard generator formulas are

\[
n_1=a_2a_3+a_3b_2+b_2b_3,
\quad n_2=a_1a_3+a_1b_3+b_1b_3,
\quad n_3=a_1a_2+a_2b_1+b_1b_2.
\]

Let \(PF(H)=\{f_A,f_B\}\), \(N=n_1+n_2+n_3\), and \(s_\varepsilon=f_\varepsilon+N\). With **rows equal to socle factorizations**, the correct matrices are

\[
U_A=\begin{pmatrix}0&\rho_2&a_3\\a_1&0&\rho_3\\\rho_1&a_2&0\end{pmatrix},
\qquad
U_B=\begin{pmatrix}0&b_2&\rho_3\\\rho_1&0&b_3\\b_1&\rho_2&0\end{pmatrix}.
\tag{U}
\]

Differences of rows are the zero relations above, hence \(U_\varepsilon n=s_\varepsilon\mathbf1\). Substituting the generator formulas gives

\[
\det U_\varepsilon=s_\varepsilon,
\qquad \operatorname{adj}(U_\varepsilon)\mathbf1=n.
\tag{UD}
\]

## The minimal factorization forced by three actual arms {#fr-A1.2}

Assume three arms of the same color \(\varepsilon\):

\[
q_i=f_\varepsilon-\lambda_i n_i\in PF(\Gamma),\qquad
1\le\lambda_i\le\alpha_i-1,
\quad
\alpha_i=\begin{cases}a_i&\varepsilon=A,\\b_i&\varepsilon=B\end{cases}
\tag{ARM}
\]

Then \(f=f_\varepsilon\in\Gamma\setminus H\). Every genuine factorization

\[
f=k m+\sum_i x_i n_i
\]

must satisfy \(k\ge1\) and \(0\le x_i\le\lambda_i-1\). Indeed, if \(x_i\ge\lambda_i\), removing \(\lambda_i n_i\) from that same factorization would give \(q_i\in\Gamma\).

Choose a factorization with the positive \(m\)-coefficient minimal:

\[
f=k m+\sum_i(p_i-1)n_i,
\qquad1\le p_i\le\lambda_i\le\alpha_i-1.
\tag{MIN}
\]

Thus \(s-p\cdot n=km\). No uniqueness of factorization is assumed at this stage.

## Empty tetrahedron and the cyclic quotient {#fr-A1.3}

Let \(L_d=\{z\in\mathbb Z^3:z\cdot n\equiv0\pmod d\}\). Since \(n\) is primitive, \([\mathbb Z^3:L_d]=d\). Define

\[
C=U-\mathbf1p^T,
\qquad c_i=U_i-p
\]

Then \(Cn=km\mathbf1\), and by (UD) and the determinant lemma, \(\det C=km\). Hence

\[
\operatorname{row}_{\mathbb Z}C=L_{km},
\qquad L_m/L_{km}\cong\mathbb Z/k\mathbb Z,
\quad [z]\mapsto z\cdot n/m\pmod k.
\tag{LAT}
\]

The simplex \(\Delta=\operatorname{conv}(p,U_1,U_2,U_3)\) is empty with respect to the affine lattice \(p+L_m\). Indeed, if

\[
u=(1-\tau)p+\sum_i\tau_iU_i,
\quad \tau_i\ge0,\quad\tau=\sum_i\tau_i\le1
\]

is a lattice point, then \(\ell=(s-u\cdot n)/m=(1-\tau)k\) is an integer.

* If \(0<\ell<k\), then \(u>0\) coefficientwise, so \(f=\ell m+\sum_i(u_i-1)n_i\) is a genuine factorization, contradicting minimality of \(k\).
* If \(\ell=k\), then \(u=p\).
* If \(\ell=0\), then \(u\) lies on the top face. At a nonvertex point at least two of the \(U_i\) occur, and since each row of (U) has its unique zero in a different coordinate, \(u>0\). Then \(f=\sum_i(u_i-1)n_i\in H\), a contradiction.

Thus the only lattice points are the four vertices. The relative lattice volume is \(\det C/[\mathbb Z^3:L_m]=k\).

## White classes: the only additional standard external theorem {#fr-A1.4}

The only result of White used here is the standard theorem that an empty lattice tetrahedron has lattice width one: G. K. White, *Lattice Tetrahedra*, Canad. J. Math. 16 (1964), 389–396. An exposition of the proof is given by Khan–Rogers, *An Exposition of White's Characterization of Empty Lattice Tetrahedra*. The quotient, height, and companion constructions below are proved within the present argument.

Assume \(k\ge2\). In the half-open parallelepiped, choose a representative of class \(j\in\{1,\ldots,k-1\}\):

\[
r_j=\sum_i\theta_{j,i}c_i,\qquad0\le\theta_{j,i}<1
\]

Emptiness gives \(\sum_i\theta_{j,i}>1\). For the negative class, the nonzero coordinates have coefficients \(1-\theta_{j,i}\). Since both sums are \(>1\), all three coordinates are nonzero, and

\[
0<\theta_{j,i}<1,
\qquad1<\sum_i\theta_{j,i}<2.
\]

Moreover, \(k\sum_i\theta_{j,i}=r_j\cdot n/m\equiv j\pmod k\), so

\[
\sum_i\theta_{j,i}=1+j/k.
\tag{AGE}
\]

White's width-one planes separate the vertices into two pairs. A \(1+3\) split would have an empty triangular facet that is unimodular in its own lattice and height one, forcing simplex volume one, contrary to \(k\ge2\). After a row permutation, the planes may therefore be taken to separate \((p,U_1)\) from \((U_2,U_3)\). Normalize the corresponding primitive affine functional to be linear with \(p=0\); then \(c_1\mapsto0,c_2,c_3\mapsto1\). Since \(r_1\) is a lattice point, \(\theta_{1,2}+\theta_{1,3}\) is an integer in \((0,2)\), equivalently \(0<\cdot<2\) for this quantity, and hence equals one. By AGE, \(\theta_{1,1}=1/k\).

Thus, for some \(1\le r<k\),

\[
\theta_1=(1/k,r/k,(k-r)/k).
\]

Nonvanishing of all coordinates in every class gives \(\gcd(r,k)=1\). Let \(q<k\) be the positive integer and let \(\ell\) be the nonnegative integer determined by \(rq=1+\ell k\). If the rows in the natural ordering are denoted by \(R_i\), then

\[
z=\frac{R_1+r(R_2-R_3)-p}{k}\in\mathbb Z^3,
\qquad z_q=qz-\ell(R_2-R_3)\in\mathbb Z^3.
\tag{Z}
\]

Here \(r_1=c_3+z,r_q=c_3+z_q\). For \(v=z\) or \(z_q\), the lower companions of class \(j\) and \(k-j\) are

\[
\begin{array}{lll}
p+R_3-R_1+v,&p+R_3-R_2+v,&p+v,\\
R_2-v,&R_1-v,&R_1+R_2-R_3-v.
\end{array}
\tag{COMP}
\]

They satisfy \(s-u\cdot n=(k-j)m\) or \(jm\), respectively. Minimality therefore implies that **none of the six vectors is coefficientwise strictly positive**. The argument is unchanged if classes coincide when \(q=1\) or \(k=2\).

## Exact failure inequalities for color A {#fr-A1.5}

For \(U_A\) in the natural ordering,

\[
z=(-X,Y,Z),
\quad X=\frac{rb_1+p_1}{k},
\quad Y=\frac{b_2-(r-1)a_2-p_2}{k},
\quad Z=\frac{(r+1)a_3+rb_3-p_3}{k}.
\]

The arm bounds give \(X>0,X<p_1+\rho_1,X<p_1+b_1\), \(-a_2<Y<b_2\), and \(0<Z<\rho_3\). Apply failure of the six vectors in COMP in the following order.

1. Failure of \(R_2-z=(a_1+X,-Y,\rho_3-Z)\) gives \(Y\ge0\).
2. Failure of \(R_1-z=(X,\rho_2-Y,a_3-Z)\) gives \(Z\ge a_3\).
3. From \(p+R_3-R_2+z=(p_1+b_1-X,p_2+a_2+Y,p_3-\rho_3+Z)\), obtain \(Z\le\rho_3-p_3\).
4. From \(p+R_3-R_1+z=(p_1+\rho_1-X,p_2-b_2+Y,p_3-a_3+Z)\), obtain \(Y\le b_2-p_2\).
5. Failure of \(p+z\) gives \(X\ge p_1\).
6. Failure of \(R_1+R_2-R_3-z=(X-b_1,b_2-Y,2a_3+b_3-Z)\) gives \(X\le b_1\).

Therefore

\[
p_1\le X\le b_1,\quad0\le Y\le b_2-p_2,
\quad a_3\le Z\le\rho_3-p_3.
\tag{BA}
\]

For \(z_q=(-X_q,Y_q,Z_q)\), direct calculation gives

\[
X_q=(b_1+qp_1)/k,
\quad Y_q=[q(b_2-p_2)+(q-1)a_2]/k,
\quad Z_q=[(q+1)a_3+b_3-qp_3]/k.
\]

Since \(b_2-p_2\ge(r-1)a_2\), one has \(Y_q\ge0\). Also

\[
kb_2-kY_q=(k-q)b_2+qp_2-(q-1)a_2
\ge k(r-\ell-1)a_2+kp_2>0.
\]

Thus \(Y_q<b_2\). The remaining bounds \(0<X_q<p_1+b_1\) and \(0<Z_q<\rho_3\) are immediate, so the same six-vector argument applies (BA) to \(z_q\) as well.

Using only \(X_q\ge p_1,Y\ge0,Z_q\ge a_3\) and integrality, and writing \(s=k-q\ge1\), we obtain

\[
b_1=sp_1+ku,
\quad b_2=p_2+(r-1)a_2+ky,
\quad b_3=qp_3+(s-1)a_3+kv,
\quad u,y,v\in\mathbb Z_{\ge0}.
\tag{AP}
\]

The final proof does not require a converse classification of the failure cone or its redundant inequalities.

## Color A multiplicity contradiction for all \(k\ge2\) {#fr-A1.6}

Put \(e_i=a_i-p_i\ge1\). The three socle rows give

\[
\begin{aligned}
km&=(e_1+b_1)n_1+e_2n_2-p_3n_3,\\
km&=-p_1n_1+(e_2+b_2)n_2+e_3n_3,\\
km&=e_1n_1-p_2n_2+(e_3+b_3)n_3.
\end{aligned}
\]

Multiply them respectively by \(1,s,rs\) and add. With \(D=1+s+rs\), (AP) gives

\[
w\cdot n=kDm,
\quad
\begin{cases}
w_1=(1+rs)e_1+ku,\\
w_2=(1+rs)e_2+sky,\\
w_3=((k-1)rs-1)p_3+s(1+rs)e_3+rskv.
\end{cases}
\]

We have \((k-1)rs-1\ge0\) and each \(w_i>0\). Since \(rs+1=k(r-\ell)\) and \(r-\ell\ge1\),

\[
\sum_iw_i-kD\ge(s+1)(rs+1-k)
=k(s+1)(r-\ell-1)\ge0.
\]

But \(n_i>m\), so \(w\cdot n>m\sum_iw_i\ge kDm\), a contradiction.

## Color B failure inequalities and multiplicity contradiction {#fr-A1.7}

For the correct natural ordering of \(U_B\),

\[
z=(X,-Y,Z),
\quad X=(ra_1-p_1)/k,
\quad Y=[r\rho_2-b_2+p_2]/k,
\quad Z=[a_3+(r+1)b_3-p_3]/k.
\]

The arm bounds give \(-p_1<X<a_1,0<Y<\rho_2,0<Z<\rho_3\). Apply failure of COMP in order.

1. From \(p+z\), obtain \(Y\ge p_2\).
2. From \(R_2-z=(\rho_1-X,Y,b_3-Z)\), obtain \(Z\ge b_3\).
3. From \(R_1-z=(-X,b_2+Y,\rho_3-Z)\), obtain \(X\ge0\).
4. From \(R_1+R_2-R_3-z=(a_1-X,Y-a_2,a_3+2b_3-Z)\), obtain \(Y\le a_2\).
5. From \(p+R_3-R_1+z=(p_1+b_1+X,p_2+a_2-Y,p_3-\rho_3+Z)\), obtain \(Z\le\rho_3-p_3\).
6. From \(p+R_3-R_2+z=(p_1-a_1+X,p_2+\rho_2-Y,p_3-b_3+Z)\), obtain \(X\le a_1-p_1\).

Hence

\[
0\le X\le a_1-p_1,\quad p_2\le Y\le a_2,
\quad b_3\le Z\le\rho_3-p_3.
\tag{BB}
\]

For \(z_q=(X_q,-Y_q,Z_q)\), direct calculation gives

\[
X_q=(a_1-qp_1)/k,
\quad Y_q=[a_2-(q-1)b_2+qp_2]/k,
\quad Z_q=[qa_3+(q+1)b_3-qp_3]/k.
\]

The arm bounds directly give \(-p_1<X_q<a_1\), \(0<Z_q<\rho_3\), and \(Y_q<\rho_2\). Failure of \(p+z_q\) first gives \(Y_q\ge p_2>0\). Continuing the same six-vector argument in the same order applies (BB) to \(z_q\) as well.

From \(X_q\ge0,Y_q\ge p_2,Z\ge b_3\) and integrality, with \(t=k-r\ge1\),

\[
a_1=qp_1+ku,
\quad a_2=(q-1)b_2+(k-q)p_2+ky,
\quad a_3=p_3+(t-1)b_3+kv,
\quad u,y,v\ge0.
\tag{BP}
\]

Let \(f_i=b_i-p_i\ge1\). The three socle rows are

\[
\begin{aligned}
km&=-p_1n_1+f_2n_2+(a_3+f_3)n_3,\\
km&=(a_1+f_1)n_1-p_2n_2+f_3n_3,\\
km&=f_1n_1+(a_2+f_2)n_2-p_3n_3.
\end{aligned}
\]

Multiply them respectively by **\(q,1,qt\)** and set \(D=1+q+qt\). Then

\[
w\cdot n=kDm,
\quad
\begin{cases}
w_1=(1+qt)f_1+ku,\\
w_2=(qt(k-1)-1)p_2+q(1+qt)f_2+qtk y,\\
w_3=(1+qt)f_3+qkv.
\end{cases}
\]

All \(w_i>0\). Since \(qt+1=k(q-\ell)\) and \(q-\ell\ge1\),

\[
\sum_iw_i-kD\ge(q+1)(qt+1-k)
=k(q+1)(q-\ell-1)\ge0.
\]

Again this contradicts \(n_i>m\).

## White row ordering and conclusion {#fr-A1.8}

The row ordering selected by White may be arbitrary. Apply a simultaneous generator permutation that returns the unique zero coordinate of each row to the corresponding index. An even permutation preserves both \(A/B\) and \(a/b\); an odd permutation exchanges \(a/b\) and \(A/B\) simultaneously. The arm box \(p_i\le a_i-1\) is correspondingly carried to \(p_i'\le b_i'-1\). This can be checked directly by simultaneously permuting rows and columns in (U). Thus the two natural master orderings exhaust all possibilities.

It follows that \(k\ge2\) is impossible, and therefore

\[
\boxed{k=1,\qquad f_\varepsilon=m+\sum_i(p_i-1)n_i,
\quad1\le p_i\le\lambda_i\le\alpha_i-1.}
\tag{MINBOX}
\]

This stage uses only lattice algebra and the **minimal positive \(m\)-coefficient**. No signed intermediate is called actual. A lower companion used for contradiction is converted into a genuine factorization only when all three coordinates are positive.

## Exact interface to the \(k=1\) dynamics {#fr-A1.9}

After color reversal if necessary, take color A. Put \(x=p\ge1,y=a-p\ge1,z=y+b\ge2\). Then

\[
C=U_A-\mathbf1p^T
=\begin{pmatrix}-x_1&z_2&y_3\\y_1&-x_2&z_3\\z_1&y_2&-x_3\end{pmatrix},
\quad Cn=m\mathbf1,\quad\det C=m.
\tag{BOX}
\]

The three-arm coordinate caps further imply that, for every \(u\in\mathbb Z_{>0}^3\) satisfying

\[
s-u\cdot n\in m\mathbb Z_{\ge0}
\]

we have \(u_i\le\lambda_i\le a_i-1=x_i+y_i-1\). This is the LOWER-BOX condition in [A2.0](#fr-A2.0).

For example, eliminating rows 1 and 3 of (BOX) gives, for \(\Delta_2=x_1x_3-z_1y_3\),

\[
\Delta_2 n_3=(x_1y_2+z_1z_2)n_2-(x_1+z_1)m>0
\]

Indeed, \(y_2\ge1,z_2\ge2,n_2>m\), so the right-hand side is positive. The other relevant cyclic minors are positive in the same way. Hence the positive minors needed downstream do not rely on an independent older master lemma.

The matrix \(C\), the box \(\mathcal B\), and the local integers introduced here are used only in this appendix.

## Exact input inherited from MINBOX {#fr-A2.0}

Let \(x_i,y_i,b_i\) be positive integers, with \(z_i=y_i+b_i\) and \(a_i=x_i+y_i\). Assume

\[
C=\begin{pmatrix}-x_1&z_2&y_3\\y_1&-x_2&z_3\\z_1&y_2&-x_3\end{pmatrix},
\quad Cn=m\mathbf1,
\quad 0<m<\min(n_1,n_2,n_3).
\tag{INPUT}
\]

Let \(\mathcal B=\prod_i[1,a_i-1]\cap\mathbb Z^3\), with initial point \(p=x\).

Firing row \(i\) means \(u\mapsto u-c_i\). A firing is *positive* if all coordinates remain positive, and *in-box* if the result also lies in \(\mathcal B\). **Theorem DPE:** a maximal in-box path from \(p\) cannot terminate at a positivity sink; it has a positive out-of-box firing.

Neither \(\det C=m\) nor \(\operatorname{adj}C\mathbf1=n\) is an additional requirement for this dynamics theorem. INPUT is already sufficient.

## The finite unique in-box path {#fr-A2.1}

The three source regions for in-box firings are

\[
F_1:\ u_1\le y_1-1,\ u_2\ge z_2+1,\ u_3\ge y_3+1,
\]
\[
F_2:\ u_1\ge y_1+1,\ u_2\le y_2-1,\ u_3\ge z_3+1,
\]
\[
F_3:\ u_1\ge z_1+1,\ u_2\ge y_2+1,\ u_3\le y_3-1.
\]

These regions are pairwise disjoint. Every firing decreases \(u\cdot n\) by exactly \(m\), so no path is infinite.

A state with no positive firing lies in the union of the following four regions; this follows by negating the two positivity conditions for each row and expanding:

\[
\mathsf A:\ u_1\le y_1,u_2\le z_2;
\quad\mathsf B:\ u_1\le z_1,u_3\le y_3;
\]
\[
\mathsf C:\ u_2\le y_2,u_3\le z_3;
\quad\mathsf D:\ u_1\le z_1,u_2\le z_2,u_3\le z_3.
\tag{SINK}
\]

The initial point \(p\) is not a sink. If \(p\in\mathsf A\), then \(c_1+c_2\) is coefficientwise nonnegative and its third coefficient is \(y_3+z_3\ge3\), giving \(2m\ge3n_3\), a contradiction. The cases \(\mathsf B,\mathsf C\) are the cyclic analogues. If \(p\in\mathsf D\), the sum of the three rows has coefficients \(y_i+z_i-x_i\ge y_i\ge1\), giving \(3m\ge n_1+n_2+n_3\), again impossible.

If the first firing is out of the box, the theorem is already proved. Otherwise, after cyclic normalization we may assume \(p\in F_1\). Then

\[
x_1<y_1,\quad x_2>z_2,\quad x_3>y_3.
\tag{START}
\]

We henceforth suppose, toward a contradiction, that a maximal path terminates at a sink.

## Positive minors needed for the two-color calculation {#fr-A2.2}

Combining the first two rows of INPUT gives

\[
(x_1x_2-y_1z_2)n_2
=(y_1y_3+x_1z_3)n_3-(x_1+y_1)m>0.
\]

This follows from \(z_3\ge2,y_3\ge1,n_3>m\). Hence \(\Delta_3=x_1x_2-y_1z_2>0\).

Likewise,

\[
(x_1x_3-y_3z_1)n_3
=(z_1z_2+x_1y_2)n_2-(z_1+x_1)m>0,
\]

so \(\Delta_2=x_1x_3-y_3z_1>0\). These inequalities establish the orientations of the two Farey corridors used below.

## Common arithmetic lemma for a two-color prefix {#fr-A2.3}

Consider only row 1 and row \(r\), where \(r=2\) or \(3\). Use the following common notation.

| Symbol | \(r=2\) | \(r=3\) |
|---|---|---|
| x | \(x_1\) | \(x_1\) |
| A | \(y_1\) | \(z_1\) |
| B | \(z_2\) | \(y_3\) |
| v | \(x_2\) | \(x_3\) |
| b=A−y_1 | 0 | \(b_1\) |
| c=B−y_r | \(b_2\) | 0 |

In either case \(A>x\), \(v>B\), and \(A/x<v/B\). Write the row counts as \((N-1,q-1)\), and define

\[
X=qA-Nx,\qquad D=NB-qv.
\]

The used coordinates are \(u_1=A-X,u_r=B-D\). For row 1 to fire in-box one needs \(X\ge b+1\); for row \(r\) to fire in-box one needs \(D\ge c+1\). These conditions are sufficient once the remaining unused-coordinate threshold is satisfied.

### Successful crossings {#fr-A2.3.1}

At the \(q\)-th crossing where an in-box firing of row \(r\) actually follows a run of row 1,

\[
N_q=\lceil qA/x\rceil,
\quad E_q=N_qx-qA,\quad U_q=qv-(N_q-1)B,
\]
\[
1\le E_q\le x-b-1,
\qquad1\le U_q\le B-c-1=y_r-1.
\tag{RES}
\]

Indeed, the in-box continuation by row 1 ends when \(X\le b\). The strip \(0\le X\le b\) is an early-exit strip in which switching to row \(r\) is impossible. At a successful switch, \(X=-E_q<0\), while the preceding row-1 source satisfies \(X+x\ge b+1\), giving \(E_q\le x-b-1\). The positivity and capacity of the row-\(r\) source are exactly the stated range for \(U_q\).

Immediately after firing row \(r\), one has \(u_1=E_q<x<y_1\), so row \(r\) cannot fire again immediately. Hence successful crossings occur as the chronological initial prefix \(q=1,2,\ldots\). Before the third color appears, the next move is a row-1 run.

RES gives

\[
(N_q-1)/q<A/x<v/B<N_q/q
\tag{CROSS}
\]

Therefore, if all crossings through \(q\) are successful, then for every \(1\le h\le q\) there is no integral fraction \(k/h\) in the closed interval \([A/x,v/B]\). This is the **PREFIX separator rule**; it is a consequence, not an additional assumption.

### Injectivity, anti-chain property, and last-rank bound {#fr-A2.3.2}

For \(i<j\), set \(h=j-i,k=N_j-N_i\). Then

\[
E_j-E_i=kx-hA,\qquad U_j-U_i=hv-kB.
\]

If the \(E\)-coordinates are equal, then \(k/h=A/x\); if the \(U\)-coordinates are equal, then \(k/h=v/B\). Either contradicts PREFIX. If both coordinates increase, then \(A/x<k/h<v/B\), again impossible.

Thus each coordinate is injective, and relative to the last point \((E_q,U_q)\), every earlier point satisfies \(E_i>E_q\) or \(U_i>U_q\). Counting integer slots gives

\[
q+E_q+U_q\le (x-b)+(B-c)-1.
\tag{LR}
\]

In particular, \(q\le x-b-1\) and \(q\le y_r-1\).

The same difference calculation applies to a terminal crossing \(q=Q\) before success. If indices \(1,\ldots,Q-1\) are successful and the terminal point has \(N=\lceil QA/x\rceil\), then

\[
Q-1\le(x-b-1-E)_++(y_r-1-U)_+,
\tag{ELR}
\]

provided the relevant terminal residues lie in their stated positive ranges. At every use of ELR below, \(E\ge1,U\ge1\), and \(E\le x-b-1\) are verified explicitly.

## Reciprocal-rank lemma, including preservation of the omitted prefix {#fr-A2.4}

Consider a state reached by \(\ell\ge1\) additional row-1 firings after the last successful crossing \(q\ge1\). Put

\[
Q=q+1,\quad N=N_q+\ell,
\quad d=A-x>0,\quad a=v-B>0,
\quad H=N-Q.
\]

Assume that at this state \(X=QA-Nx\ge b\). Since \(\Delta>0\), one has \(D=NB-Qv<0\). Define

\[
E=-D=Qa-HB,\qquad V=d-X=Hx-(Q-1)d.
\]

From RES and \(\ell\ge1\),

\[
H\ge1,\quad1\le E\le a-1,\quad1\le V\le d-b.
\tag{DR-BOX}
\]

Indeed, \(E=a-\ell B+U_q\le a-c-1\), while \(X=A-E_q-\ell x\le d-1\). Therefore

\[
(Q-1)/H<B/a<x/d\le Q/H.
\tag{DR-BRACKET}
\]

### Complete proof of the dual PREFIX {#fr-A2.4.1}

Suppose that for some \(s<H\) there were a positive integer \(k\) with \(B/a\le k/s\le x/d\). Since \(sx/d<Hx/d\le Q\), one has \(k\le Q-1=q\).

Taking reciprocals and adding one gives

\[
A/x\le(k+s)/k\le v/B,
\]

contradicting the original successful PREFIX at denominator \(k\le q\).

Thus, for \(s=1,\ldots,H-1\), the dual crossing index

\[
K_s=\lceil sB/a\rceil=\lceil sx/d\rceil
\]

is defined, with dual residues

\[
E_s^*=K_sa-sB\in[1,a-1],
\quad V_s^*=sx-(K_s-1)d\in[1,d-1].
\]

For the terminal value \(s=H\), set \(K_H=Q\) and use \(E,V\) from DR-BOX. This convention is also consistent at right-endpoint equality.

### Preservation of the shifted gap {#fr-A2.4.2}

For \(s<H\), the corresponding original count pair is \((N_s,K_s)=(s+K_s,K_s)\). Its original \(X\)-coordinate is

\[
X_s=K_sd-sx=d-V_s^*\in[1,d-1].
\]

Since \(K_s\le Q\), the inequality \(X_s>0\) gives \(N_s<K_sA/x\), while \(X_s<d\) gives \(N_s>(K_s-1)A/x+1\). Therefore \(N_s\) is an integer count on the row-1 run between the original \((K_s-1)\)-st successful firing and the \(K_s\)-th crossing.

If \(K_s<Q\), that run lies in the already successful PREFIX. If \(K_s=Q\), then \(s<H\) gives \(N_s<N\), so the state lies before the terminal point on the current final row-1 run. In either case the path actually passes through this state and continues with row 1.

When \(K_s=1\), the “0-th successful firing” means the first row-1 run from the initial state. The inequalities \(N_s>1\) and \(N_s<N_1\) give the same correspondence directly, without assuming a nonexistent crossing.

Hence \(X_s\ge b+1\), so

\[
V_s^*\le d-b-1\quad(s<H).
\]

Thus the assertion that the dual residues avoid the same early-exit strip is established by explicit correspondence with integer counts actually traversed by the path, not by formal analogy.

### Dual rank {#fr-A2.4.3}

Applying the same difference calculation as in [A2.3.2](#fr-A2.3.2) to the dual PREFIX gives injectivity and the anti-chain property. Hence

\[
H-1\le(a-1-E)+\max(d-b-1-V,0).
\]

If \(V\le d-b-1\), this directly gives the desired bound; if \(V=d-b\), the second term is zero. In either case,

\[
\boxed{H+E+V\le a+d-b.}
\tag{DR}
\]

No infinite descent or new actual row is assumed in this lemma. It counts explicitly specified states in the original finite prefix.

## Rule for weighted certificates {#fr-A2.5}

For every nonzero nonnegative integer row vector \(\lambda\), if \(v=\lambda C\ge0\) and \(|v|_1\ge|\lambda|_1\), then

\[
|λ|_1m=v\cdot n>|v|_1m\ge|λ|_1m,
\]

which is impossible. We use the certificates below according to this rule.

For row counts \(c=(r,s,t)\), the universal identity is

\[
(c+\mathbf1)C=(y_1+z_1-u_1,y_2+z_2-u_2,y_3+z_3-u_3).
\tag{MC}
\]

## A one-color path cannot terminate at a sink {#fr-A2.6}

Suppose only row 1 has fired, \(N-1\ge1\) times. Then \(u_1=Nx_1\), and the box condition gives \((N-1)x_1\le y_1-1\).

\[
N\le y_1-x_1+1,
\quad N(x_1+1)\le2y_1,
\quad y_1+z_1-Nx_1\ge N+b_1.
\]

The first inequality follows from \((x_1-1)(y_1-x_1-1)\ge0\).

For sink \(\mathsf A\), take \(\lambda=(N,1,0)\). Then \(\lambda C=(y_1-u_1,z_2-u_2,Ny_3+z_3)\ge0\), and the third coefficient is at least \(N+2>|\lambda|\).

For sink \(\mathsf B\), take \(\lambda=(N,0,1)\). Then \(\lambda C=(z_1-u_1,Nz_2+y_2,y_3-u_3)\ge0\), and the second coefficient is at least \(2N+1\ge|\lambda|\).

For sinks \(\mathsf C,\mathsf D\), use MC with \(\lambda=(N,1,1)\). The first coefficient is at least \(N+b_1\), and the remaining two are at least \((z_2,y_3)\) or \((y_2,y_3)\), respectively. Thus \(\lambda C\ge\lambda\) componentwise. Every case contradicts the weighted-certificate rule.

## Excluding all terminal states of a \(\{1,2\}\) two-color path {#fr-A2.7}

Let \(N=r+1,Q=s+1\), and set \(X=Qy_1-Nx_1\), \(Y=Nz_2-Qx_2-b_2\), \(u_1=y_1-X,u_2=y_2-Y\).

There have been \(q=Q-1\) successful crossings, so \(Q\le x_1,Q\le y_2\). From the box condition and \(q\le x_1-1\), we also have \(N\le y_1\). For if \(N\ge y_1+1\), then \(u_1=Nx_1-qy_1\ge x_1+y_1\), contrary to the box condition.

Sink \(\mathsf A\) would require \(X\ge0,Y\ge-b_2\), but

\[
x_2X+y_1Y=-NΔ_3-y_1b_2<-y_1b_2
\]

which is impossible.

For sink \(\mathsf D\), take \(\lambda=(N,Q,1)\). By MC, \(\lambda C=(z_1+X,z_2+Y,y_3+z_3-u_3)\). The \(\mathsf D\)-conditions together with \(N\le y_1,Q\le y_2\) give \(\lambda C\ge\lambda\) componentwise.

### The last firing is row 2 {#fr-A2.7.1}

Immediately before the last firing we are at the last successful crossing \(q=Q-1\), with \(N=N_q,E=E_q,U=U_q,D_q=z_2-U\).

After firing, \(u_1=E<x_1<y_1\) and \(u_2=x_2+U>z_2\). At a sink, one must have \(u_3\le y_3\), since otherwise row 1 would be positive. Thus the sink is \(\mathsf B\).

For \(\lambda=(N,q,1)\), all coefficients of \(\lambda C\) are nonnegative, and the margin is

\[
|λC|-|λ|
=b_1+(y_1-N+D_q-E)+(y_2-q-1)+(y_3-u_3).
\]

By LR, \(D_q-E\ge q-x_1+b_2+1\). Since \(q<x_1\),
\(N-q=\lceil q(y_1-x_1)/x_1\rceil\le y_1-x_1\). Hence the second bracket is at least \(b_2+1\), and all other terms are nonnegative.

### The last firing is row 1, sink \(\mathsf B\), \(X\ge0\): the pre-crossing terminal case {#fr-A2.7.2}

Sink \(\mathsf B\) means \(X\ge-b_1,u_3\le y_3\). The subcase \(X\ge0\) includes states before the crossing.

Apply the reciprocal-rank lemma [A2.4](#fr-A2.4) with \(A=y_1,B=z_2,v=x_2,b=0,c=b_2\). Since \(\ell\ge1\) row-1 firings follow the last successful crossing \(q\ge1\), all hypotheses hold.

With \(H=N-Q\), \(a=x_2-z_2\), \(d=y_1-x_1\), \(E=-(Y+b_2)\), and \(V=d-X\), we have \(H+E+V\le a+d\).

For \(\lambda=(N,Q-1,1)\),

\[
λC=(b_1+X,x_2+z_2+Y,y_3-u_3)\ge0.
\]

The second coefficient is nonnegative because the box condition \(u_2\le x_2+y_2-1\) gives \(x_2+z_2+Y\ge z_2+1\). The margin is

\[
|λC|-|λ|
=b_1+d+x_2+y_2-(H+E+V)-2Q+(y_3-u_3)
\]
\[
\ge b_1+z_2+y_2-2Q+(y_3-u_3)\ge b_1+b_2>0.
\tag{PRE-CROSS-PATCH}
\]

Thus both the pre-crossing cases \(X>0\) and \(X=0\) are excluded.

### The last firing is row 1, sink \(\mathsf B\), \(X<0\) {#fr-A2.7.3}

Here \(N=N_Q\) and \(E=-X\in[1,x_1-1]\). Put \(D=Y+b_2=Nz_2-Qx_2\). For the same \(\lambda=(N,Q-1,1)\), the margin is

\[
(b_1-E)+(x_2-N+D)+(y_2-Q)+(y_3-u_3).
\]

The first, third, and fourth terms are nonnegative. If \(D\ge0\), then \(N\le x_2\), because \(Q\le y_2<z_2\) and \(N=\lceil Qy_1/x_1\rceil<Qx_2/z_2+1\), so the second term is also nonnegative.

If \(D<0\), put \(W=-D>0\). If some prior \(U_j\le W\), then with \(h=Q-j,k=N-N_j+1\),

\[
kx_1-hy_1=E-E_j+x_1>0,
\quad hx_2-kz_2=W-U_j\ge0,
\]

which is a PREFIX separator. Hence all prior \(U_j>W\), and injectivity gives \(Q+W\le y_2\).

Also \(N-Q\le x_2-z_2\) because \(Q<z_2\) and \(y_1/x_1<x_2/z_2\). Therefore

\[
x_2-N\ge z_2-Q\ge y_2-Q\ge W.
\]

The second term is nonnegative as well. This is the required predecessor estimate.

### The last firing is row 1, sink \(\mathsf C\) {#fr-A2.7.4}

Since \(Y\ge0\), one has \(X<0\) and \(N=N_Q\). Put \(E=-X\) and \(U=u_2=z_2-(Y+b_2)>0\). Apply ELR to all prior points.

If \(U>y_2-1\), then \(Q+E\le x_1\); otherwise \(Q+E+U\le x_1+y_2-1\). In either case,
\(Q\le x_1-E+Y=x_1+X+Y\).

For \(\lambda=(N-1,Q,1)\),

\[
λC=(x_1+z_1+X,Y,z_3-u_3)\ge0.
\]

The sum of the first two coefficients is at least \(z_1+Q\ge N+Q+b_1\). Hence \(|\lambda C|\ge|\lambda|\). This exhausts the sink regions for the \(\{1,2\}\)-path.

## Excluding all terminal states of a \(\{1,3\}\) two-color path {#fr-A2.8}

Let \(N=r+1,R=t+1\), and set \(X=Rz_1-Nx_1\), \(Y=Ny_3-Rx_3\), \(u_1=z_1-X,u_3=y_3-Y\).

With \(q=R-1\) successful crossings, one has \(q\le x_1-b_1-1\), \(q\le y_3-1\), and \(R\le y_3\).

The box condition also gives \(N\le y_1\). If \(N\ge y_1+1\), then

\[
u_1-(x_1+y_1-1)
\ge b_1(b_1+y_1-x_1+1)+1>0.
\]

Sink \(\mathsf B\) would require \(X\ge0,Y\ge0\), contradicting \(x_3X+z_1Y=-N\Delta_2<0\).

For sink \(\mathsf D\), take \(\lambda=(N,1,R)\). By MC and \(N\le y_1,R\le y_3\), one has \(\lambda C\ge\lambda\) componentwise.

### The last firing is row 3 {#fr-A2.8.1}

Immediately after the last successful crossing \(q\), \(u_1=E_q<x_1<y_1\) and \(u_3=x_3+U_q>y_3\). If this is a sink, then \(u_2\le z_2\), so it lies in \(\mathsf A\).

For \(\lambda=(N,1,q)\),

\[
λC=(y_1-E_q,z_2-u_2,y_3+z_3-U_q)\ge0.
\]

Using LR, \(q+E_q+U_q\le x_1-b_1+y_3-1\), together with \(N-q\le z_1-x_1\) and \(q\le y_3-1\), the margin is at least \(b_3+1>0\).

### The last firing is row 1, sink \(\mathsf A\) {#fr-A2.8.2}

Here \(X\ge b_1,u_2\le z_2\). Apply the reciprocal-rank lemma [A2.4](#fr-A2.4) with \(A=z_1,B=y_3,v=x_3,b=b_1,c=0\).

Set \(H=N-R\), \(d=z_1-x_1\), \(a=x_3-y_3\), \(E=-Y\), \(V=d-X\), and \(D_*=a+d-b_1-(H+E+V)\ge0\).

For \(\lambda=(N,1,R-1)\),

\[
λC=(X-b_1,z_2-u_2,x_3+z_3+Y).
\]

The first two coordinates are nonnegative by the \(\mathsf A\)-conditions. For the third, using the residue \(U_q\) at the last success \(q=R-1\) and \(N=N_q+\ell\), \(\ell\ge1\),
\(x_3+z_3+Y=z_3+(\ell+1)y_3-U_q>0\). Thus all coefficients are nonnegative, and the exact margin is

\[
|λC|-|λ|=D_*+(z_2-u_2)+b_3+2(y_3-R)\ge b_3>0.
\]

### The last firing is row 1, sink \(\mathsf C\) {#fr-A2.8.3}

Here \(u_2\le y_2,Y\ge-b_3\). Since the preceding state lies in \(F_1\), one has \(X+x_1\ge b_1+1\). Put

\[
P=x_1+X-b_1-1\ge0,\quad B_*=b_3+Y\ge0,
\quad A_*=x_1-b_1-1,\quad C_*=y_3-1.
\]

Every successful index \(b_1<i\le q\) satisfies \(E_i>A_*-P\) or \(U_i>C_*-B_*\).

If both failed, then with \(h=R-i,k=N-N_i\),

\[
h z_1-kx_1=E_i+X\le0,
\]
\[
(k+1)y_3-hx_3=U_i+Y\le y_3-b_3-1,
\]

so \(z_1/x_1\le k/h<x_3/y_3\), contradicting PREFIX for \(1\le h\le q\).

Slot counting using injectivity gives \(q-b_1\le P+B_*\) (trivial when \(q\le b_1\)). Thus \(D_*=P+B_*-(q-b_1)\ge0\).

For \(\lambda=(N-1,1,R)\), the coefficients are \((x_1+y_1+X,y_2-u_2,b_3+Y)\). The first is positive by the row-1 predecessor condition \(X+x_1\ge b_1+1\), and the last two are nonnegative by the \(\mathsf C\)-conditions. Therefore

\[
|λC|-|λ|=(y_1-N)+(y_2-u_2)+D_*\ge0.
\]

This excludes every two-color sink.

## Excluding the first occurrence of the third color {#fr-A2.9}

The first firing is row 1. The first firing of a third color is therefore either \(\{1,2\}\to3\) or \(\{1,3\}\to2\).

If row 3 first appeared immediately after row 2, the first coordinate of the preceding state would be at least \(y_1+z_1+1=2y_1+b_1+1\), whereas the box upper bound is \(x_1+y_1-1\), contradicting START \(x_1<y_1\). The same argument excludes row 2 immediately after row 3. Hence in either case the third color first appears immediately after row 1.

### \(\{1,2\}\to3\) {#fr-A2.9.1}

The source counts for the third color are \((N-1,Q-1,0)\). Substituting the preceding \(F_1\)-condition and the current \(F_3\)-condition gives

\[
1-x_1\le X\le-b_1-1,
\quad z_2+1-x_2\le Y\le-1,
\quad1\le u_3\le y_3-1.
\]

Thus \(N=N_Q\) and \(E=-X\in[1,x_1-1]\). All prior indices \(1,\ldots,Q-1\) are successful.

Every prior \(E_j>E\). Otherwise, with \(h=Q-j,k=N-N_j\), one would have \(kx_1-hy_1=E-E_j\ge0\). Meanwhile \(D=Nz_2-Qx_2=Y+b_2\le b_2-1\) and \(D_j=z_2-U_j\ge b_2+1\), so \(kz_2-hx_2=D-D_j<0\), producing a PREFIX separator.

Hence \(Q+E\le x_1\). Together with \(N-Q\le y_1-x_1\), this gives \(N+E\le y_1\).

Also \(y_2+D\ge Q\). If \(D\ge0\), this follows from \(Q\le y_2\). If \(D<0\), the same difference calculation as in [A2.7.3](#fr-A2.7.3) shows that all prior \(U_j>-D\), hence \(Q-D\le y_2\).

For \(\lambda=(N,Q,1)\),

\[
λC=(z_1-E,y_2+D,y_3+z_3-u_3)\ge(N+b_1,Q,z_3+1)\geλ.
\]

This is a contradiction.

### \(\{1,3\}\to2\) {#fr-A2.9.2}

The source counts are \((N-1,0,R-1)\). The preceding \(F_1\)-condition and the current \(F_2\)-condition give

\[
b_1+1-x_1\le X\le b_1-1,
\quad1\le u_2\le y_2-1,
\quad y_3+1-x_3\le Y\le-b_3-1.
\]

Set \(P=b_1-X\ge1\) and \(W_*=-b_3-Y\ge1\). All prior indices \(1,\ldots,R-1\) are successful.

Every prior \(E_j>P\). Otherwise, with \(h=R-j,k=N-N_j\), one has \(D_1=hz_1-kx_1=E_j+X\le b_1\).

If \(D_1\le0\), then \(k/h\ge z_1/x_1\). On the other hand,
\((k+1)y_3-hx_3=U_j+Y\le y_3-b_3-2<y_3\), so \(k/h<x_3/y_3\), contradicting PREFIX.

If \(1\le D_1\le b_1\), the existence of a successful prefix gives \(b_1\le x_1-2\), while \(k=\lfloor hz_1/x_1\rfloor\) and \(N_h=k+1\). Therefore \(E_h=x_1-D_1\ge x_1-b_1\), directly contradicting the successful EBOX bound \(E_h\le x_1-b_1-1\) at index \(h<R\). This is the integral form of the early-exit strip.

Next, every prior \(U_j>W_*\). Otherwise, the already-proved inequality \(E_j>P\) gives \(b_1+1\le D_1\le x_1-2\). With \(k'=k+1\),

\[
k'x_1-hz_1>0,\quad hx_3-k'y_3=W_*-U_j+b_3>0,
\]

again producing a PREFIX separator.

By injectivity, \(R+P\le x_1-b_1\) and \(R+W_*\le y_3\). Since the preceding state is a row-1 source, \(N\le\lceil Rz_1/x_1\rceil\). From \(R<x_1\) and \(z_1=x_1+d\), we get \(N-R\le d\), hence \(N+P\le y_1\).

For \(\lambda=(N,1,R)\),

\[
λC=(z_1-P,y_2+z_2-u_2,y_3-W_*)\ge(N+b_1,z_2+1,R)\geλ,
\]

again a contradiction.

## Exhaustion and connection to the upstream argument {#fr-A2.10}

Suppose that a finite maximal in-box path terminates at a sink.

- If only row 1 occurs, [A2.6](#fr-A2.6) gives a contradiction.
- If exactly two colors occur, [A2.7](#fr-A2.7)–[A2.8](#fr-A2.8) give a contradiction.
- If all three colors occur, the first firing of the third color contradicts [A2.9](#fr-A2.9).

Therefore the endpoint of every maximal path admits a positive out-of-box firing.

This proves DPE, which applies directly to the matrix INPUT obtained from MINBOX with \(k=1\).

### Final connection to the same actual \(f_\varepsilon\) {#fr-A2.10.1}

By [A1.2](#fr-A1.2), for the same semigroup and the same socle element under the assumption of three actual arms,

\[
f_\varepsilon=m+\sum_i(p_i-1)n_i,\qquad
q_i=f_\varepsilon-\lambda_i n_i\in PF(\Gamma),
\quad1\le p_i\le\lambda_i\le\alpha_i-1
\]

First consider color A, so \(\alpha_i=a_i\) and \(p=x\).

After a total of \(t\) firings, write the state as \(u=p-rC\), with \(|r|_1=t\). Since \(Cn=m\mathbf1\),

\[
\boxed{f_A=(t+1)m+\sum_i(u_i-1)n_i.}
\tag{SAME-F}
\]

At a positive state, every \(u_i\ge1\), so this is a genuine factorization of the same \(f_A\). The original \(\Gamma,m,n_i,f_A\) have not changed.

The first positive out-of-box state \(u^*\) supplied by DPE satisfies the same identity. Since it leaves \(\mathcal B=\prod_i[1,a_i-1]\) while all coordinates remain positive, some \(i\) satisfies \(u_i^*\ge a_i\). Hence

\[
u_i^*-1\ge a_i-1\ge\lambda_i.
\]

Removing \(\lambda_i n_i\) from this one final coefficient vector gives

\[
q_i=(t+1)m+(u_i^*-1-\lambda_i)n_i
+\sum_{j\ne i}(u_j^*-1)n_j\in\Gamma,
\]

contradicting the fact that \(q_i\) is an actual pseudo-Frobenius gap. No semantic subtraction of a signed relation is used.

Color B is carried to color A by an odd generator permutation together with the complete simultaneous exchange of \(a/b\) and A/B. The three actual pseudo-Frobenius elements and their arm bounds are exchanged at the same time, so the same conclusion holds.

Thus three actual arms of the same color cannot occur:

\[
\boxed{\text{THREE-ARM CLOSED}.}
\]

For either color, every actual row is either the corner \(f_\varepsilon\) or an arm \(f_\varepsilon-\lambda n_i\). Two distinct depths in the same direction contradict pseudo-Frobenius comparability. A corner cannot coexist with an arm of the same color for the same reason. Therefore, three rows of one color would have to consist of one arm in each of the three directions, and this has just been excluded. Hence, within the canonical six-arm classification,

\[
\boxed{\text{COLOR-CAP}\le2.}
\]

The chain MINBOX → DPE → SAME-F → THREE-ARM → COLOR-CAP requires no additional upstream lemma.

## Proposition B.1 (THREE-ARM / COLOR-CAP) {#prop-B1}

In the setting of the canonical six-arm classification, three actual arms of the same color do not exist. Moreover, for each color there are at most two actual corner/arm rows.

**Proof.** The first assertion is exactly THREE-ARM CLOSED, proved in [A1.1](#fr-A1.1)–[A2.10.1](#fr-A2.10.1). The second is the already-proved COLOR-CAP conclusion obtained at the end of [A2.10.1](#fr-A2.10.1) from incomparability and uniqueness of depth in a fixed direction. No new hypothesis or conclusion is introduced here.
