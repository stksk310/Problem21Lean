# 付録 A2 — boxed dynamicsとCOLOR-CAP

行列Cとbox 𝓑、局所整数は本付録内でのみ使用する。

### A2.0 MINBOX 側から受け取る正確な入力

x_i,y_i,b_i は正整数、z_i=y_i+b_i、a_i=x_i+y_i とする。

\[
C=\begin{pmatrix}-x_1&z_2&y_3\\y_1&-x_2&z_3\\z_1&y_2&-x_3\end{pmatrix},
\quad Cn=m\mathbf1,
\quad 0<m<\min(n_1,n_2,n_3).
\tag{INPUT}
\]

箱 \(\mathcal B=\prod_i[1,a_i-1]\cap\mathbb Z^3\)、初期点 p=x。

row i firing は u↦u−c_i。全座標正なら positive、さらに箱内なら in-box と呼ぶ。**定理 DPE:** p からの最大 in-box path は positivity sink で終われず、positive out-of-box firing を持つ。

detC=m や adjC1=n はこの dynamics 定理には追加で必要ない。INPUT がすでに十分。

### A2.1 有限の一意な in-box path

in-box firing の三つの source regions は

\[
F_1:\ u_1\le y_1-1,\ u_2\ge z_2+1,\ u_3\ge y_3+1,
\]
\[
F_2:\ u_1\ge y_1+1,\ u_2\le y_2-1,\ u_3\ge z_3+1,
\]
\[
F_3:\ u_1\ge z_1+1,\ u_2\ge y_2+1,\ u_3\le y_3-1.
\]

これらは互いに素。各 firing で u⋅n はちょうど m 減るので無限 path はない。

positive firing を一つも持たない state は、次の四領域の和集合である（各 row の二つの positivity 条件を否定して展開すればよい）。

\[
\mathsf A:\ u_1\le y_1,u_2\le z_2;
\quad\mathsf B:\ u_1\le z_1,u_3\le y_3;
\]
\[
\mathsf C:\ u_2\le y_2,u_3\le z_3;
\quad\mathsf D:\ u_1\le z_1,u_2\le z_2,u_3\le z_3.
\tag{SINK}
\]

p は sink でない。p∈A なら c_1+c_2 は係数非負で第三係数 y_3+z_3≥3。従って 2m≥3n_3、矛盾。B,C も cyclic に同様。p∈D なら三行和は各係数 y_i+z_i−x_i≥y_i≥1 なので 3m≥n_1+n_2+n_3、矛盾。

初手が out-of-box なら完了。そうでなければ cyclic normalization で p∈F_1 としてよい。このとき

\[
x_1<y_1,\quad x_2>z_2,\quad x_3>y_3.
\tag{START}
\]

以後 sink に終わる最大 path が存在すると仮定して矛盾を導く。

### A2.2 二色計算に必要な正の minors

INPUT の一、二行を組み合わせると

\[
(x_1x_2-y_1z_2)n_2
=(y_1y_3+x_1z_3)n_3-(x_1+y_1)m>0.
\]

z_3≥2,y_3≥1,n_3>m による。従って Δ_3=x_1x_2−y_1z_2>0。

同様に

\[
(x_1x_3-y_3z_1)n_3
=(z_1z_2+x_1y_2)n_2-(z_1+x_1)m>0,
\]

従って Δ_2=x_1x_3−y_3z_1>0。以下で用いる二つの Farey corridor の向きはこれで証明される。

### A2.3 二色 prefix の共通 arithmetic lemma

row 1 と row r（r=2 または3）だけを考える。以下の表で共通記号を定める。

| 記号 | r=2 | r=3 |
|---|---|---|
| x | x_1 | x_1 |
| A | y_1 | z_1 |
| B | z_2 | y_3 |
| v | x_2 | x_3 |
| b=A−y_1 | 0 | b_1 |
| c=B−y_r | b_2 | 0 |

いずれも A>x、v>B、A/x<v/B。row counts を (N−1,q−1) と書き

\[
X=qA-Nx,\qquad D=NB-qv.
\]

used coordinates は u_1=A−X,u_r=B−D。row 1 が in-box であるには X≥b+1、row r が in-box であるには D≥c+1 が必要。残る unused-coordinate threshold が満たされればこれらで十分。

### A2.3.1 Successful crossings

row 1 run に続いて row r が実際に in-box firing できる q-th crossing では

\[
N_q=\lceil qA/x\rceil,
\quad E_q=N_qx-qA,\quad U_q=qv-(N_q-1)B,
\]
\[
1\le E_q\le x-b-1,
\qquad1\le U_q\le B-c-1=y_r-1.
\tag{RES}
\]

理由: X が b 以下になった時点で row 1 の in-box continuation は終わる。0≤X≤b は row r に切り替われない early-exit strip。successful switch なら X=−E_q<0 で、直前の row 1 source の X+x≥b+1 から E_q≤x−b−1。row r source の positivity/capacity は U_q の範囲そのもの。

row r を一度 fire した直後の u_1 は E_q<x<y_1 であり、同じ row r を続けて fire できない。従って successful crossings は q=1,2,…の chronological initial prefix。第三色が出る前なら、次は row 1 run である。

RES は

\[
(N_q-1)/q<A/x<v/B<N_q/q
\tag{CROSS}
\]

を与える。よって q まで成功していれば、任意の 1≤h≤q に対し、閉区間 [A/x,v/B] に整数分数 k/h は存在しない。これが以下の **PREFIX separator rule** であり、名称による追加仮定ではない。

### A2.3.2 Injectivity、anti-chain、last-rank

i<j で h=j−i,k=N_j−N_i とすると

\[
E_j-E_i=kx-hA,\qquad U_j-U_i=hv-kB.
\]

E が等しければ k/h=A/x、U が等しければ k/h=v/B。いずれも PREFIX に反する。両方が増えれば A/x<k/h<v/B、これも反する。

従って各 coordinate は injective で、last point (E_q,U_q) に対し各 prior point は E_i>E_q または U_i>U_q。整数 slots を数えると

\[
q+E_q+U_q\le (x-b)+(B-c)-1.
\tag{LR}
\]

特に q≤x−b−1、q≤y_r−1。

同じ difference 計算は、成功前の terminal crossing q=Q の値 E,U にも使える。previous indices 1,…,Q−1 が成功し、terminal が N=ceil(QA/x) なら

\[
Q-1\le(x-b-1-E)_++(y_r-1-U)_+,
\tag{ELR}
\]

ただし terminal E,U が各正区間内にあるかは個別に確認する。以下の ELR 使用箇所では E≥1,U≥1 かつ E≤x−b−1 が成立する。

### A2.4 Reciprocal-rank lemma（省略されていた prefix 保存も明示）

最後の成功 crossing q≥1 の後に row 1 が ℓ≥1 回進んだ state を考える。

\[
Q=q+1,\quad N=N_q+\ell,
\quad d=A-x>0,\quad a=v-B>0,
\quad H=N-Q.
\]

この state で X=QA−Nx≥b を仮定する。Δ>0 より D=NB−Qv<0。置く

\[
E=-D=Qa-HB,\qquad V=d-X=Hx-(Q-1)d.
\]

RES と ℓ≥1 から

\[
H\ge1,\quad1\le E\le a-1,\quad1\le V\le d-b.
\tag{DR-BOX}
\]

実際 E=a−ℓB+U_q≤a−c−1、X=A−E_q−ℓx≤d−1。これらから

\[
(Q-1)/H<B/a<x/d\le Q/H.
\tag{DR-BRACKET}
\]

### A2.4.1 Dual PREFIX の完全証明

s<H に対し B/a≤k/s≤x/d となる正整数 k があれば、s x/d<Hx/d≤Q より k≤Q−1=q。

逆数を取り1を加えると

\[
A/x\le(k+s)/k\le v/B,
\]

元の successful PREFIX の denominator k≤q に反する。

従って s=1,…,H−1 に対し、dual crossing index

\[
K_s=\lceil sB/a\rceil=\lceil sx/d\rceil
\]

が存在し、dual residues

\[
E_s^*=K_sa-sB\in[1,a-1],
\quad V_s^*=sx-(K_s-1)d\in[1,d-1].
\]

terminal s=H は K_H=Q とし DR-BOX の E,V を用いる。右 endpoint equality でもこの指定で整合する。

### A2.4.2 Shifted gap の保存を証明

s<H に対応する original count pair は (N_s,K_s)=(s+K_s,K_s)。その original X-coordinate は

\[
X_s=K_sd-sx=d-V_s^*\in[1,d-1].
\]

K_s≤Q。X_s>0 は N_s<K_sA/x を、X_s<d は N_s>(K_s−1)A/x+1 を与える。従って N_s は、original (K_s−1)-th successful firing と K_s-th crossing の間の row-1 run 上の整数 count である。

K_s<Q ならその run は成功済み PREFIX 内にある。K_s=Q なら s<H により N_s<N なので現在の final row-1 run の、terminal より前の state である。従っていずれも実際に path が通過し、row 1 で続行した state。

K_s=1 の場合、「0-th successful firing」は初期状態からの最初の row-1 run を指す。上の N_s>1 と N_s<N_1 により同じ対応が直接成立し、存在しない crossing を仮定しない。

ゆえに X_s≥b+1 が必要であり

\[
V_s^*\le d-b-1\quad(s<H).
\]

これで「dual residues も同じ早期 exit を回避する」が、抽象的な類似ではなく実際の integer count の対応として示された。

### A2.4.3 Dual rank

dual PREFIX に対して A2.3.2 と同じ difference 計算を行えば injectivity と anti-chain を得る。従って

\[
H-1\le(a-1-E)+\max(d-b-1-V,0).
\]

V≤d−b−1 なら直接、V=d−b なら第二項が0となることから、どちらも

\[
\boxed{H+E+V\le a+d-b.}
\tag{DR}
\]

この補題には無限下降や新しい actual row の仮定はない。元の有限 prefix 上の明示された count を数えたものである。

### A2.5 Weighted certificate の使用規則

任意の非負整数 row vector λ≠0 に対し、v=λC≥0 かつ |v|_1≥|λ|_1 なら

\[
|λ|_1m=v\cdot n>|v|_1m\ge|λ|_1m,
\]

矛盾。以下の certificate はこの規則により使う。

counts c=(r,s,t) に対する universal identity は

\[
(c+\mathbf1)C=(y_1+z_1-u_1,y_2+z_2-u_2,y_3+z_3-u_3).
\tag{MC}
\]

### A2.6 一色 path は sink で終われない

row 1 のみ N−1≥1 回進んだとする。u_1=Nx_1、box より (N−1)x_1≤y_1−1。

\[
N\le y_1-x_1+1,
\quad N(x_1+1)\le2y_1,
\quad y_1+z_1-Nx_1\ge N+b_1.
\]

最初の不等式は (x_1−1)(y_1−x_1−1)≥0 から従う。

sink A には λ=(N,1,0) を使う。λC=(y_1−u_1,z_2−u_2,Ny_3+z_3)≥0、第三係数≥N+2>|λ|。

sink B には λ=(N,0,1)。λC=(z_1−u_1,Nz_2+y_2,y_3−u_3)≥0、第二係数≥2N+1≥|λ|。

sink C,D には MC の λ=(N,1,1)。第一係数≥N+b_1、残りはそれぞれ (z_2,y_3) 以上、または (y_2,y_3) 以上。よって componentwise λC≥λ。全て矛盾。

### A2.7 {1,2} 二色 path の全終端を排除

N=r+1,Q=s+1、X=Qy_1−Nx_1、Y=Nz_2−Qx_2−b_2、u_1=y_1−X,u_2=y_2−Y。

q=Q−1 successes があるため Q≤x_1,Q≤y_2。box と q≤x_1−1 より N≤y_1。例えば N≥y_1+1 なら u_1=Nx_1−qy_1≥x_1+y_1、box に反する。

sink A は X≥0,Y≥−b_2 だが

\[
x_2X+y_1Y=-NΔ_3-y_1b_2<-y_1b_2
\]

と矛盾。

sink D には λ=(N,Q,1)。MC より λC=(z_1+X,z_2+Y,y_3+z_3−u_3)。D 条件と N≤y_1,Q≤y_2 により componentwise λC≥λ。

### A2.7.1 最後が row 2

直前は last successful crossing q=Q−1、N=N_q、E=E_q,U=U_q,D_q=z_2−U。

fire 後は u_1=E<x_1<y_1、u_2=x_2+U>z_2。sink なら u_3≤y_3 でなければ row 1 が positive。従って sink B。

λ=(N,q,1) の全係数は非負で、margin は

\[
|λC|-|λ|
=b_1+(y_1-N+D_q-E)+(y_2-q-1)+(y_3-u_3).
\]

LR より D_q−E≥q−x_1+b_2+1、また q<x_1 なので N−q=ceil(q(y_1−x_1)/x_1)≤y_1−x_1。よって第二括弧≥b_2+1。他も非負。

### A2.7.2 最後が row 1、sink B、X≥0：pre-cross終端

sink B は X≥−b_1,u_3≤y_3。このうち X≥0 は crossing 前も含む。

A2.4 の reciprocal lemma を A=y_1,B=z_2,v=x_2,b=0,c=b_2 に適用する。last successful q≥1 の後に ℓ≥1 回 row 1 が進んだので、全入力が成立する。

H=N−Q、a=x_2−z_2、d=y_1−x_1、E=−(Y+b_2)、V=d−X とすると H+E+V≤a+d。

λ=(N,Q−1,1) に対して

\[
λC=(b_1+X,x_2+z_2+Y,y_3-u_3)\ge0.
\]

第二係数の非負性は box u_2≤x_2+y_2−1 から x_2+z_2+Y≥z_2+1。margin は

\[
|λC|-|λ|
=b_1+d+x_2+y_2-(H+E+V)-2Q+(y_3-u_3)
\]
\[
\ge b_1+z_2+y_2-2Q+(y_3-u_3)\ge b_1+b_2>0.
\tag{PRE-CROSS-PATCH}
\]

よって pre-cross X>0 と X=0 は完全に排除。

### A2.7.3 最後が row 1、sink B、X<0

この場合 N=N_Q、E=−X∈[1,x_1−1]。D=Y+b_2=Nz_2−Qx_2 と置く。同じ λ=(N,Q−1,1) の margin は

\[
(b_1-E)+(x_2-N+D)+(y_2-Q)+(y_3-u_3).
\]

第一・第三・第四項は非負。D≥0 なら N≤x_2（Q≤y_2<z_2 かつ N=ceil(Qy_1/x_1)<Qx_2/z_2+1）から第二も非負。

D<0 では W=−D>0 とする。もし prior U_j≤W なら h=Q−j,k=N−N_j+1 により

\[
kx_1-hy_1=E-E_j+x_1>0,
\quad hx_2-kz_2=W-U_j\ge0,
\]

なので PREFIX separator。従って全 prior U_j>W、injectivity から Q+W≤y_2。

また N−Q≤x_2−z_2（Q<z_2 と y_1/x_1<x_2/z_2）なので

\[
x_2-N\ge z_2-Q\ge y_2-Q\ge W.
\]

これで第二項も非負。これは 必要なpredecessor評価を与える。

### A2.7.4 最後が row 1、sink C

Y≥0 から X<0、N=N_Q。E=−X、U=u_2=z_2−(Y+b_2)>0 とする。prior 全点に ELR を用いる。

U>y_2−1 なら Q+E≤x_1。そうでなければ Q+E+U≤x_1+y_2−1。どちらも Q≤x_1−E+Y=x_1+X+Y。

λ=(N−1,Q,1) は

\[
λC=(x_1+z_1+X,Y,z_3-u_3)\ge0.
\]

最初の二係数和≥z_1+Q≥N+Q+b_1。従って |λC|≥|λ|。全 sink 領域を尽くした。

### A2.8 {1,3} 二色 path の全終端を排除

N=r+1,R=t+1、X=Rz_1−Nx_1、Y=Ny_3−Rx_3、u_1=z_1−X,u_3=y_3−Y。

q=R−1 successful crossings より q≤x_1−b_1−1、q≤y_3−1、R≤y_3。

N≤y_1 も box から従う。もし N≥y_1+1 なら

\[
u_1-(x_1+y_1-1)
\ge b_1(b_1+y_1-x_1+1)+1>0.
\]

sink B は X≥0,Y≥0 だが x_3X+z_1Y=−NΔ_2<0 に反する。

sink D には λ=(N,1,R)。MC と N≤y_1,R≤y_3 より componentwise λC≥λ。

### A2.8.1 最後が row 3

last success q の直後で u_1=E_q<x_1<y_1、u_3=x_3+U_q>y_3。sink なら u_2≤z_2 であり A に入る。

λ=(N,1,q) に対して

\[
λC=(y_1-E_q,z_2-u_2,y_3+z_3-U_q)\ge0.
\]

LR: q+E_q+U_q≤x_1−b_1+y_3−1、N−q≤z_1−x_1、q≤y_3−1 より margin≥b_3+1>0。

### A2.8.2 最後が row 1、sink A

X≥b_1,u_2≤z_2。A2.4 の reciprocal lemma を A=z_1,B=y_3,v=x_3,b=b_1,c=0 に適用。

H=N−R、d=z_1−x_1、a=x_3−y_3、E=−Y、V=d−X とし D_*=a+d−b_1−(H+E+V)≥0。

λ=(N,1,R−1) の係数は

\[
λC=(X-b_1,z_2-u_2,x_3+z_3+Y).
\]

前二つは sink A 条件で非負。第三は last success q=R−1 の residue U_q を用い、N=N_q+ℓ、ℓ≥1 より x_3+z_3+Y=z_3+(ℓ+1)y_3-U_q>0。従って全係数非負。その margin は exact に

\[
|λC|-|λ|=D_*+(z_2-u_2)+b_3+2(y_3-R)\ge b_3>0.
\]

### A2.8.3 最後が row 1、sink C

u_2≤y_2,Y≥−b_3。直前が F_1 なので X+x_1≥b_1+1。置く

\[
P=x_1+X-b_1-1\ge0,\quad B_*=b_3+Y\ge0,
\quad A_*=x_1-b_1-1,\quad C_*=y_3-1.
\]

successful indices b_1<i≤q の各々は E_i>A_*−P または U_i>C_*−B_* を満たす。

両方偽なら h=R−i,k=N−N_i に対し

\[
h z_1-kx_1=E_i+X\le0,
\]
\[
(k+1)y_3-hx_3=U_i+Y\le y_3-b_3-1,
\]

ゆえに z_1/x_1≤k/h<x_3/y_3。1≤h≤q の PREFIX に反する。

injectivity の slot counting で q−b_1≤P+B_*（q≤b_1 の場合は自明）。従って D_*=P+B_*−(q−b_1)≥0。

λ=(N−1,1,R) の係数は (x_1+y_1+X,y_2-u_2,b_3+Y)。第一は row-1 predecessor 条件 X+x_1≥b_1+1 で正、後二つは sink C 条件で非負。従って

\[
|λC|-|λ|=(y_1-N)+(y_2-u_2)+D_*\ge0.
\]

これで全二色 sink が排除された。

### A2.9 Third color の初出を排除

初手は row 1。third-color first firing は {1,2}→3 または {1,3}→2。

row 2 の直後に row 3 が初出するなら、前stateの第一座標≥y_1+z_1+1=2y_1+b_1+1。しかし box は≤x_1+y_1−1。START x_1<y_1 に反する。row 3 の直後に row 2 も同じ。従ってどちらも row 1 の直後に初出する。

### A2.9.1 {1,2}→3

third-color source の counts は (N−1,Q−1,0)。直前 F_1 と現在 F_3 を式に代入すると

\[
1-x_1\le X\le-b_1-1,
\quad z_2+1-x_2\le Y\le-1,
\quad1\le u_3\le y_3-1.
\]

従って N=N_Q、E=−X∈[1,x_1−1]。prior 1,…,Q−1 は success。

全 prior E_j>E。もし E_j≤E なら h=Q−j,k=N−N_j について kx_1−hy_1=E−E_j≥0。一方 D=Nz_2−Qx_2=Y+b_2≤b_2−1、D_j=z_2−U_j≥b_2+1 なので kz_2−hx_2=D−D_j<0。PREFIX separator となる。

ゆえに Q+E≤x_1、N−Q≤y_1−x_1 から N+E≤y_1。

また y_2+D≥Q。D≥0 なら Q≤y_2 で明らか。D<0 なら A2.7.3 と同じ差計算により全 prior U_j>−D、従って Q−D≤y_2。

λ=(N,Q,1) に対して

\[
λC=(z_1-E,y_2+D,y_3+z_3-u_3)\ge(N+b_1,Q,z_3+1)\geλ.
\]

矛盾。

### A2.9.2 {1,3}→2

source counts (N−1,0,R−1)、直前 F_1 と現在 F_2 から

\[
b_1+1-x_1\le X\le b_1-1,
\quad1\le u_2\le y_2-1,
\quad y_3+1-x_3\le Y\le-b_3-1.
\]

P=b_1−X≥1、W_*=-b_3−Y≥1。prior 1,…,R−1 は success。

全 prior E_j>P。反対に E_j≤P とすれば h=R−j,k=N−N_j に対し D_1=hz_1−kx_1=E_j+X≤b_1。

D_1≤0 なら k/h≥z_1/x_1。一方 (k+1)y_3−hx_3=U_j+Y≤y_3-b_3-2<y_3 なので k/h<x_3/y_3、PREFIX に反する。

1≤D_1≤b_1 なら、successful prefix が存在するので b_1≤x_1−2 であり、k=floor(hz_1/x_1)、N_h=k+1。従って E_h=x_1−D_1≥x_1−b_1 となり、index h<R の successful EBOX E_h≤x_1−b_1−1 に直接反する。これは early-exit strip の整数式による表現である。

次に全 prior U_j>W_*。反対に U_j≤W_* とすれば、既に示した E_j>P により b_1+1≤D_1≤x_1−2。k'=k+1 とすると

\[
k'x_1-hz_1>0,\quad hx_3-k'y_3=W_*-U_j+b_3>0,
\]

これも PREFIX separator。

injectivity から R+P≤x_1−b_1、R+W_*≤y_3。直前が row 1 source なので N≤ceil(Rz_1/x_1)。R<x_1 と z_1=x_1+d より N−R≤d、従って N+P≤y_1。

λ=(N,1,R) について

\[
λC=(z_1-P,y_2+z_2-u_2,y_3-W_*)\ge(N+b_1,z_2+1,R)\geλ,
\]

矛盾。

### A2.10 Exhaustion と upstream への接続

有限の最大 in-box path が sink に終わるとする。

- row 1 のみなら A2.6 が矛盾。
- ちょうど二色なら A2.7/8 が矛盾。
- 三色なら、その第三色の最初の firing が A2.9 に反する。

従って最大 path の終端には必ず positive out-of-box firing が存在する。

これでDPEを証明した。 これは MINBOX k=1 からの matrix INPUT に直接適用できる。

### A2.10.1 同じ actual f_ε への最終接続

付録A1 から、三本の actual arms を仮定した同じ半群・同じ socle element に対し

\[
f_\varepsilon=m+\sum_i(p_i-1)n_i,\qquad
q_i=f_\varepsilon-\lambda_i n_i\in PF(\Gamma),
\quad1\le p_i\le\lambda_i\le\alpha_i-1
\]

が得られる。まず color A、すなわち \(\alpha_i=a_i\)、\(p=x\) とする。

合計 \(t\) 回 firing した state を \(u=p-rC\)、\(|r|_1=t\) とする。\(Cn=m\mathbf1\) により

\[
\boxed{f_A=(t+1)m+\sum_i(u_i-1)n_i.}
\tag{SAME-F}
\]

positive state では全 \(u_i\ge1\) なので、これは同じ \(f_A\) の genuine factorization である。元の \(\Gamma,m,n_i,f_A\) は変わっていない。

DPE が与える最初の positive out-of-box state \(u^*\) も同じ式を満たす。全座標正のまま \(\mathcal B=\prod_i[1,a_i-1]\) を出るので、ある \(i\) に対し \(u_i^*\ge a_i\)。従って

\[
u_i^*-1\ge a_i-1\ge\lambda_i.
\]

この一個の final coefficient vector から \(\lambda_i n_i\) を除くと

\[
q_i=(t+1)m+(u_i^*-1-\lambda_i)n_i
+\sum_{j\ne i}(u_j^*-1)n_j\in\Gamma,
\]

actual PF gap に反する。signed relation の semantic subtraction は使用していない。

color B は、generator の奇 permutation と \(a/b\)、A/B の完全な同時交換によって color A に移る。三本の actual PF elements とその arm bounds も同時に交換されるため、同じ結論が成立する。

したがって三本の同色 actual arms は存在せず、

\[
\boxed{\text{THREE-ARM CLOSED}.}
\]

各色の actual rows は corner \(f_\varepsilon\) または arm \(f_\varepsilon-\lambda n_i\) である。同一方向に異なる depths の二本は PF comparability に反する。corner と同色 arm の共存も同じ理由で不可能。従って一色に三本あれば三方向の arms が一本ずつ必要だが、今それを排除した。ゆえに canonical six-arm classification の範囲で

\[
\boxed{\text{COLOR-CAP}\le2.}
\]

MINBOX → DPE → SAME-F → THREE-ARM → COLOR-CAP の接続には、追加の上流補題を必要としない。
