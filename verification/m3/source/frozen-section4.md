# 04 — 非対称の局所幾何と四行分類

### G4.1 共通設定

Γ=⟨m,n_i,n_j,n_k⟩、m は multiplicity、F=F(Γ)、W=F+m、H=⟨n_i,n_j,n_k⟩ とする。canonical reduction は

\[
q\in Q:=PF(Γ)\setminus\{F\}\Longrightarrow c_q=W-q\in Γ
\]

を保証する。各 actual q について q+m,c_q∈H、c_q−m∉Γ、q∉Γ とする（canonical elementary lemmas）。

\[
SH(q)=\{r:q+n_r\in H\},\qquad D(c)=\{r:c-n_r\in H\}.
\]

KEY は ∅≠D(c_q)⊆SH(q) であり、等号を仮定しない。KEY 自体は q+n_r−m∈Γ を仮定すると F=(c_q−n_r)+(q+n_r−m)∈Γ となることから直証明できる。

Herzog convention は cyclic (i,j,k) に対して

\[
ρ_i=a_i+b_i,\quad ρ_in_i=b_jn_j+a_kn_k,
\]
\[
ρ_jn_j=a_in_i+b_kn_k,\qquad ρ_kn_k=b_in_i+a_jn_j,
\tag{H}
\]

全 a_r,b_r は正整数、ρ_r は H における critical multiplier とする。

KEYからSH(q)は空でない。SH(q)={r}となる行をsingleton S_r、
|SH(q)|=2となる行をdoubleton、SH(q)={i,j,k}となる行をcornerと呼ぶ。
cornerはPF(H)の元である。doubletonのmissing direction rはr∉SH(q)で定義する。
doubletonのsix-arm atlasをG4.1.1で示す：

\[
A_r(λ)=f_A-λn_r\quad(1≤λ≤a_r-1),
\]
\[
B_r(μ)=f_B-μn_r\quad(1≤μ≤b_r-1).
\]

三つの cyclic 表示を含む PF corner の正確な式は

\[
f_A=(ρ_i-1)n_i+(a_j-1)n_j-n_k
      =-n_i+(ρ_j-1)n_j+(a_k-1)n_k,
\]
\[
f_B=(ρ_i-1)n_i-n_j+(b_k-1)n_k,
\qquad f_A-f_B=a_jn_j-b_kn_k.
\tag{PF}
\]

同じ arm の二行、corner とその同色 arm は PF antichain に反する。triple-support row は lower corner 高々一つ。higher corner は F(H)≥F(Γ) と q<F(Γ) に反する。

### G4.1.1 Six-arm atlas の短い証明

q∉H、q+n_j,q+n_k∈H、q+n_i∉H とする。q+ℓn_i∉H を満たす最大整数 ℓ≥0 を取る。H は数値半群なので存在し、q+n_i∉H より ℓ≥1。f=q+ℓn_i は f+n_i∈H を満たし、q+n_j,q+n_k∈H に ℓn_i を足せば f+n_j,f+n_k∈H。従って f∈PF(H)={f_A,f_B}。

f=f_A で ℓ≥a_i と仮定する。canonical 式は
\[
q+n_j=(a_i-ℓ-1)n_i+(ρ_k-1)n_k.
\]
これを genuine H-factorization Xn_i+Yn_j+Zn_k と比較すると
\[
(ρ_k-1-Z)n_k=(ℓ-a_i+1+X)n_i+Yn_j.
\]
右辺は正なので左係数は正、しかも ρ_k 未満。criticality に反する。よって 1≤ℓ≤a_i−1。

f=f_B の場合は q+n_k=(b_i−ℓ−1)n_i+(ρ_j−1)n_j を使って同様に ℓ≤b_i−1。

逆に A_i(λ),1≤λ≤a_i−1 について
\[
q+n_j=(a_i-λ-1)n_i+(ρ_k-1)n_k\in H,
\]
\[
q+n_k=(ρ_i-λ-1)n_i+(a_j-1)n_j\in H.
\]
q または q+n_i が H に入れば、足りない非負倍の n_i を足して f_A∈H となるため、両方 gap。B の場合も対応する二 canonical 式で同じ。色・depth は上記最大 ℓ により一意。

これでSTD_HERZOGからsix-arm atlasを得た。

### G4.2 基本的な actual antichain と係数制約

異なる PF rows q,q' について q−q'∉Γ, q'−q∉Γ。従って異なる complements c,c' も Γ-antichain である。

singleton S_r は KEY により c_S=κ_r n_r。もしその H-factorization が別方向を使えば D(c_S)⊆{r} に反する。また κ_r≥ρ_r なら (H) がその別方向の factorization を与える。従って

\[
1≤κ_r≤ρ_r-1.
\tag{SR}
\]

同方向に二 singleton は pure-ray comparability に反する。singleton S_r が存在すれば、他の任意の complement の任意の H-factorization で r-coordinate は κ_r−1 以下である。そうでなければ c−κ_r n_r∈H となり antichain に反する（差ゼロなら同じ row）。

また W の任意の H-factorization で r-coordinate≤κ_r−1。κ_r 個を除ければ q_S∈H となるためである。一方、q_S+n_r∈H より最大値 κ_r−1 は実現する。

arm missing i の complement は n_i を一切使わず

\[
c=y n_j+z n_k,\qquad 0≤y<ρ_j,\quad0≤z<ρ_k.
\tag{CB}
\]

実際 y≥ρ_j 又は z≥ρ_k なら (H) により n_i を使う表示ができて KEY に反する。この二係数表示は一意：二表示の差は j/k の pure relation で、非零なら片側係数が critical multiplier 未満となる。

### G4.3 Critical-box uniqueness と integer-kernel basis

**Critical-box uniqueness.** 二つの異なる非負 factorization がいずれも全座標 X_r<ρ_r を満たすことはない。差は非零 kernel vector で、三座標のため符号の一方は一座標だけ。その一座標の絶対値は ρ_r 未満なので criticality contradiction。

**Integer basis.**

\[
r_j=(a_i,-ρ_j,b_k),\qquad r_k=(b_i,a_j,-ρ_k)
\]

は Z-kernel の basis である。線形独立な二 vector は real kernel を張る。任意の整数 kernel vector からその real coefficients の床倍を引くと

\[
v=xr_j+yr_k\in\mathbb Z^3,\qquad0≤x,y<1.
\]

x+y>0 なら 0<v_i<ρ_i、−ρ_j<v_j<a_j、−ρ_k<v_k<b_k。v_j,v_k≤0 なら i-criticality、v_j≥0 なら負の k-coordinate の絶対値<ρ_k に対する criticality、v_k≥0 なら j-criticality が矛盾を与える。全非負 kernel vector は正の n_r により非零ではあり得ない。よって x=y=0 で、もとの real coefficients は整数。

この lemma は hidden connectivity・factorization uniqueness の仮定を用いない。uniqueness を使用する箇所は上記明示した critical box の中に限る。

### G4.4 Corner と singleton は共存しない

corner f_A と singleton S_j を仮定する。c_0=W-f_A∈H、c_S=κ n_j、κ≤ρ_j−1 である。すると同じ actual q_S に対し

\[
q_S+n_i=f_A+c_0-κn_j+n_i
=(ρ_j-1-κ)n_j+(a_k-1)n_k+c_0\in H.
\]

i は singleton S_j の missing direction なので矛盾。cyclic permutation で各 singleton direction に適用できる。f_B は color reversal による同じ議論である。

これは「四行における corner 排除」より強い局所共存排除である。ただし singleton を含まない corner＋三反対色 arm には別途 COLOR-CAP が必要。

### G4.5 Matched A_i/B_i synchronization

actual A_i(λ),B_i(μ) を取り、complements を

\[
c_A=y n_j+z n_k,\qquad c_B=y'n_j+z'n_k
\]

とする。(CB) の bounds を満たす。Δ_j=y'−y, Δ_k=z'−z とすれば

\[
v=(μ-λ,a_j-Δ_j,-b_k-Δ_k)\in\ker_\mathbb Z(n).
\]

G4.3 により v=u r_j+v_0 r_k、u,v_0∈Z。座標 bounds は

\[
2-a_i≤v_i≤b_i-2,
\]
\[
1-b_j≤v_j≤ρ_j+a_j-1,\qquad v_k≤a_k-1.
\]

u≥1,v_0≤0 なら j≤−ρ_j で矛盾。u≤−1,v_0≥1 なら j≥ρ_j+a_j で矛盾。u≥0,v_0≥1 なら i≥b_i で矛盾。u≤−1,v_0≤0 なら i≤−a_i で矛盾。残る u=0,v_0≤−1 は k≥ρ_k で矛盾。従って u=v_0=0。

よって

\[
λ=μ,\qquad y'=y+a_j,\qquad z'=z-b_k.
\]

g=y≥0, α=z'≥0 と置くと

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

P>a_i,b_i、g≤b_j−1、α≤a_k−1。g,α の strict positivity は仮定せず、境界 g=0 / α=0 も含む。

### G4.5.1 Matched pair と singleton

S_j があれば κ_j<ρ_j。complement antichain と c_B=Rn_j+αn_k から κ_j>R（等号で α=0 なら同じ complement、それ以外は比較可能）。同じ q_{S_j} について

\[
q_{S_j}+n_k=(P-1)n_i+(R-κ_j-1)n_j+Tn_k
\]

に a_i n_i+b_k n_k=ρ_j n_j を一回使うと

\[
q_{S_j}+n_k=(P-a_i-1)n_i+(R-κ_j-1+ρ_j)n_j+αn_k\in H.
\]

P−a_i−1=b_i−λ−1≥0、κ_j≤ρ_j−1 なので全係数非負。missing k に反する。

S_k は dual：κ_k>T、q_{S_k}+n_j の b_i n_i+a_j n_j を ρ_k n_k に置換して全非負。従って matched pair と共存できる singleton は S_i だけ。


## M4 — root-free matched-pair level rigidity

G4.5の同じactual matched pairを固定し、\(q_A=A_i(\lambda),q_B=B_i(\lambda)\)、
\(\delta=a_i-\lambda\ge1,\beta=b_i-\lambda\ge1\)、\(g,\alpha\ge0\) とする。
\(P=\rho_i-\lambda,R=a_j+g,T=b_k+\alpha\)。すると正整数Lと非負整数t,uが存在し、
\[
q_A+n_i=Lm+(a_j+t)n_j+un_k,\qquad
q_B+n_i=Lm+tn_j+(u+b_k)n_k,
\]
\[
Pn_i=Lm+(t+1)n_j+(u+1)n_k.
\]
証明ではg=0、α=0も保持する。以下、G4.5のcomplement表示をCOMPと呼ぶ。

### M4.2 actual positive-m returns は独立に選択できる

PF 性により E_A=q_A+n_i,E_B=q_B+n_i は Γ に属する。どの Γ-factorization にも n_i は現れない。現れれば、その同じ非負係数ベクトルから n_i を一個除いて q_A または q_B が Γ に入ってしまう。

さらに E_A,E_B は H に属さない。以下はその短い pure-H 証明である。

### E_A∉H

仮に E_A=Xn_j+Yn_k、X,Y≥0 とする。canonical 式から

\[
Pn_i=(X-a_j+1)n_j+(Y+1)n_k.
\]

X≥a_j−1 なら 0<P<ρ_i に対する criticality contradiction。

X≤a_j−2 なら

\[
(Y+1)n_k=Pn_i+(a_j-1-X)n_j.
\]

criticality より Y+1≥ρ_k。R_k を一回差し引くと

\[
δn_i=(X+1)n_j+(Y+1-ρ_k)n_k.
\]

これは 0<δ<ρ_i に反する。ここまで m 係数は最初からゼロであり、criticality の使用は合法。

### E_B∉H

同様に E_B=Xn_j+Yn_k とすると

\[
Pn_i=(X+1)n_j+(Y-b_k+1)n_k.
\]

Y≥b_k−1 なら P<ρ_i に反する。Y≤b_k−2 なら

\[
(X+1)n_j=Pn_i+(b_k-1-Y)n_k,
\]

ゆえに X+1≥ρ_j。R_j を差し引けば

\[
βn_i=(X+1-ρ_j)n_j+(Y+1)n_k,
\]

となり 0<β<ρ_i に反する。

従って二つの actual 元には必ず positive-m returns が存在する。各元ごとに、正の m 係数の最小値を選び、一つの実現表示を固定する。

\[
E_A=L_A m+U_jn_j+U_kn_k,\qquad
E_B=L_B m+V_jn_j+V_kn_k,
\tag{RET}
\]

\[
L_A,L_B\ge1,\qquad U_j,U_k,V_j,V_k\ge0.
\]

これは空でない自然数集合の明示的最小値である。固定するのは同じΓ,F,W,q_A,q_Bとcanonical係数であり、選ぶのはRETの二つの非負係数ベクトルだけである。

### M4.3 四つの coordinate caps

RET と COMP を加えて一個の m を除くと、同じ F+n_i に対して

\[
F+n_i=(L_A-1)m+(U_j+g)n_j+(U_k+T)n_k,
\]
\[
F+n_i=(L_B-1)m+(V_j+R)n_j+(V_k+α)n_k
\tag{FI}
\]

という genuine 表示が得られる。

例えば U_j+g≥ρ_j なら、含まれた ρ_jn_j を a_in_i+b_kn_k に置換し、同じ最終表示から n_i を除けば F∈Γ。a_i≥1 がその一個を供給する。他の三つも R_j/R_k により同様。

従って

\[
U_j+g\leρ_j-1,\quad U_k+T\leρ_k-1,
\]
\[
V_j+R\leρ_j-1,\quad V_k+α\leρ_k-1.
\tag{CAP}
\]

### M4.4 Unequal levels を一括排除

置く

\[
t=U_j-a_j,\quad K=U_k+b_k,\quad
x=V_j-t,
\quad y=K-V_k.
\]

canonical 差 E_B=E_A−a_jn_j+b_kn_k と RET から

\[
(L_A-L_B)m=xn_j-yn_k.
\tag{DIFF}
\]

CAP から特に

\[
-ρ_j<x<ρ_j,\qquad -ρ_k<y<ρ_k.
\tag{BOX}
\]

厳密には

\[
R+1-ρ_j\le x\leρ_j-g-1,
\quad T+1-ρ_k\le y\leρ_k-α-1.
\]

### M4.4.1 L_A>L_B は不可能

σ=L_A−L_B≥1 とする。もし V_k≥b_k なら

\[
E_A=L_Bm+(V_j+a_j)n_j+(V_k-b_k)n_k
\]

は E_A の strictly lower positive-m actual return であり、L_A の最小性に反する。従って V_k≤b_k−1。

ゆえに C:=y=U_k+b_k−V_k≥1 であり、DIFF は

\[
σm+C n_k=Δ n_j,
\qquad Δ:=x>0.
\]

BOX により Δ<ρ_j。

R_j を completed zero identity として加えると、同じ数 W に対し

\[
W=(β-1)n_i+(ρ_j+R-1)n_j+(α-1)n_k
\tag{WJ}
\]

という exact 表示がある。**α=0 なら k 係数は −1 であり、これは signed intermediate にすぎない。** ここへ σm+C n_k−Δn_j=0 を completed identity として加え、F=W−m を用いると

\[
\boxed{F=(σ-1)m+(β-1)n_i+(ρ_j+R-1-Δ)n_j+(α+C-1)n_k\inΓ.}
\tag{ABS+}
\]

全係数非負なので矛盾。特に α=0 でも C≥1 により α+C−1≥0。actual と呼ぶのは最終 ABS+ のみでよい。σ≥3 や σ≥5 は全く不要。

### M4.4.2 L_B>L_A は不可能

σ=L_B−L_A≥1 とする。もし t≥0 なら

\[
E_B=L_A m+t n_j+K n_k
\]

は actual な lower positive-m return となり L_B の最小性に反する。従って t<0。

ゆえに Δ:=x=V_j−t≥1。DIFF は

\[
σm+Δn_j=Cn_k,\qquad C:=y>0.
\]

BOX により C<ρ_k。

R_k を completed zero identity として加えると、同じ数 W に対し

\[
W=(δ-1)n_i+(g-1)n_j+(ρ_k+T-1)n_k
\tag{WK}
\]

という exact 表示がある。**g=0 なら j 係数は −1 であり、これは signed intermediate にすぎない。** ここへ σm+Δn_j−Cn_k=0 を completed identity として加え、F=W−m を用いると

\[
\boxed{F=(σ-1)m+(δ-1)n_i+(g+Δ-1)n_j+(ρ_k+T-C-1)n_k\inΓ.}
\tag{ABS-}
\]

再び全係数非負。特に g=0 でも Δ≥1 により g+Δ−1≥0。従って矛盾。

### M4.5 Equal-level matching と PRE 排除

以上より L_A=L_B=:L。DIFF は xn_j=yn_k となる。

BOX と tail criticality から x=y=0。実際、どちらかがゼロなら両方ゼロであり、非零なら同符号だから |x|n_j=|y|n_k が 0<|x|<ρ_j に反する。

従って

\[
V_j=t\ge0,\qquad V_k=U_k+b_k.
\]

u:=U_k とすれば

\[
\boxed{E_A=Lm+(a_j+t)n_j+u n_k,\quad
E_B=Lm+t n_j+(u+b_k)n_k,\quad t,u\ge0.}
\tag{EA/EB}
\]

canonical E_A の式と比較して

\[
\boxed{Pn_i=Lm+(t+1)n_j+(u+1)n_k.}
\tag{P-FIBER}
\]

右辺は genuine。PRE=t<0 は全域で排除された。



### G4.5.2 Matched pair と extra arms

M4のroot-free level theorem は、(MATCH) と二 actual PF rows のみから

\[
q_A+n_i=Lm+(a_j+t)n_j+u n_k,
\]
\[
q_B+n_i=Lm+t n_j+(u+b_k)n_k,
\qquad L≥1,\ t,u≥0
\tag{EA/EB}
\]

を与える。これは HIGH root を仮定しない。

従って f_A=(q_A+n_i)+(λ−1)n_i の genuine factorization は j-coordinate≥a_j。actual A_j(μ), μ≤a_j−1 があれば、この同じ factorization から μn_j を除いて A_j∈Γ となる。矛盾。同様に f_B の k-coordinate≥b_k より B_k は共存不能。

従って matched i に追加できる別 arm は B_j または A_k のみ。この時点で SQ は直接排除される。

### G4.5.3 Matched pair と S_i も不可能（追加の短い閉鎖）

(EA/EB) から
\[
Pn_i=Lm+(t+1)n_j+(u+1)n_k
\]
を得るので Pn_i−m∈Γ。singleton S_i の complement が κn_i なら、(MATCH) の genuine W 表示により κ≤P−1 は q_{S_i}∈H を与える。従って κ≥P。すると
\[
c_{S_i}-m=(κ-P)n_i+(Pn_i-m)\in Γ,
\]
actual complement の Apéry 性に反する。従って matched pair はどの singleton とも共存不能。TYPE Iはここで排除される。TYPE Iという候補は最終分類に残らない。

### G4.6 同色二 arm の正確な complement geometry

actual A_i(λ),A_k(ν) を取る。c_i=y n_j+z n_k、c_k=x n_i+y'n_j とすると

\[
(λ+x,y'-y,-ν-z)=u r_j+v r_k.
\]

i>0,k<0, |j|<ρ_j から u≥0,v≥1。u≤−1,v≥1 は j≥ρ_j+a_j に反し、u≤−1,v≤0 は i≤0 に反し、u≥0,v≤0 は k≥0 に反する。

i≤ρ_i+a_i−2 より u≤1。−k≤ρ_k+a_k−2 より v≤1。従って (u,v)=(0,1) または (1,1) のみ。

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

表示中の係数は元の genuine complement の係数なので非負。特に Case A なら b_i−λ≥0。

### G4.6.1 残りの方向の singleton S_j は不可能

Case A の W は
\[
W=(ρ_i-λ-1)n_i+(a_j+y-1)n_j+(ρ_k-ν-1)n_k.
\]
q_{S_j}+n_i に a_i n_i+b_k n_k=ρ_j n_j を一回使うと
\[
q_{S_j}+n_i=(b_i-λ)n_i+(a_j+y-κ_j-1+ρ_j)n_j+(a_k-ν-1)n_k\in H.
\]
全係数非負なので missing i に反する。

Case B では
\[
W=(ρ_i-λ-1)n_i+(ρ_j+y'-1)n_j+(a_k-ν-1)n_k.
\]
κ_j≤ρ_j−1 より q_{S_j}=W−κ_jn_j 自体が H に入る。矛盾。

### G4.6.2 同時に二 singleton S_i,S_k を伴うことも不可能

Case A：y=0 なら c_i は pure k-ray で c_{S_k} と比較可能。従って y≥1。antichain より κ_k>ρ_k−ν。上記 W に対して q_{S_k}+n_i の b_i n_i+a_j n_j を ρ_k n_k に置換すると
\[
q_{S_k}+n_i=(a_i-λ)n_i+(y-1)n_j+(ρ_k-ν-κ_k-1+ρ_k)n_k\in H.
\]
最後の係数は κ_k≤ρ_k−1 により≥ρ_k−ν≥1。missing i に反する。

Case B：y'=0 なら c_k は pure i-ray で c_{S_i} と比較可能。従って y'≥1。q_{S_i}+n_k の ρ_j n_j を a_i n_i+b_k n_k に置換すると
\[
q_{S_i}+n_k=(ρ_i-λ+a_i-κ_i-1)n_i+(y'-1)n_j+(ρ_k-ν)n_k\in H.
\]
最初の係数≥a_i−λ≥1。missing k に反する。

従って同色二 arm は二 singleton と共存しない。color reversal で B 同士も同じ。

### G4.7 異色・異方向二 arm：二つの向きを区別する

### G4.7.1 B_i(λ),A_k(ν) の向き

c_{B_i}=y n_j+z n_k、c_{A_k}=x n_i+y'n_j と置くと
\[
(λ+x,a_j-y+y',-b_k-ν-z)=u r_j+v r_k.
\]

i>0、−b_j<j<ρ_j+a_j、−k<2ρ_k、i<ρ_i+b_i により (u,v)=(0,1) のみ：まず mixed-sign coefficients は j-bound または i>0 に反し、u≥1,v=1 は j≤−b_j、u≥1,v≥2 は i≥ρ_i+b_i、u=0,v≥2 は −k≥2ρ_k に反する。

従って正整数 β=b_i−λ、α=a_k−ν と R=y=y'≥0 により
\[
c_{B_i}=R n_j+αn_k,\qquad c_{A_k}=βn_i+R n_j.
\tag{BA}
\]

Wのexact表示は
\[
W=(a_i+β-1)n_i+(R-1)n_j+(b_k+α-1)n_k
\]
と書ける。ただし R=0 ならこの表示は signed なので、次の完成表示だけを actual と呼ぶ：
\[
W=(β-1)n_i+(R+ρ_j-1)n_j+(α-1)n_k.
\tag{BA-W}
\]
これは a_i n_i+b_k n_k=ρ_j n_j による exact identity で全係数非負。

S_j があれば κ_j≤ρ_j−1 なので (BA-W) から q_{S_j}∈H、矛盾。従って singleton は i/k 方向に限られる。

### G4.7.2 A_i(λ),B_k(ν) の反対向き

同様に kernel vector は
\[
(λ+x,-a_j-y+y',b_k-ν-z)=u r_j+v r_k.
\]

i>0、−ρ_j−a_j<j<b_j、−ρ_k<k<b_k、i<ρ_i+a_i より (u,v)=(1,1) のみ。mixed signs は j 又は k の bound に反し、u=0 又は v=0 も k-bound に反する。u≥2 は i-bound、v≥2 は k-bound に反する。

従って P=ρ_i−λ、T=ρ_k−ν と y≥0、y'=y+a_j−b_j≥0 により
\[
c_{A_i}=y n_j+Tn_k,\qquad c_{B_k}=Pn_i+y'n_j,
\]
\[
W=(P-1)n_i+(a_j+y-1)n_j+(T-1)n_k.
\tag{AB-reverse}
\]

S_i を仮定すると y'=0 は pure-ray comparability に反するので y'≥1。a_j+y−1=b_j+y'−1≥b_j、T−1≥a_k より b_jn_j+a_kn_k を ρ_in_i に置換できる：
\[
W=(P+ρ_i-1)n_i+(y'-1)n_j+(b_k-ν-1)n_k.
\]
κ_i≤ρ_i−1 より q_{S_i}∈H、矛盾。

S_k を仮定すると y=0 は pure-ray comparability に反するので y≥1。P−1≥b_i、a_j+y−1≥a_j より b_i n_i+a_j n_j を ρ_k n_k に置換できる：
\[
W=(a_i-λ-1)n_i+(y-1)n_j+(T+ρ_k-1)n_k.
\]
κ_k≤ρ_k−1 より q_{S_k}∈H、矛盾。

従ってこの反対向きで共存できる singleton は S_j だけ。

### G4.8 三 singleton があれば |Q|=3

S_i,S_j,S_k が存在すると G4.2 より、W の全 factorization は全座標≤κ_r−1<ρ_r を満たす。G4.3 の critical-box uniqueness より W は一つの factorization だけを持つ。それぞれの座標最大値 κ_r−1 が実現するため
\[
W=(κ_i-1)n_i+(κ_j-1)n_j+(κ_k-1)n_k.
\]

別 row q の complement c は antichain により全座標≤κ_r−1。従ってその任意の genuine factorization はこの同じ W の factorization に coefficientwise に入り、q=W−c∈H。矛盾。

これは全体の factorization uniqueness を仮定していない。singleton caps から critical box に閉じ込めた上で G4.3 により証明した。

### G4.9 四行の exhaustive classification

四つの異なる actual Q-rows を取る。singleton 数 s、corner 数 c、arm 数 a とする。

**corner のある場合。** G4.4 より singleton はない。corner と同色 arm は antichain によりない。従って c=1,a=3 なら三 arm は全て反対色。同じ arm の重複は不可能なので三方向全部を使う。ここだけで付録A2のTHREE-ARM / COLOR-CAP定理を適用する。

以後 c=0。G4.8 より s≤2。

**s=2,a=2。** matched pair は G4.5.1 により一方向の singleton しか許さない。同色二 arm は G4.6 により二 singleton と共存不能。異色異方向の反対向き G4.7.2 も singleton を一方向しか許さない。従って G4.7.1 の向きで singleton は i,k。正確に
\[
S_i,\quad B_i(λ),\quad A_k(ν),\quad S_k
\]
という PATH。

**s=1,a=3。** 三 arm が同色なら三方向を使う。singleton の方向以外の二 arm に G4.6.1 を使って矛盾。従って色は 2+1。

matched pair があるなら pivot i を取り、G4.5.1 より singleton は S_i。G4.5.2 より残りの arm は B_j 又は A_k。両者は color reversal と cyclic convention の反転で同一 TYPE I orbit：
\[
S_i,\quad A_i(λ),\quad B_i(λ),\quad A_k(ν).
\]

matched pair がなければ三 missing directions は全て異なる。同色二つを A_i,A_k、反対色を B_j と書く。反対向き pair A_k,B_j に G4.7.2 を適用すると singleton は S_i のみ。正確に
\[
S_i,\quad A_i(λ),\quad B_j(μ),\quad A_k(ν)
\]
という TYPE II。

**s=0,a=4。** 三方向・各色の同じ arm 高々一つなので、ある方向 i で A_i,B_i が共存する。G4.5.2 により追加可能な arm は B_j,A_k の二本だけ。従って
\[
B_j(μ),\quad A_i(λ),\quad B_i(λ),\quad A_k(ν)
\]
という CHAIN。

以上でactual four-row nonsymmetric counterexampleはPATH / TYPE II / CHAINへ縮約される。SQはG4.5.2、TYPE IはG4.5.3で排除した。

### G4.11 末端証明に必要な scalar input の抽出

### G4.11.1 一般 singleton saturation lemma

同じ actual W が
\[
W=(P-1)n_i+(R-1)n_j+(T-1)n_k,
\quad1≤P≤ρ_i,\quad1≤R≤ρ_j,\quad1≤T≤ρ_k
\tag{BOX-W}
\]
と書け、singleton S_i の complement が κ n_i とする。G4.2 より W の全 factorization の i-coordinate は κ−1<ρ_i 以下で、最大値 κ−1 が実現する。

任意の W-factorization と (BOX-W) の差を u r_j+v r_k とする。u≥1,v≤0 なら j-coordinate≤R−1−ρ_j<0。u≤0,v≥1 なら k-coordinate≤T−1−ρ_k<0。u,v≥1 なら i-coordinate≥P−1+ρ_i≥ρ_i で singleton cap に反する。残りは u,v≤0 で、その i-coordinate は P−1 以下。

従って最大値は P−1、すなわち
\[
\boxed{κ=P.}
\]

cyclic version も成立する。全体的な fiber uniqueness は不要。

### G4.11.2 CHAIN の全 canonical positive box

G4.9 の CHAIN rows を取る。matched i により (MATCH) が成立する。right-oriented pair B_j(μ),A_i(λ) に G4.7.1 を cyclic (j,k,i) で適用すると
\[
c_{A_i}=(b_j-μ)n_j+Tn_k,\qquad c_{B_j}=(a_i-λ)n_i+Tn_k.
\]
matched complement の一意な j/k 表示との比較より
\[
g=b_j-μ≥1,\quad R=ρ_j-μ.
\]
同様に B_i(λ),A_k(ν) から
\[
α=a_k-ν≥1,\quad T=ρ_k-ν,
\]
\[
c_{A_k}=(b_i-λ)n_i+Rn_j.
\]
従って δ=a_i−λ≥1、β=b_i−λ≥1 とともに
\[
P=λ+δ+β,\quad R=a_j+g,\quad T=b_k+α
\]
を持ち、四 complements は
\[
c_{B_j}=δn_i+Tn_k,\quad c_{A_i}=g n_j+Tn_k,
\]
\[
c_{B_i}=Rn_j+αn_k,\quad c_{A_k}=βn_i+Rn_j.
\]
これは HIGH / CENTRAL 入口が使用する strict canonical core そのものである。

### G4.11.3 TYPE II の全 input

S_i,A_i(λ),B_j(μ),A_k(ν) を取る。A_i,A_k の G4.6 Case A/B と B_j,A_i の G4.7.1 を比較する。Case B なら c_{A_i} の j-coordinate は b_j+y' と b_j−μ の両方に等しく、y'=−μ<0 となり不可能。従って Case A。

その結果
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
よって同じ W は (BOX-W) の形で、singleton saturation より c_{S_i}=Pn_i。
従って
\[
q_{S_i}=-n_i+(R-1)n_j+(T-1)n_k.
\]
arm-domain による 1≤λ≤a_i−1、1≤μ≤b_j−1、1≤ν≤a_k−1 と上記 λ≤b_i が、T6.1 の全 input を与える。

### G4.11.4 PATH の canonical endpoint rays

PATH の B_i(λ),A_k(ν) から G4.7.1 の α=a_k−ν>0、β=b_i−λ>0、R≥0 を得る。R=0 なら c_{A_k}=βn_i は c_{S_i} と pure-ray comparable（又は同一 row）となるため不可能。従って R≥1。

また c_{B_i} の missing-i critical box より R<ρ_j。従って
\[
P=a_i+β=ρ_i-λ,\quad T=b_k+α=ρ_k-ν,
\]
\[
W=(P-1)n_i+(R-1)n_j+(T-1)n_k
\]
は (BOX-W) を満たす。singleton saturation を i,k にそれぞれ適用すると
\[
c_{S_i}=Pn_i,\qquad c_{S_k}=Tn_k.
\]
q_L=q_{S_i},q_A=q_{A_k},q_B=q_{B_i},q_R=q_{S_k} と命名すれば
\[
q_L+a_in_i=q_A+Rn_j,
\quad q_A+βn_i=q_B+αn_k,
\quad q_R+b_kn_k=q_B+Rn_j.
\]
このactual PATH ladderをP5へ渡す。q_A/q_B はここでは ladder 上のラベルであり Herzog color を意味しない。
