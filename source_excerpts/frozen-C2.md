# 02 — canonical reduction

**C2.** 第01章のcanonical条件の下で次が成立する。

## 共通設定

Γ=⟨m,n₁,n₂,n₃⟩ は数値半群、mはmultiplicity、FはFrobenius数、H=⟨n₁,n₂,n₃⟩、W=F+m、𝒜=Ap(Γ,m)。Q=PF(Γ)\{F}。

canonical条件は

\[
W-\varphi\in\Gamma\quad(\varphi\in PF(\Gamma)).
\]

𝒜の元のfactorizationはmを含まないので𝒜⊆H。W∈𝒜であり、任意のw∈𝒜についてw−m≤F、従ってw≤W。

### C2.1 PF条件から全gapの条件へ

非負gap xを取る。有限集合 (x+Γ)\Γ の最大の整数φを取れば、任意の正のs∈Γについてφ+s∈Γである。従ってφ∈PF(Γ)、φ−x∈Γ。

\[
W-x=(W-\varphi)+(\varphi-x)\in\Gamma.
\]

外部のpositioned-semigroup criterionを引用せず、この方向を直接得た。

### C2.2 正確な二層分割

w∈𝒜についてb=W−w≥0とする。w=0の場合はb=W∈𝒜。w>0の場合x=w−mは非負gapであり、前節からb+m=W−x∈Γ。

- b∈Γなら、b−m∈Γは w+(b−m)=F∈Γを招くのでb∈𝒜。この場合b+m∉𝒜。
- b∉Γなら、b+m∈Γかつ(b+m)−m=b∉Γなのでb+m∈𝒜。

従って、ちょうど一方が成立する：W−w∈𝒜、またはW+m−w∈𝒜。

\[
\mathcal A_0=\{w\in \mathcal A:W-w\in \mathcal A\},\qquad \mathcal A_1=\mathcal A\setminus \mathcal A_0.
\]

x≤Γy、y∈𝒜₀なら W−x=(W−y)+(y−x)∈Γ。𝒜の元xとの和がWなのでW−x∈𝒜。従って𝒜₀はlower ideal、𝒜₁はupper filter。

𝒜₁上のι(w)=W+m−wは再び𝒜₁に入り、ι²=id、ι(x)−ι(y)=y−xだからorder-reversing involutionである。

Apéryのmaximal元はPF+mである。この対応も、q∈PFならq+m∈𝒜であり、それより大きい𝒜の元との差s>0がΓにあればq+s∈Γと矛盾することから分かる。逆にmaximalなw∈𝒜について、q=w−mはgapであり、q+sがgapならw+s∈𝒜となってmaximalityに反する。

q∈Qならq<F。q+m∈𝒜₀は W−(q+m)=F−q∈Γ\{0} によりmaximalityに反する。𝒜₁がupper filterであることと合わせて

\[
\operatorname{Max}\mathcal A_1=(PF\setminus\{F\})+m,
\]
\[
\operatorname{Min}\mathcal A_1=\{W-q:q\in Q\},\qquad
|\operatorname{Min}\mathcal A_1|=|Q|=t-1.
\]

また𝒜₀={h∈H:W−h∈H}。右辺のhについてh−m∈ΓならF=(h−m)+(W−h)∈Γとなるため、h∈𝒜である。

### C2.3 KEY：support-zero return の直接証明

q∈Q、c=W−q∈Γとし、c−nᵢ∈Hとなる方向iを取る。PF性によりq+nᵢ∈Γ。

仮にq+nᵢ−m∈Γなら

\[
F=(c-n_i)+(q+n_i-m)\in\Gamma,
\]

矛盾。従って

\[
q+n_i\in \mathcal A\subset H.
\]

この元のgenuine H-factorizationにnᵢの正係数があれば、同じfactorizationからnᵢを一つ除いてq∈Γとなる。ゆえに

\[
\boxed{c-n_i\in H\ \Longrightarrow\ q+n_i\in\langle n_j,n_k\rangle.}
\]

c=W−q>0はHに属するのでD(c)は空でない。特にD(c)={i:c−nᵢ∈H}、SH(q)={i:q+nᵢ∈H}という規約なら∅≠D(c)⊆SH(q)。**等号は主張しない。** Hall型の存在定理、factorization uniqueness、generic connectivityは不要。

さらにc−m=F−qは正でΓに入らないためc∈𝒜。x=c−nᵢも𝒜に入る（x−m∈Γならc−m∈Γ）。y=q+nᵢ、h=q+mとすると

\[
h,c,x,y\in H\cap \mathcal A,\quad h+c=W+m,\quad x+y=W.
\]

この結論はsupport条件がある一方向ごとのもの。行の分類はG4で行う。

### C2.4 Tail gcd firewall

Qが空でないとする。q∈Qを一つ取るとq+m,W,c=W−qはいずれも𝒜⊆H。従って

\[
m=(q+m)+(W-q)-W\in\mathbb ZH.
\]

d=gcd(n₁,n₂,n₃)はmも割る。Γが数値半群なのでgcd(m,n₁,n₂,n₃)=1、よってd=1。

符号付き等式は整数群ℤHでのみ使用した。これを非負factorizationとは呼んでいない。

## C2.5 — 四行の選択とtailの極小性

反証仮定から異なる四つの \(q_1,q_2,q_3,q_4\in Q(\Gamma)\) を選べる。
上のApéry性・KEYは全Qに成立するため、選んだ四行にも同時に成立する。
もしtailのある生成元が残り二つの非負結合なら、Γのその生成元も冗長となり
edimΓ=4に反する。したがってtailの生成は極小である。
C2.4よりtailのgcdは1。よってHは真の極小3生成数値半群であり、対称／非対称に二分される。
