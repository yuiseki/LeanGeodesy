import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl
import LeanGeodesyBookYaruo.Dialogue
import LeanGeodesyBookYaruo.Figure

open Verso.Genre Manual
open LeanGeodesyManualJa LeanGeodesyBookYaruo

#doc (Manual) "第2部 地球を無理やり平らにする" =>
%%%
file := "flatten"
tag := "ja-story-flatten"
%%%

「じゃあ、地図にすれば距離は簡単になる？」という問いから始めます。

# 地図の縮尺は一つではない
%%%
file := "scale-bar"
tag := "s2-scale-bar"
%%%

:::yaruo
地球の上で測るのは面倒だお。地図にしてしまえば、あとは定規で測るだけだお。地理院地図にも縮尺バーが付いてるお。
:::

:::yaranaio
Web 地図で北海道から沖縄までスクロールしながら、縮尺バーを見ていたことはあるか。
:::

:::yaruo
……そういえば、場所を動かすとバーの長さが変わるお。バグかと思ってたお。
:::

:::yaranaio
バグじゃない。Web 地図では、ズームレベル $`z` の 1 ピクセルが地表の何 m に当たるかが、緯度で変わる。
:::

$$`\text{1 ピクセルの地上距離} = \frac{2\pi a \cos \varphi}{256 \cdot 2^z}`

:::yaranaio
$`\cos \varphi` が付いているだろ。北へ行くほど、同じ 1 ピクセルが表す距離が短くなる。だから縮尺バーは、画面の中央の緯度に合わせて描き直されている。
:::

{leanDecl Geodesy.Projection.groundResolution_eq}

:::yaruo
じゃあ、縮尺が場所で変わらない、ちゃんとした地図を作ればいいお。
:::

:::yaranaio
みかんの皮を、破らず、伸ばさず、しわも作らずに机の上に平らに広げられるか。
:::

:::yaruo
無理だお。どこかが破れるか伸びるお。
:::

:::yaranaio
地球も同じだ。曲がった面を平面に写すと、どこかが必ず伸び縮みする。これは作図の腕の問題じゃなくて、曲面と平面の性質の違いから来る、避けられないことだ。
:::

:::yaruo
避けられないなら、どれくらい伸び縮みしているかを知りたいお。
:::

:::yaranaio
それがこの部の目標だ。伸び縮みを、ちゃんと数で測れるようにする。
:::

# 地表の一歩と地図の一歩
%%%
file := "two-steps"
tag := "s2-two-steps"
%%%

:::yaruo
伸び縮みを測るって、何と何を比べればいいんだお。
:::

:::yaranaio
地表の一歩と、それが地図に描かれた一歩だ。地表の一歩の長さは、第1部のものさしで測れるようになった。北へ $`d\varphi` なら $`M\,d\varphi`、東へ $`d\lambda` なら $`N \cos \varphi\,d\lambda` だったな。
:::

:::yaruo
地図の側は、その一歩が地図の上で何ミリになるかを測ればいいお。
:::

:::yaranaio
そう。地図投影は、緯度経度 $`(\varphi, \lambda)` を平面の点 $`(x, y)` に写す関数だ。緯度だけを少し動かすと、地図の上の点も少し動く。その動きの向きと大きさを表すベクトルが、投影を緯度で偏微分したものだ。ここでは `dLat` と呼ぼう。経度で偏微分したものは `dLon` だ。
:::

:::yaruo
さっきの $`\partial r/\partial\varphi` と同じ考え方だお。あっちは地表の一歩、こっちは地図の一歩だお。
:::

:::yaranaio
いい読み方だ。偏微分を並べた行列をヤコビ行列と呼ぶが、要するに「座標を少し動かしたら、写った先がどう動くか」の表だ。
:::

:::yaranaio
あとは比を取るだけだ。
:::

$$`h = \frac{\lVert \mathtt{dLat} \rVert}{M}, \qquad k = \frac{\lVert \mathtt{dLon} \rVert}{N \cos \varphi}`

:::yaranaio
$`h` は子午線方向の縮尺、$`k` は緯線方向の縮尺だ。地表の 1 m が、地図の上で何 m として描かれるかを表す。どちらも 1 なら、その方向では伸び縮みしていない。
:::

:::yaruo
面積はどうなるんだお。
:::

:::yaranaio
地表の小さな長方形の面積は $`M \cdot N \cos \varphi\,d\varphi\,d\lambda` だ。地図の上では、`dLat` と `dLon` が張る平行四辺形になる。その面積の比が面積の縮尺だ。
:::

$$`\text{面積の縮尺} = \frac{\lvert \det(\mathtt{dLat}, \mathtt{dLon}) \rvert}{M \cdot N \cos \varphi}`

:::yaruo
$`\det` は平行四辺形の面積を出す行列式だお。それは大学で習ったお。
:::

:::yaranaio
LeanGeodesy では、地表の基準の長さ二つと、地図上の二つのベクトルを組にして、局所歪みという構造にしている。楕円体の上で測るときは、基準の長さを第一基本形式の $`\sqrt{E} = M` と $`\sqrt{G} = N \cos \varphi` に取る。
:::

{leanDecl Geodesy.Projection.LocalDistortion}

{leanDecl Geodesy.Projection.LocalDistortion.ofEllipsoid}

:::yaruo
第1部のものさしが、そのまま地図の歪みを測る物差しになってるお。
:::

:::yaranaio
そうだ。第一基本形式は、地図を測るためにも必要だったというわけだ。
:::

# 小さな円は楕円になる
%%%
file := "tissot"
tag := "s2-tissot"
%%%

:::yaruo
$`h` と $`k` があるのは分かったお。でも数字が二つあるだけだと、何が起きてるのか想像しにくいお。
:::

:::yaranaio
地表に、半径 1 m の小さな円を描いたとする。それを地図に写すと、どんな形になると思う。
:::

:::yaruo
$`h` と $`k` が違うなら、縦と横で伸び方が違うから……楕円だお。
:::

:::figure (src := "figures/tissot.svg") (alt := "左に地表の小さな円（北向き・東向きの半径 1）、右に地図投影後の楕円（子午線方向の半軸 h、緯線方向の半軸 k）。") (width := "520px")
局所歪みとは、地表の小さな円が地図上でどんな楕円になるかを見ること：子午線方向に $`h` 倍、緯線方向に $`k` 倍
:::

:::yaranaio
正解だ。`dLat` と `dLon` が直交していれば、地表の小さな円は、半軸が $`h` と $`k` の楕円に描かれる。これをティソーの指示楕円と呼ぶ。図法の本で、地図の上に小さな楕円がずらっと並んでいる図を見たことがないか。
:::

:::yaruo
あるお。あれはこういう意味だったのかお。
:::

{leanDecl Geodesy.Projection.LocalDistortion.tissot}

:::yaranaio
楕円の形で、その地点の歪みが一目で分かる。円のままなら形は崩れていない。円の大きさが変われば面積が変わっている。
:::

# 角度を守るということ
%%%
file := "conformal"
tag := "s2-conformal"
%%%

:::yaruo
じゃあ、指示楕円がずっと円のままの地図があれば最高だお。形が崩れないお。
:::

:::yaranaio
形が崩れない、というのを正確に言うとどうなる。
:::

:::yaruo
……交差点の角度が、地図の上でも同じ角度になることだお。
:::

:::yaranaio
それを等角と呼ぶ。どの方向の一歩も同じ倍率で伸び縮みすれば、方向どうしの角度は変わらない。局所歪みの言葉で言うと、`dLat` と `dLon` が直交していて、しかも $`h = k` であることだ。
:::

{leanDecl Geodesy.Projection.LocalDistortion.isConformal_iff}

:::yaruo
直交と $`h = k`。条件が二つあるお。
:::

:::yaranaio
第一基本形式を使うと、一つにまとまる。等角な地図では、どんな向きの一歩についても、地図上の長さの二乗が、地表の長さの二乗のちょうど $`h^2` 倍になる。
:::

$$`(\text{地図上の長さ})^2 = h^2 \times (\text{第一基本形式で測った地表の長さ})^2`

:::yaruo
ものさし全体を $`h^2` 倍しているだけ、ってことかお。
:::

:::yaranaio
そうだ。場所ごとに倍率は違っていいが、その場所では、どの向きにも同じ倍率をかける。角度は二つのベクトルの内積を長さで割ったものだから、ものさし全体を同じ数倍しても変わらない。等角とは、第一基本形式をスカラー倍で保つことなんだ。
:::

:::yaruo
それも証明されてるのかお。
:::

:::yaranaio
ここまで話した二つの言い方が同値だ、という定理がある。
:::

{leanDecl Geodesy.Projection.isConformal_iff_firstForm}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Conformal iff it scales the first fundamental form」）

# 何かを守れば、何かが壊れる
%%%
file := "tradeoff"
tag := "s2-tradeoff"
%%%

:::yaruo
等角な地図なら形が崩れないお。面積もついでに守れば完璧だお。
:::

:::yaranaio
等角な地図の面積の縮尺はいくつになると思う。
:::

:::yaruo
縦に $`h` 倍、横に $`h` 倍だから……$`h^2` だお。
:::

{leanDecl Geodesy.Projection.LocalDistortion.areaScale_of_isConformal}

:::yaranaio
そうだ。面積を守るには $`h = 1`、つまりどこでも縮尺 1 でないといけない。それは、みかんの皮を伸ばさずに平らにするのと同じで、できない。
:::

:::yaruo
じゃあ等角な地図は、場所によって面積がでたらめなのかお。
:::

:::yaranaio
でたらめではなく、$`h^2` 倍という決まった歪み方をする。何かを守れば、そのぶん別の何かが壊れる。地図投影の中心にあるのはこの問題だ。どれを守るかを選ぶのが、図法を選ぶということなんだ。
:::

:::yaruo
Web 地図は形が崩れてないから、角度を守ってるんだお。Mercator っていう名前だった気がするお。
:::

:::yaranaio
次はその Mercator の話だ。あの式を覚えている必要はない。「等角にしろ」という条件を置くだけで、式のほうから出てくる。
:::
