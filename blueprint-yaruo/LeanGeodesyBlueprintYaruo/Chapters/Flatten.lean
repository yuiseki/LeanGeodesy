import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第3章 平面への亡命" =>
%%%
file := "flatten"
tag := "by-flatten"
%%%

# 破れないオレンジの皮
%%%
file := "orange"
tag := "by-orange"
%%%

:::yaruo
地図にすれば、全部定規で測れるお。
:::

:::yaranaio
オレンジの皮を、破らず、伸ばさず、しわも作らずに、机に平らに広げてみろ。
:::

:::yaruo
無理だお。どこかが破れるか、伸びるお。
:::

:::yaranaio
惑星も同じだ。曲がった面を平面に写すと、必ずどこかが伸び縮みする。地図の縮尺が画面のどこでも同じ、という地図は存在しない。
:::

:::yaruo
じゃあ、せめて、どこがどれだけ伸びたかを知りたいお。
:::

:::yaranaio
それがこの章の仕事だ。伸び縮みを、数にする。
:::

# 地表の一歩と、地図の一歩
%%%
file := "two-steps"
tag := "by-two-steps"
%%%

:::yaranaio
地図投影は、緯度経度 $`(\varphi, \lambda)` を平面の点 $`(x, y)` に写す関数だ。緯度だけを少し動かせば、地図の上の点も少し動く。その動きのベクトルを `dLat` と呼ぶ。経度だけなら `dLon`。
:::

:::yaruo
さっきの地面の矢印と同じだお。今度は、地図に貼りついた矢印だお。
:::

:::yaranaio
地表の一歩の長さは、ものさしで測れる。北へ $`M`、東へ $`N\cos\varphi`。地図の一歩の長さは、定規で測れる。比べればいい。
:::

$$`h = \frac{\lVert \mathtt{dLat} \rVert}{M}, \qquad k = \frac{\lVert \mathtt{dLon} \rVert}{N\cos\varphi}`

:::yaranaio
$`h` が*子午線方向の縮尺*、$`k` が*緯線方向の縮尺*。地表の 1 m が、地図で何 m に描かれるかだ。
:::

:::yaruo
面積はどうなるんだお。
:::

:::yaranaio
地表の小さな長方形の面積 $`MN\cos\varphi\,d\varphi\,d\lambda` と、地図の上で `dLat` と `dLon` が張る平行四辺形の面積の比。それが*面積の縮尺*だ。この四つをまとめたものを*局所歪み*と呼ぶ。
:::

:::yaruo
地表に小さな円を描いて、地図に写したら……
:::

:::yaranaio
`dLat` と `dLon` が直交していれば、半軸 $`h` と $`k` の楕円になる。*ティソーの指示楕円*。地図の歪みは、円がどんな楕円に化けるかで、一目で分かる。
:::

:::definition "local_distortion" (lean := "Geodesy.Projection.LocalDistortion, Geodesy.Projection.LocalDistortion.ofEllipsoid, Geodesy.Projection.LocalDistortion.tissot")
地図投影の*局所歪み*は、地表の基準の長さ $`M`、$`N\cos\varphi` と、地図上の偏微分ベクトル `dLat`、`dLon` の組である。*子午線方向の縮尺* $`h`、*緯線方向の縮尺* $`k`、*面積の縮尺*はその比として決まり、`dLat` と `dLon` が直交するとき地表の小円は半軸 $`h`、$`k` の楕円に描かれる。基準の長さは {uses "first_fundamental_form"}[] の $`\sqrt{E}` と $`\sqrt{G}` である。
:::

# 形を守るということ
%%%
file := "conformal"
tag := "by-conformal"
%%%

:::yaruo
円が円のまま描かれる地図なら、形が崩れないお。
:::

:::yaranaio
それを*等角*と呼ぶ。交差点の角度も、海岸線の曲がり方も、地図の上で同じ角度になる。条件は二つ。`dLat` と `dLon` が直交していること。そして $`h = k`。
:::

:::yaruo
二つも条件があるのかお。
:::

:::yaranaio
第一基本形式で言い直すと、一つにまとまる。等角な地図では、どんな向きの一歩についても
:::

$$`(\text{地図上の長さ})^2 = h^2 \times ds^2`

:::yaruo
地表のものさしを、そのまま $`h^2` 倍してるだけだお。
:::

:::yaranaio
場所ごとに倍率は違っていい。ただ、その場所ではどの向きにも同じ倍率をかける。角度は内積の比だから、ものさし全体を何倍にしても変わらない。
:::

:::kimatta
つまり、*等角は第一基本形式のスカラー倍*ということなんだよ。

美しい……
:::

:::theorem "conformal_first_form" (lean := "Geodesy.Projection.LocalDistortion.isConformal_iff, Geodesy.Projection.isConformal_iff_firstForm")
地図投影が*等角*であること、すなわち `dLat` と `dLon` が直交し $`h = k` であることは、任意の一歩について地図上の長さの二乗が第一基本形式の $`h^2` 倍に等しいことと同値である。等角性は {uses "local_distortion"}[] の性質として定まる。
:::

:::proof "conformal_first_form"
一歩 $`v = (d\varphi, d\lambda)` の像は $`d\varphi\,\mathtt{dLat} + d\lambda\,\mathtt{dLon}`。その長さの二乗を展開し、第一基本形式 $`M^2 d\varphi^2 + (N\cos\varphi)^2 d\lambda^2` と係数を比べる。
:::

# 代償
%%%
file := "price"
tag := "by-price"
%%%

:::yaruo
等角で、しかも面積も守れば、完璧な地図だお。
:::

:::yaranaio
等角な地図の面積の縮尺は、いくつになる。
:::

:::yaruo
縦に $`h` 倍、横に $`h` 倍だから、$`h^2`……
:::

:::yaranaio
面積を守るには $`h = 1`、どこでも縮尺 1。それはオレンジの皮を伸ばさずに広げるのと同じで、不可能だ。形を守れば、面積が壊れる。
:::

:::yaruo
何かを守ると、何かが壊れる……。
:::

:::yaranaio
それが地図投影の宿命だ。そしてその宿命を、四百年前に一人の地図職人が真正面から引き受けた。
:::
