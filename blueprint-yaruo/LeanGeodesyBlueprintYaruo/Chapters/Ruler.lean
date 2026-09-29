import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第2章 地表のものさし" =>
%%%
file := "ruler"
tag := "by-ruler"
%%%

# 斜めの一歩
%%%
file := "diagonal"
tag := "by-diagonal"
%%%

:::yaruo
北へ一歩で $`M\,d\varphi`、東へ一歩で $`N\cos\varphi\,d\lambda`。北東に一歩なら、足せばいいお。
:::

:::yaranaio
北へ 3 m、東へ 4 m。どれだけ離れた。
:::

:::yaruo
7 m……じゃないお。5 m。三平方の定理だお。
:::

:::yaranaio
北と東が直角だからだ。じゃあ聞く。曲がった地球の表面で、北と東は本当に直角か。
:::

:::yaruo
……そんなの、確かめたことないお。
:::

:::yaranaio
確かめる方法がある。楕円体の上の点を、緯度と経度で決まる空間の点 $`r(\varphi, \lambda)` として置く。緯度だけを少し動かしたときに点が動く向き、それが北向きの矢印 $`\partial r/\partial\varphi` だ。経度だけなら東向きの矢印 $`\partial r/\partial\lambda`。どちらも地面に接している。
:::

:::yaruo
地面に貼りついた、二本の矢印だお。
:::

:::yaranaio
この二本の矢印だけで、どんな向きの一歩の長さも決まる。緯度を $`d\varphi`、経度を $`d\lambda` だけ動かしたときに地表を進む距離 $`ds` は
:::

$$`ds^2 = E\,d\varphi^2 + 2F\,d\varphi\,d\lambda + G\,d\lambda^2`

:::yaranaio
$`E` は北向きの矢印の長さの二乗、$`G` は東向きの矢印の長さの二乗、$`F` は二本の内積。二本がどれだけ斜めに交わっているかを表す。
:::

:::yaruo
$`F` がなければ、ただの三平方の定理だお。
:::

:::yaranaio
この式を*第一基本形式*と呼ぶ。座標で書いた一歩を、地表の長さに換える装置だ。*地表のものさし*と言ってもいい。
:::

# 楕円体のものさし
%%%
file := "ellipsoid-ruler"
tag := "by-ellipsoid-ruler"
%%%

:::yaruo
楕円体の $`E`、$`F`、$`G` は、どうやって計算するんだお。
:::

:::yaranaio
もう全部持っている。北向きの矢印の長さは $`M`、東向きは緯線の半径 $`N\cos\varphi`。そして Lean で内積を計算すると、二本の矢印の内積は、どの地点でも正確に 0 になる。
:::

:::yaruo
直角だったお……！
:::

:::yaranaio
だから
:::

$$`E = M^2, \qquad F = 0, \qquad G = (N\cos\varphi)^2`

$$`ds^2 = M^2\,d\varphi^2 + (N\cos\varphi)^2\,d\lambda^2`

:::yaruo
三平方の定理そのものだお。ただし、辺の長さが場所で変わる三平方の定理。
:::

:::kimatta
つまり、*地表の距離は、辺の長さが場所ごとに変わる三平方の定理*ということなんだよ。

美しい……
:::

:::yaruo
誰だお。
:::

:::yaranaio
気にするな。たまに出る。
:::

:::theorem "first_fundamental_form" (lean := "Geodesy.ReferenceEllipsoid.firstFormE_eq, Geodesy.ReferenceEllipsoid.firstFormF_eq, Geodesy.ReferenceEllipsoid.firstFormG_eq, Geodesy.ReferenceEllipsoid.norm_dr_sq")
緯度と経度を局所座標とする楕円体の*第一基本形式*は $`E = M^2`、$`F = 0`、$`G = (N\cos\varphi)^2` であり、座標の一歩 $`(d\varphi, d\lambda)` が地表で進む距離は $`ds^2 = M^2\,d\varphi^2 + (N\cos\varphi)^2\,d\lambda^2` である。係数は {uses "radii"}[] の二つの曲率半径である。
:::

:::proof "first_fundamental_form"
北向きと東向きの接ベクトルの長さはそれぞれ $`M` と $`N\cos\varphi`、内積は 0。接ベクトルの一次結合の長さを展開すると線素になる。
:::

# ものさしが全部を決める
%%%
file := "everything"
tag := "by-everything"
%%%

:::yaruo
長さが測れるようになったお。
:::

:::yaranaio
長さだけじゃない。二つの向きのなす角は、このものさしで測った内積を長さで割れば出る。面積は $`\sqrt{EG - F^2} = MN\cos\varphi` を積分すれば出る。曲線の長さは、一歩ずつ測って足し合わせれば出る。
:::

:::yaruo
長さも、角度も、面積も、全部このものさしから出るのかお。
:::

:::yaranaio
そうだ。これから先、地図を作るときも、最短の道を探すときも、戻ってくるのは必ずこの一本の式だ。
:::

:::yaruo
地表はもう測れるお。じゃあ、これを平面に広げたら？ 地図なら、定規で測れるお。
:::

:::yaranaio
やってみるか。惑星を、平面に押しつぶす。
:::
