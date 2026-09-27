import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "保存するものと壊すもの" =>
%%%
file := "tradeoffs"
tag := "ja-tradeoffs"
%%%

結局、どの図法を使えばよいのでしょうか。GIS で投影法を選ぶとき、この問いには一つの答えがありません。答えは「何を測りたいか」で決まります。この章では、ここまでの図法が何を守り、何を壊すのかを並べ、その選択が数学的にどう縛られているかを見ます。

# 一覧
%%%
tag := "table"
%%%

特に断らない限り、球の上での性質です。

- Mercator：角度を守る。面積は $`\sec^2 \varphi` 倍に拡大し、距離の縮尺は $`\sec \varphi`（北緯 60° で 2 倍）。
- Web Mercator：楕円体の上では角度を厳密には守らず、面積はすべての緯度で拡大する。
- Lambert 正積円筒図法：面積を守る（局所でも、セル単位でも）。赤道以外では角度を壊し、縮尺は子午線方向 $`\cos \varphi`、緯線方向 $`\sec \varphi`。
- 正距円筒図法：子午線方向の距離を守る。赤道以外では角度を壊し、面積は $`\sec \varphi` 倍。
- 正距方位図法：中心からの距離と方位を守る。極以外では角度を壊し、バッファの面積を拡大する。
- 横メルカトル図法：角度を守る。縮尺が 1 なのは中央経線の上だけで、離れるほど面積が拡大する。

どの項目も、ここまでの章で証明された定理に対応しています。

# 選択を縛っている定理
%%%
tag := "constraints"
%%%

この一覧は経験則の寄せ集めではありません。円筒図法については、何を守るかを決めた時点で図法そのものが決まってしまうことが証明されています。等角なら Mercator、正積なら Lambert です。

{leanDecl Geodesy.Projection.eq_mercatorY_of_isConformal}

{leanDecl Geodesy.Projection.eq_sin_of_isEqualArea}

そして、二つを同時に満たせるのは赤道だけです。

{leanDecl Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea}

正距円筒図法（plate carrée、緯度経度をそのまま $`x, y` にする図法）は、どちらも守らない代わりに、子午線方向の距離を守ります。

{leanDecl Geodesy.Projection.plateCarree_h}

# 縮尺 1 の帯を選ぶ：横メルカトルと UTM
%%%
tag := "utm"
%%%

Mercator は赤道では縮尺 1 で、赤道から離れるほど縮尺が大きくなります。それなら球を 90° 回して、好きな経線を「赤道」の位置に持ってくればよいのではないか。これが横メルカトル図法で、UTM や日本の平面直角座標系の基礎です。等角性はそのまま保たれ、今度は中央経線の上で縮尺が 1 になります。

{leanDecl Geodesy.Projection.tm_isConformal}

{leanDecl Geodesy.Projection.tmScale_central}

UTM は幅 6° の帯ごとに横メルカトル図法を使い、全体に 0.9996 をかけます。こうすると中央経線ではわずかに縮み、その両側の二本の線で縮尺がちょうど 1 になります。球の上では、帯全体で縮尺が $`[0.9996, 1.00098)` に収まり、格子上の距離は球面上の距離と 0.1 % 以内で一致します。

{leanDecl Geodesy.Projection.utmScale_bounds}

ここに図法選びの考え方が表れています。歪みを消すことはできないので、測りたい量を守る図法を選び、そのうえで歪みが小さく済む範囲だけを使うのです。

ここまでは地表を平面へ写しました。次は逆に、地表そのものの上で最短経路を考えます。
