import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "測地線方程式と保存則" =>
%%%
file := "geodesic-equations"
tag := "ja-geodesic-equations"
%%%

測地線に沿って進むと、方位角は少しずつ変わっていきます。北東へ出発した測地線は、やがて真東を向き、そのあと南東へ向きを変えます。進むにつれて何もかもが変わっていくように見えますが、測地線の上でずっと変わらない量はないのでしょうか。

この章では、前の章の「曲がらない」という条件を緯度と経度の方程式に書き直し、そこから保存量を取り出します。ここでも主役は第1章の第一基本形式です。

# 測地線方程式
%%%
tag := "equations"
%%%

測地線の条件は、加速度と二つの接ベクトルの内積がどちらも 0 になることでした。この内積を第一基本形式の係数で計算すると、緯度と経度についての二本の微分方程式になります。ここで $`E' = dE/d\varphi`、$`G' = dG/d\varphi` です。係数が緯度だけで決まるので、微分するのも緯度についてだけで済みます。

$$`E \varphi'' + \tfrac{1}{2} E' \varphi'^2 - \tfrac{1}{2} G' \lambda'^2 = 0, \qquad G \lambda'' + G' \varphi' \lambda' = 0`

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_latitude_equation}

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_longitude_equation}

逆に、この二本の方程式を満たす曲線は測地線です。「曲がらない」という幾何の条件と、座標で書いた方程式が、ちょうど同じものを表しています。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesic_iff_equations}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Geodesic equations」）

微分幾何の教科書では、緯度の方程式を $`E` で割った形がクリストッフェル記号 $`\Gamma^\varphi_{\varphi\varphi} = E'/2E`、$`\Gamma^\varphi_{\lambda\lambda} = -G'/2E` を使って書かれます。見慣れない記号ですが、中身は第一基本形式の係数とその微分にすぎません。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_latitude_equation_christoffel}

# 経度の方程式は保存則だった
%%%
tag := "conservation"
%%%

二本目の方程式 $`G \lambda'' + G' \varphi' \lambda' = 0` をよく見ると、これは $`G \lambda'` を時間で微分したものです。

$$`\frac{d}{dt}\left(G \lambda'\right) = G' \varphi' \lambda' + G \lambda''`

方程式が言っているのは、$`G \lambda' = (N \cos \varphi)^2 \lambda'` が時間によらず一定だ、ということです。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut_G_mul_lon'}

この保存量はどこから来たのでしょうか。第一基本形式 $`M^2 d\varphi^2 + (N \cos \varphi)^2 d\lambda^2` の係数には、経度 $`\lambda` がまったく現れません。楕円体を地軸のまわりに回しても、形は変わらないからです。回転しても変わらないという対称性が、変わらない量を一つ生みます。物理で、回転対称な系では角運動量が保存されるのと同じ構造です。

# Clairaut の関係
%%%
tag := "clairaut"
%%%

保存量 $`(N \cos \varphi)^2 \lambda'` は、もっと見慣れた形に書き直せます。測地線の速さは一定でした（第6章）。方位角 $`A` の正弦は、東向きの成分 $`N \cos \varphi \cdot \lambda'` を速さで割ったものです。二つを組み合わせると、地軸からの距離 $`p = N \cos \varphi` と方位角 $`A` について

$$`p \sin A = \text{一定}`

が得られます。これが Clairaut の関係です。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.sinAzimuth_eq}

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Clairaut's relation」）

この関係から、測地線の振る舞いがかなりの程度まで読めます。$`\lvert \sin A \rvert \le 1` なので、$`p` はこの一定値より小さくなれません。極へ近づくと $`p` は小さくなるので、測地線は、ある緯度より高くは上がれないのです。その最高緯度で $`\lvert \sin A \rvert = 1`、つまり測地線は真東か真西を向き、そこから引き返します。冒頭の「北東へ出発した測地線が、やがて真東を向き、南東へ向きを変える」振る舞いは、この関係の帰結です。測地線を計算するソフトウェアは、この一定値を出発点での方位と緯度から求めて利用します。

# 緯線は測地線か
%%%
tag := "parallels"
%%%

北緯 45° の緯線に沿って、方位を真東に保って進むとします。方位角はずっと 90° で、地軸からの距離も一定なので、$`p \sin A` は一定です。速さも一定にできます。二つの保存則はどちらも満たされています。それでは、この緯線は測地線なのでしょうか。

答えは「いいえ」で、測地線になる緯線は赤道だけです。緯線に沿って進むとき、加速度は地軸の方を向いています。地軸は緯線の円の中心を通るので、赤道以外では、この加速度に子午線方向の成分が残ります。地表から見ると、緯線は極の側へ曲がり続けている道なのです。

{leanDecl Geodesy.ReferenceEllipsoid.parallelCurve_isGeodesic_iff}

保存則だけでは測地線を決めきれないのは、緯度が変化しない瞬間だけです。緯度が変化している場所では、二つの保存則から測地線方程式の両方が復元されます。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesicAt_of_conserved}

# 第I部のまとめと次へ
%%%
tag := "part-summary"
%%%

第I部では、地球の形を二つの数で決め（第1章）、そこから地表のものさしである第一基本形式を組み立てました。地図投影の歪みは、そのものさしと地図上の長さの比として測れました（第2章〜第5章）。最短経路は、そのものさしで測った長さとして定義され、ものさしの係数に経度が現れないという対称性から、Clairaut の保存則が出てきました（第6章、第7章）。どの章でも、出発点は同じ第一基本形式です。

第II部では、ここで平面に写した Web Mercator の正方形の世界を、今度は整数で切り分けます。タイル番号、quadkey、Morton code、Hilbert order に、どんな数学が潜んでいるのかを見ていきます。
