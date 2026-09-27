import VersoManual
import LeanGeodesyManualJa.Part1

open Verso.Genre Manual

#doc (Manual) "LeanGeodesy（日本語版）" =>
%%%
shortTitle := "LeanGeodesy 日本語版"
tag := "ja-top"
%%%

LeanGeodesy は、GIS ソフトウェアが前提にしている数学を Lean 4 で証明するライブラリです。この本は、そのライブラリを API の一覧としてではなく、いくつかの大きな問いへの答えとして読むためのものです。英語版の翻訳ではなく、同じ Lean の宣言を参照しながら、日本語で独立に書いています。

各節は、GIS で実際に出会う疑問から始まります。直感的な説明のあとで必要な数学を導入し、最後に、その主張が LeanGeodesy のどの定理として証明されているかを示します。定理の名前と型（signature）は、ビルドしたライブラリから取り込んだもので、手で書き写してはいません。証明の細部より、定理どうしがどうつながっているかを追うことに重きを置いています。

各章の要所には、依存関係を Lean Atlas で見るためのリンクがあります。Atlas で主定理を選ぶと、いま読んだ概念が形式的にどんな依存関係になっているのかを確かめられます。

いまは第I部「地球を測り、平面に写す」まであります。タイル番号の数学（第II部）と座標参照系（第III部）は、今後追加する予定です。

用語は次の表記で統一します。Lean の識別子は翻訳しません。

- reference ellipsoid：参照楕円体
- meridian radius of curvature：子午線曲率半径
- prime vertical radius of curvature：卯酉線曲率半径
- first fundamental form：第一基本形式
- local distortion：局所歪み
- map projection：地図投影
- conformal：等角
- geodesic：測地線

{include 1 LeanGeodesyManualJa.Part1}
