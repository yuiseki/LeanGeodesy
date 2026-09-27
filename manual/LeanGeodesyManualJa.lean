import VersoManual
import LeanGeodesyManualJa.ProjectionSpine

open Verso.Genre Manual

#doc (Manual) "LeanGeodesy（日本語版）" =>
%%%
shortTitle := "LeanGeodesy 日本語版"
%%%

LeanGeodesy は、GIS ソフトウェアが前提にしている数学を Lean 4 で証明するライブラリです。この日本語版は英語版の翻訳ではなく、同じ Lean の宣言を参照しながら、数学的な構造を日本語で理解するための独立した読み物です。

いまは試作として、第一基本形式から局所歪みを経て Mercator 図法の等角性に至る一本の筋だけを扱います。本文に出てくる定理の名前と型（signature）は、ビルドしたライブラリから取り込んだもので、手で書き写してはいません。

用語は次の表記で統一します。Lean の識別子は翻訳しません。

- reference ellipsoid：参照楕円体
- meridian radius of curvature：子午線曲率半径
- prime vertical radius of curvature：卯酉線曲率半径
- first fundamental form：第一基本形式
- local distortion：局所歪み
- map projection：地図投影
- conformal：等角
- geodesic：測地線

{include 1 LeanGeodesyManualJa.ProjectionSpine}
