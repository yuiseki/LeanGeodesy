import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "隣どうしを隣に並べる：Hilbert 順序" =>
%%%
file := "hilbert"
tag := "ja-hilbert"
%%%

番号が一つ違うタイルは、地図の上でも必ず辺を共有している。そんな並べ方があれば、番号の近さが地図の近さを保証してくれます。Hilbert 曲線はまさにそういう並べ方で、空間インデックスでよく使われます。この章では、LeanGeodesy が有限のタイル格子の上で Hilbert 順序をどう構成し、何を証明しているかを見ます。

# 四つの象限に、向きを変えて並べる
%%%
tag := "t-construction"
%%%

Hilbert 順序も、Morton 順序と同じく再帰的に作ります。ズーム $`z + 1` の番号 $`i` を、最上位の 4 進数の桁 $`q = \lfloor i/4^z \rfloor` と残り $`r = i \bmod 4^z` に分けます。$`q` はどの象限に入るかを、$`r` はその象限の中でズーム $`z` の曲線の何番目かを表します。

Morton との違いは、象限ごとにズーム $`z` の曲線の向きを変えて置くことです。$`q = 0` の象限（$`x` も $`y` も小さい側）には曲線を転置して置き、$`q = 3` の象限（$`x` が大きく $`y` が小さい側）には反転と転置を組み合わせて置きます。$`q = 1` と $`q = 2` の象限には、そのまま平行移動して置きます。

{leanDecl Geodesy.Tiles.quadPlace}

{leanDecl Geodesy.Tiles.hilbertD}

# 始点と終点が曲線をつなぐ
%%%
tag := "t-endpoints"
%%%

向きを変える理由は、曲線の端と端をつなぐためです。どのズームでも、Hilbert 曲線は $`(0, 0)` から出発し、$`(2^z - 1, 0)` で終わります。始点と終点が、同じ辺の両端にあるのです。

{leanDecl Geodesy.Tiles.hilbertD_zero}

{leanDecl Geodesy.Tiles.hilbertD_last}

この性質が、次のズームの曲線をつなぎ合わせる鍵になります。象限ごとの向きの変え方は、ある象限の曲線の終点が、次の象限の曲線の始点と辺を共有するように選ばれています。そのため、どのズームでも、番号が一つ違うタイルは必ず隣り合います。

{leanDecl Geodesy.Tiles.hilbert_adjacent}

一つの不変量（始点と終点の位置）を保つことで、局所的な性質（隣接）が全体で成り立つ。帰納法による証明の典型的な形です。

# すべてのタイルをちょうど一度ずつ
%%%
tag := "t-bijection"
%%%

Hilbert 曲線は、すべてのタイルをちょうど一度ずつ訪れます。番号からタイルへの写像と、タイルから番号への写像は、互いに逆写像です。

{leanDecl Geodesy.Tiles.hilbertEquiv}

タイルから番号を求める写像 `encode` は、象限を読み取り、その象限の向きの変換を元に戻すことを再帰的に繰り返して計算します。この写像は計算可能で、選択公理を使っていません。公理の監査で、`propext` と `Quot.sound` だけに依存していることが確かめられています。証明されたアルゴリズムが、そのまま実行できるプログラムでもあるということです。

{leanDecl Geodesy.Tiles.encode}

# Hilbert 順序も四分木に沿っている
%%%
tag := "t-hilbert-nested"
%%%

Hilbert 順序は向きを変えながら並べるので、Morton 順序のように四分木に沿った構造は失われているように見えます。ところが、そうではありません。ズーム $`z + 1` で $`i` 番目に訪れるタイルの親は、ズーム $`z` で $`\lfloor i/4 \rfloor` 番目に訪れるタイルです。番号 $`4k`〜$`4k + 3` の四枚は、ちょうど番号 $`k` のタイルの四つの子です。

{leanDecl Geodesy.Tiles.parent_hilbert_decode}

番号を 4 で割ると親の番号になる。この性質は Morton 順序と Hilbert 順序に共通しています。次の章では、この一つの性質だけから、空間インデックスとして使うのに必要なことがすべて出てくることを見ます。
