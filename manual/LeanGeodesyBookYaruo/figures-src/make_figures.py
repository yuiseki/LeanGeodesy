"""Generate the SVG figures of the dialogue book into ../figures/.

Run from this directory: python3 make_figures.py

All figures share one visual language: a light, quiet body; the quantity
being explained drawn in blue (solid) or orange (dashed), so line style and
labels carry the meaning as well as colour; math symbols in italic serif, as
in the text; as little Japanese as possible.
"""

import math
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "figures"

INK = "#1f2937"
MUTED = "#6b7280"
BODY_FILL = "#f3f4f6"
BODY_STROKE = "#9ca3af"
BLUE = "#1d4ed8"
ORANGE = "#c2410c"

STYLE = f"""
<style>
  .body {{ fill: {BODY_FILL}; stroke: {BODY_STROKE}; stroke-width: 1.5; }}
  .aux {{ fill: none; stroke: {MUTED}; stroke-width: 1.2; stroke-dasharray: 5 4; }}
  .ink {{ fill: none; stroke: {INK}; stroke-width: 1.6; }}
  .blue {{ fill: none; stroke: {BLUE}; stroke-width: 2.4; }}
  .orange {{ fill: none; stroke: {ORANGE}; stroke-width: 2.4; stroke-dasharray: 8 5; }}
  .dot {{ fill: {INK}; }}
  .math {{ font-family: "Times New Roman", "STIX Two Text", "Cambria Math", serif; font-style: italic; font-size: 20px; fill: {INK}; }}
  .math.blue-t {{ fill: {BLUE}; }}
  .math.orange-t {{ fill: {ORANGE}; }}
  .up {{ font-style: normal; }}
  .ja {{ font-family: "Hiragino Sans", "Yu Gothic", "Noto Sans JP", "Noto Sans CJK JP", sans-serif; font-size: 15px; font-style: normal; fill: {INK}; }}
  .ja.muted {{ fill: {MUTED}; font-size: 13px; }}
  .ja.blue-t {{ fill: {BLUE}; }}
  .ja.orange-t {{ fill: {ORANGE}; }}
</style>
"""


def defs():
    """Arrowheads in the three colours."""
    out = ["<defs>"]
    for name, colour in [("ink", INK), ("blue", BLUE), ("orange", ORANGE), ("muted", MUTED)]:
        out.append(
            f'<marker id="arrow-{name}" viewBox="0 0 10 10" refX="9" refY="5" '
            f'markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
            f'<path d="M0,0 L10,5 L0,10 z" fill="{colour}"/></marker>'
        )
    out.append("</defs>")
    return "\n".join(out)


def svg(width, height, title, body):
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'width="{width}" height="{height}" role="img">\n'
        f"<title>{title}</title>\n{STYLE}\n{defs()}\n{body}\n</svg>\n"
    )


def line(x1, y1, x2, y2, cls="ink", arrow=None, start_arrow=None):
    a = f' marker-end="url(#arrow-{arrow})"' if arrow else ""
    s = f' marker-start="url(#arrow-{start_arrow})"' if start_arrow else ""
    return f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" class="{cls}"{a}{s}/>'


def text(x, y, s, cls="math", anchor="middle"):
    return f'<text x="{x:.1f}" y="{y:.1f}" class="{cls}" text-anchor="{anchor}">{s}</text>'


def arc(cx, cy, r, a0, a1, cls="ink"):
    """Arc of the circle (cx, cy, r) from angle a0 to a1 (degrees, counterclockwise, y up)."""
    x0, y0 = cx + r * math.cos(math.radians(a0)), cy - r * math.sin(math.radians(a0))
    x1, y1 = cx + r * math.cos(math.radians(a1)), cy - r * math.sin(math.radians(a1))
    large = 1 if abs(a1 - a0) > 180 else 0
    sweep = 0 if a1 > a0 else 1
    return f'<path d="M{x0:.1f},{y0:.1f} A{r:.1f},{r:.1f} 0 {large} {sweep} {x1:.1f},{y1:.1f}" class="{cls}"/>'


def right_angle(px, py, ux, uy, vx, vy, size=11, cls="ink"):
    """Right-angle mark at P between unit directions u and v (screen coordinates)."""
    a = (px + ux * size, py + uy * size)
    b = (px + ux * size + vx * size, py + uy * size + vy * size)
    c = (px + vx * size, py + vy * size)
    return f'<path d="M{a[0]:.1f},{a[1]:.1f} L{b[0]:.1f},{b[1]:.1f} L{c[0]:.1f},{c[1]:.1f}" class="{cls}" stroke-width="1.2"/>'


def sphere():
    cx, cy, r = 180, 150, 110
    body = [
        f'<circle cx="{cx}" cy="{cy}" r="{r}" class="body"/>',
        f'<circle cx="{cx}" cy="{cy}" r="3.5" class="dot"/>',
        text(cx - 14, cy + 22, "O"),
        line(cx, cy, cx + r, cy, "blue", arrow="blue"),
        text(cx + r / 2, cy - 12, "R", "math blue-t"),
        text(cx, cy + r + 34, '<tspan class="math">R</tspan><tspan class="ja"> = 6371 km</tspan>', "math"),
    ]
    return svg(360, 300, "半径 R の球の断面", "\n".join(body))


def ellipsoid():
    cx, cy, a, b = 210, 170, 160, 110
    body = [
        line(cx, cy - b - 36, cx, cy + b + 30, "aux"),
        text(cx + 8, cy - b - 42, "地軸", "ja muted", anchor="start"),
        line(cx - a - 20, cy, cx + a + 20, cy, "aux"),
        f'<ellipse cx="{cx}" cy="{cy}" rx="{a}" ry="{b}" class="body"/>',
        f'<circle cx="{cx}" cy="{cy}" r="3.5" class="dot"/>',
        text(cx - 14, cy + 22, "O"),
        line(cx, cy, cx + a, cy, "blue", arrow="blue"),
        text(cx + a / 2, cy - 12, "a", "math blue-t"),
        line(cx, cy, cx, cy - b, "orange", arrow="orange"),
        text(cx - 16, cy - b / 2 + 6, "b", "math orange-t"),
        text(cx + a - 4, cy + 22, "赤道", "ja muted", anchor="end"),
        # Formula and WGS 84 values on the right.
        text(cx, cy + b + 60, '<tspan class="math">f</tspan><tspan class="math up"> = (</tspan><tspan class="math blue-t">a</tspan>'
             '<tspan class="math up"> − </tspan><tspan class="math orange-t">b</tspan><tspan class="math up">) / </tspan>'
             '<tspan class="math blue-t">a</tspan>', "math"),
        text(cx, cy + b + 92, '<tspan class="ja">WGS 84：</tspan><tspan class="math">a</tspan><tspan class="ja"> = 6378137 m、</tspan>'
             '<tspan class="math up">1/</tspan><tspan class="math">f</tspan><tspan class="ja"> = 298.257223563</tspan>', "math"),
        text(cx, cy + b + 120, "扁平率は説明のため誇張", "ja muted"),
    ]
    return svg(440, 420, "赤道半径 a と極半径 b の回転楕円体の断面", "\n".join(body))


def ellipse_point(a, b, phi):
    """Point at geodetic latitude phi on the ellipse x²/a² + y²/b² = 1 (y up), with N."""
    e2 = 1 - (b / a) ** 2
    n = a / math.sqrt(1 - e2 * math.sin(phi) ** 2)
    return n * math.cos(phi), n * (1 - e2) * math.sin(phi), n, e2


def latitude():
    cx, cy, a, b = 230, 230, 190, 120
    phi = math.radians(42)
    px, py, n, e2 = ellipse_point(a, b, phi)
    psi = math.atan2(py, px)
    qx = n * e2 * math.cos(phi)  # where the normal meets the equatorial plane
    sx = lambda x: cx + x
    sy = lambda y: cy - y
    # Tangent direction at P (unit, math coordinates) and normal (outward).
    tx, ty = -math.sin(phi), math.cos(phi)
    nx, ny = math.cos(phi), math.sin(phi)
    body = [
        line(sx(-a - 20), sy(0), sx(a + 30), sy(0), "aux"),
        text(sx(a + 34), sy(0) + 5, "赤道面", "ja muted", anchor="start"),
        line(sx(0), sy(-b - 20), sx(0), sy(b + 30), "aux"),
        f'<ellipse cx="{cx}" cy="{cy}" rx="{a}" ry="{b}" class="body"/>',
        # Tangent line at P, for the right angle.
        line(sx(px - 70 * tx), sy(py - 70 * ty), sx(px + 70 * tx), sy(py + 70 * ty), "aux"),
        # O to P: geocentric latitude.
        line(sx(0), sy(0), sx(px), sy(py), "orange"),
        # Normal through P, from the equatorial plane outward.
        line(sx(qx), sy(0), sx(px + 60 * nx), sy(py + 60 * ny), "blue"),
        right_angle(sx(px), sy(py), -nx, ny, tx, -ty, size=12),
        arc(sx(0), sy(0), 58, 0, math.degrees(psi), "orange"),
        text(sx(0) + 74 * math.cos(psi / 2), sy(0) - 74 * math.sin(psi / 2) + 7, "ψ", "math orange-t"),
        arc(sx(qx), sy(0), 44, 0, math.degrees(phi), "blue"),
        text(sx(qx) + 60 * math.cos(phi / 2), sy(0) - 60 * math.sin(phi / 2) + 7, "φ", "math blue-t"),
        f'<circle cx="{sx(qx):.1f}" cy="{sy(0):.1f}" r="3" fill="{BLUE}"/>',
        f'<circle cx="{sx(0)}" cy="{sy(0)}" r="3.5" class="dot"/>',
        text(sx(0) - 14, sy(0) + 22, "O"),
        f'<circle cx="{sx(px):.1f}" cy="{sy(py):.1f}" r="4" class="dot"/>',
        text(sx(px) + 10, sy(py) + 22, "P", anchor="start"),
        text(sx(px + 60 * nx) + 6, sy(py + 60 * ny) - 6, "法線", "ja blue-t", anchor="start"),
        text(sx(px * 0.55) - 4, sy(py * 0.55) - 12, "OP", "math orange-t", anchor="end"),
    ]
    return svg(560, 400, "楕円体の点 P における測地緯度 φ と地心緯度 ψ", "\n".join(body))


def radii():
    cx, cy, a, b = 205, 240, 170, 120
    phi = math.radians(45)
    px, py, n, e2 = ellipse_point(a, b, phi)
    w = 1 - e2 * math.sin(phi) ** 2
    m = a * (1 - e2) / w ** 1.5
    nx, ny = math.cos(phi), math.sin(phi)
    cmx, cmy = px - m * nx, py - m * ny  # centre of curvature of the meridian
    cnx, cny = px - n * nx, py - n * ny  # centre for the prime vertical, on the axis
    sx = lambda x: cx + x
    sy = lambda y: cy - y
    deg = math.degrees(phi)
    body = [
        line(sx(0), sy(b + 40), sx(0), sy(-b - 30), "aux"),
        line(sx(-a - 10), sy(0), sx(a + 20), sy(0), "aux"),
        f'<ellipse cx="{cx}" cy="{cy}" rx="{a}" ry="{b}" class="body"/>',
        # The circle that best fits the meridian at P: radius M.
        arc(sx(cmx), sy(cmy), m, deg - 38, deg + 38, "blue"),
        line(sx(cnx), sy(cny), sx(px), sy(py), "aux"),
        f'<circle cx="{sx(cmx):.1f}" cy="{sy(cmy):.1f}" r="3.5" fill="{BLUE}"/>',
        # Dimension lines, offset to either side of the normal.
        line(sx(cmx) + 16 * ny, sy(cmy) + 16 * nx, sx(px) + 16 * ny, sy(py) + 16 * nx, "blue", arrow="blue", start_arrow="blue"),
        text(sx((cmx + px) / 2) + 30 * ny, sy((cmy + py) / 2) + 30 * nx + 6, "M", "math blue-t"),
        # The east-west circle: radius N, centre on the axis (drawn schematically in this plane).
        arc(sx(cnx), sy(cny), n, deg - 24, deg + 24, "orange"),
        f'<circle cx="{sx(cnx):.1f}" cy="{sy(cny):.1f}" r="3.5" fill="{ORANGE}"/>',
        line(sx(cnx) - 16 * ny, sy(cny) - 16 * nx, sx(px) - 16 * ny, sy(py) - 16 * nx, "orange", arrow="orange", start_arrow="orange"),
        text(sx((cnx + px) / 2) - 30 * ny, sy((cny + py) / 2) - 30 * nx + 6, "N", "math orange-t"),
        f'<circle cx="{sx(px):.1f}" cy="{sy(py):.1f}" r="4" class="dot"/>',
        text(sx(px) + 10, sy(py) - 8, "P", anchor="start"),
        text(40, 420, '<tspan class="ja blue-t">実線：南北方向に最もよく合う円、半径 </tspan><tspan class="math blue-t">M</tspan>', "ja", anchor="start"),
        text(40, 448, '<tspan class="ja orange-t">破線：東西方向に最もよく合う円、半径 </tspan><tspan class="math orange-t">N</tspan>', "ja", anchor="start"),
        text(40, 472, "（東西の円の中心は地軸上。扁平率は誇張）", "ja muted", anchor="start"),
    ]
    return svg(440, 490, "同じ点 P で南北方向と東西方向に最もよく合う円の半径 M と N", "\n".join(body))


def step():
    # A small patch of the surface around P: north is up, east is right.
    px, py = 170, 240
    lm, ln = 150, 210  # drawn lengths of M dφ and N cos φ dλ
    body = [
        # Faint grid of meridians and parallels, slightly curved.
        f'<path d="M{px - 115},{py + 75} Q{px - 125},{py - lm / 2} {px - 115},{py - lm - 30}" class="aux"/>',
        f'<path d="M{px + ln + 55},{py + 75} Q{px + ln + 45},{py - lm / 2} {px + ln + 55},{py - lm - 30}" class="aux"/>',
        f'<path d="M{px - 130},{py + 72} Q{px + ln / 2},{py + 84} {px + ln + 70},{py + 72}" class="aux"/>',
        f'<path d="M{px - 130},{py - lm - 24} Q{px + ln / 2},{py - lm - 12} {px + ln + 70},{py - lm - 24}" class="aux"/>',
        line(px, py, px, py - lm, "blue", arrow="blue"),
        line(px, py, px + ln, py, "blue", arrow="blue"),
        line(px, py, px + ln, py - lm, "orange", arrow="orange"),
        line(px + ln, py, px + ln, py - lm, "aux"),
        line(px, py - lm, px + ln, py - lm, "aux"),
        right_angle(px, py, 0, -1, 1, 0, size=14),
        f'<circle cx="{px}" cy="{py}" r="4" class="dot"/>',
        text(px - 10, py + 22, "P", anchor="end"),
        text(px - 14, py - lm / 2 - 6, "∂r/∂φ", "math blue-t", anchor="end"),
        text(px - 14, py - lm / 2 + 20, '<tspan class="math blue-t">M dφ</tspan>', "math", anchor="end"),
        text(px + ln / 2, py + 30, "∂r/∂λ", "math blue-t"),
        text(px + ln / 2, py + 54, "N cos φ dλ", "math blue-t"),
        text(px + ln / 2 - 12, py - lm / 2 - 14, "ds", "math orange-t", anchor="end"),
        text(px + ln + 16, py - lm - 4, "北", "ja muted", anchor="start"),
        text(px + ln + 16, py + 6, "東", "ja muted", anchor="start"),
        text(260, 395, "ds² = (M dφ)² + (N cos φ dλ)²", "math"),
    ]
    return svg(520, 420, "点 P から北と東への直交する二つの一歩と、斜めの一歩 ds", "\n".join(body))


def tissot():
    lx, ly, r = 110, 170, 70
    rx, ry, h, k = 380, 170, 105, 62
    body = [
        f'<circle cx="{lx}" cy="{ly}" r="{r}" class="body"/>',
        line(lx, ly, lx, ly - r, "blue", arrow="blue"),
        line(lx, ly, lx + r, ly, "orange", arrow="orange"),
        text(lx - 10, ly - r / 2 + 6, "1", "math up", anchor="end"),
        text(lx + r / 2, ly + 22, "1", "math up"),
        text(lx, ly + r + 44, "地表の小さな円", "ja"),
        line(200, ly, 280, ly, "ink", arrow="ink"),
        text(240, ly - 12, "地図投影", "ja"),
        f'<ellipse cx="{rx}" cy="{ry}" rx="{k}" ry="{h}" class="body"/>',
        line(rx, ry, rx, ry - h, "blue", arrow="blue"),
        line(rx, ry, rx + k, ry, "orange", arrow="orange"),
        text(rx - 10, ry - h / 2 + 6, "h", "math blue-t", anchor="end"),
        text(rx + k / 2, ry + 22, "k", "math orange-t"),
        text(rx, ry + h + 30, "地図上の楕円", "ja"),
        text(rx + k + 16, ry - h + 18, "子午線方向", "ja blue-t", anchor="start"),
        text(rx + k + 16, ry - 8, "緯線方向", "ja orange-t", anchor="start"),
    ]
    return svg(540, 330, "地表の小さな円が地図上で半軸 h と k の楕円になる様子", "\n".join(body))


FIGURES = {
    "sphere.svg": sphere,
    "ellipsoid.svg": ellipsoid,
    "latitude.svg": latitude,
    "radii.svg": radii,
    "step.svg": step,
    "tissot.svg": tissot,
}

if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for name, make in FIGURES.items():
        (OUT / name).write_text(make(), encoding="utf-8")
        print("wrote", OUT / name)
