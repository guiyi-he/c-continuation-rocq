"""Convert a ccont text DFA into an editable https://q.uiver.app/ diagram.

Uses quiver's version-0 URL format. Only the Python standard library is needed.
"""

import argparse
import base64
import collections
import hashlib
import html
import json
from pathlib import Path
import re


NODE = re.compile(
    r"^  (\d+): witness=(.*?) continuation=(.*?) final=(true|false)"
    r"(?: bits=([01]+) residues=\{([^}]*)\})?$", re.MULTILINE
)
EDGE = re.compile(r"^  (\d+) -(.+?)-> (\d+)$", re.MULTILINE)


def parse_dfa(path):
    raw = path.read_bytes()
    text = raw.decode("utf-8-sig")
    text = text.replace("\r\n", "\n")
    nodes = []
    for q, witness, expression, final, bits, residues in NODE.findall(text):
        nodes.append(dict(id=int(q), witness=witness, continuation=expression,
                          final=final == "true", bits=bits, residues=residues))
    edges = [(int(q), symbol, int(t)) for q, symbol, t in EDGE.findall(text)]
    count = int(re.search(r"^States: (\d+)$", text, re.MULTILINE).group(1))
    initial = int(re.search(r"^q0 = (\d+)$", text, re.MULTILINE).group(1))
    alphabet = re.search(r"^Sigma = \{(.*?)\}$", text, re.MULTILINE).group(1).split(",")
    finals_text = re.search(r"^F = \{(.*?)\}$", text, re.MULTILINE).group(1)
    finals = {int(q) for q in finals_text.split(",") if q}
    ids = {n["id"] for n in nodes}
    if len(nodes) != count or len(ids) != count or initial not in ids:
        raise ValueError("State count, unique state IDs or initial state is invalid")
    if finals != {n["id"] for n in nodes if n["final"]}:
        raise ValueError("Final-state list disagrees with state details")
    if len(set(alphabet)) != len(alphabet) or any(not a for a in alphabet):
        raise ValueError("Alphabet is invalid")
    transitions = {}
    for q, symbol, t in edges:
        if q not in ids or t not in ids or symbol not in alphabet:
            raise ValueError("A transition references an invalid state or symbol")
        if (q, symbol) in transitions:
            raise ValueError("Duplicate transition")
        transitions[q, symbol] = t
    if len(edges) != count * len(alphabet):
        raise ValueError("The transition table is not complete")
    distance = {initial: 0}
    pending = collections.deque([initial])
    while pending:
        q = pending.popleft()
        for a in alphabet:
            t = transitions[q, a]
            if t not in distance:
                distance[t] = distance[q] + 1
                pending.append(t)
    if set(distance) != ids:
        raise ValueError("The file contains an unreachable state")
    for n in nodes:
        q = initial
        # ccont's text words encode this project's single-character alphabet.
        for a in n["witness"]:
            q = transitions[q, a]
        if q != n["id"] or len(n["witness"]) != distance[q]:
            raise ValueError("A witness does not replay or is not shortest")
        if n["bits"]:
            expected = ",".join(str(i) for i, b in enumerate(n["bits"]) if b == "1")
            if expected != n["residues"] or (n["bits"][0] == "1") != n["final"]:
                raise ValueError("Bits, residues or final flag disagree")
    return nodes, edges, alphabet, initial, distance, hashlib.sha256(raw).hexdigest()


def make_payload(nodes, edges, alphabet, initial, distance):
    layers = collections.defaultdict(list)
    for n in nodes:
        layers[distance[n["id"]]].append(n["id"])
    positions = {}
    for depth, layer in layers.items():
        for rank, q in enumerate(layer):
            positions[q] = [3 * depth, 2 * rank - (len(layer) - 1)]
    # Version-0 quiver URL imports require nonnegative grid coordinates.
    min_y = min(y for _, y in positions.values())
    positions = {q: [x, y - min_y] for q, (x, y) in positions.items()}
    indices = {n["id"]: i for i, n in enumerate(nodes)}
    vertices = []
    for n in nodes:
        label = f'q_{{{n["id"]}}}'
        colour = [0, 0, 20, 1]
        if n["final"]:
            label += "^{\\star,\\mathrm{init}}" if n["id"] == initial else "^{\\star}"
            colour = [145, 65, 32, 1]
        if n["id"] == initial:
            if not n["final"]:
                label += "^{\\mathrm{init}}"
            colour = [215, 75, 40, 1]
        vertices.append([*positions[n["id"]], label, colour])
    pairs = collections.Counter((q, t) for q, _, t in edges)
    pair_rank = collections.defaultdict(int)
    arrow_cells = []
    for q, a, t in edges:
        ai = alphabet.index(a)
        colour = [215, 70, 44, 1] if ai == 0 else [28, 80, 43, 1]
        options = {"colour": colour}
        rank = pair_rank[q, t]
        pair_rank[q, t] += 1
        if q == t:
            options.update(radius=3, angle=-60 + rank * 120)
        elif pairs[q, t] > 1:
            options["curve"] = 2 * rank - (pairs[q, t] - 1)
        elif (t, q) in pairs:
            options["curve"] = 2
        elif distance[t] <= distance[q]:
            options["curve"] = 1 if ai == 0 else -1
        label = a if a.isalnum() else "\\text{" + a.replace("\\", "\\backslash ") + "}"
        arrow_cells.append([indices[q], indices[t], label, 0, options, colour])
    return [0, len(nodes), *vertices, *arrow_cells]


def validate_payload(payload, nodes, edges):
    count = payload[1]
    recovered = [(nodes[e[0]]["id"], e[2], nodes[e[1]]["id"])
                 for e in payload[2 + count:]]
    if recovered != edges:
        raise ValueError("Quiver transitions do not reproduce the input")
    if len({tuple(v[:2]) for v in payload[2:2 + count]}) != count:
        raise ValueError("Layout puts two vertices at the same position")
    if any(x < 0 or y < 0 for x, y, *_ in payload[2:2 + count]):
        raise ValueError("Quiver URL coordinates must be nonnegative")


def make_html(nodes, edges, initial, url, digest):
    esc = html.escape
    rows = []
    for n in nodes:
        rows.append(
            f'<tr data-search="{esc(str(n["id"]) + " " + n["witness"], quote=True)}">'
            f'<td>q<sub>{n["id"]}</sub>{" ★" if n["final"] else ""}'
            f'{" 初态" if n["id"] == initial else ""}</td>'
            f'<td><code>{esc(n["witness"]) or "ε"}</code></td>'
            f'<td>{"是" if n["final"] else "否"}</td>'
            f'<td><code>{esc(n["bits"])}</code></td>'
            f'<td><code>{{{esc(n["residues"])}}}</code></td>'
            f'<td><details><summary>查看剩余表达式</summary>'
            f'<code class="expression">{esc(n["continuation"])}</code></details></td></tr>'
        )
    return f'''<!doctype html>
<html lang="zh-CN"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>derivative_dfa.txt — quiver DFA</title>
<style>
body{{font:16px/1.6 system-ui,sans-serif;margin:32px auto;padding:0 24px;max-width:1280px;color:#183044;background:#f7fafc}}
h1{{font-size:28px}} .card{{background:white;padding:24px;border:1px solid #dce5ed;border-radius:14px;margin:20px 0}}
.button{{display:inline-block;background:#245bb3;color:white;text-decoration:none;padding:12px 20px;border-radius:8px;margin:8px 12px 8px 0}}
.secondary{{background:#526479}} a{{color:#245bb3}} code{{font-family:Consolas,monospace}}
table{{width:100%;border-collapse:collapse;font-size:14px}}th,td{{text-align:left;padding:10px;border-bottom:1px solid #e1e7ed;vertical-align:top}}
th{{background:#edf3fa}} .table-scroll{{overflow:auto}}.expression{{display:block;overflow-wrap:anywhere;max-width:480px;padding:12px;background:#eef4f8}}
input{{font:inherit;padding:8px 12px;border:1px solid #bccbda;border-radius:6px;width:min(90%,360px)}}
.small{{font-size:13px;color:#526479;overflow-wrap:anywhere}}summary{{cursor:pointer}}[hidden]{{display:none!important}}
</style>
<h1>REwPLA 导数 DFA</h1>
<section class="card">
<p><strong>{len(nodes)} 个状态 · {len(edges)} 条转移 · {sum(n["final"] for n in nodes)} 个终态</strong>，完整转换自 derivative_dfa.txt。</p>
<a class="button" id="open" href="{esc(url, quote=True)}" target="_blank" rel="noopener">在 quiver 中打开完整 DFA</a>
<a class="button secondary" href="{esc(url.replace('&scale=-3', '&scale=-1'), quote=True)}" target="_blank" rel="noopener">以较大比例打开</a>
<p>蓝色 init 为初态；绿色 ★ 为终态；蓝色箭头标 a，橙色箭头标 b。左右位置对应最短路径长度。</p>
<p>打开后可放大、拖动和编辑。完整图较密集：先查看总览，再放大局部。所有状态和转移均已保留，包括自环和同一对状态之间的两条不同字符转移。</p>
<p><a href="derivative_dfa.quiver.url.txt">链接文本</a> · <a href="derivative_dfa.quiver.json">quiver 数据</a> · <a href="derivative_dfa.quiver.metadata.json">状态详情数据</a></p>
<p class="small">源文件 SHA-256：{digest}</p>
</section>
<section class="card"><p>按状态编号或见证词筛选：<input id="filter" placeholder="例如 2 或 aa" aria-label="按状态编号或见证词筛选"></p>
<div class="table-scroll"><table><thead><tr><th>状态</th><th>最短见证词</th><th>接受</th><th>bits</th><th>residues</th><th>continuation</th></tr></thead>
<tbody>{"".join(rows)}</tbody></table></div></section>
<script>
document.getElementById('filter').addEventListener('input',event=>{{
 const query=event.target.value.trim().toLowerCase();
 document.querySelectorAll('tbody tr').forEach(row=>{{row.hidden=!row.dataset.search.toLowerCase().includes(query)}});
}});
</script></html>
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=Path("derivative_dfa.txt"))
    parser.add_argument("--output-dir", type=Path, default=Path("visualizations"))
    args = parser.parse_args()
    nodes, edges, alphabet, initial, distance, digest = parse_dfa(args.input)
    payload = make_payload(nodes, edges, alphabet, initial, distance)
    validate_payload(payload, nodes, edges)
    packed = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    encoded = base64.b64encode(packed.encode("utf-8")).decode("ascii")
    url = "https://q.uiver.app/#q=" + encoded + "&scale=-3&theme=light"
    # Verify URL round-trip rather than assuming the encoded representation is intact.
    assert json.loads(base64.b64decode(encoded)) == payload
    args.output_dir.mkdir(parents=True, exist_ok=True)
    def write(name, content):
        (args.output_dir / name).write_text(content, encoding="utf-8", newline="\n")
    write("derivative_dfa.quiver.json", json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    write("derivative_dfa.quiver.url.txt", url + "\n")
    write("derivative_dfa.quiver.html", make_html(nodes, edges, initial, url, digest))
    metadata = dict(source=str(args.input), source_sha256=digest, state_count=len(nodes),
                    transition_count=len(edges), final_count=sum(n["final"] for n in nodes),
                    initial=initial, alphabet=alphabet, nodes=nodes, transitions=edges,
                    legend="init = initial; green star = final; a = blue; b = orange")
    write("derivative_dfa.quiver.metadata.json", json.dumps(metadata, ensure_ascii=False, indent=2) + "\n")
    print(f"Exported {len(nodes)} states, {len(edges)} transitions, "
          f"{metadata['final_count']} final states to {args.output_dir}")


if __name__ == "__main__":
    main()
