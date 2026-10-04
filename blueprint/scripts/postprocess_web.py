#!/usr/bin/env python3
"""Finish the generated Blueprint HTML and add a static dependency graph.

Run after plasTeX and build_lean_links.py. Requires pygraphviz and Graphviz.
The vendored MathJax tree must already exist under web/vendor/mathjax/.
"""

from __future__ import annotations

import datetime as dt
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil


BLUEPRINT = Path(__file__).resolve().parents[1]
WEB = BLUEPRINT / "web"


class IdCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids = []

    def handle_starttag(self, tag, attrs) -> None:
        self.ids.extend(value for key, value in attrs if key == "id" and value is not None)


def source_anchors() -> dict[str, str]:
    anchors = {}
    for page in sorted(WEB.glob("*.html")):
        if page.name.startswith("dep_graph"):
            continue
        parser = IdCollector()
        parser.feed(page.read_text(encoding="utf-8"))
        for label in parser.ids:
            if label.startswith("bp:"):
                anchors[label] = page.name + "#" + label
    return anchors


def static_graph(text: str) -> tuple[str, dict]:
    import pygraphviz

    match = re.search(r"\.renderDot\(`(?P<dot>[^`]*)`\)", text)
    if not match:
        raise ValueError("Generated dependency page has no renderDot template")
    # DOT is taken as raw text, avoiding JavaScript string-escape interpretation.
    graph = pygraphviz.AGraph(string=match.group("dot"))
    anchors = source_anchors()
    links = {}
    for node in graph.nodes():
        label = str(node)
        if label not in anchors:
            raise ValueError(f"Dependency graph node has no chapter anchor: {label}")
        node.attr.update(URL=anchors[label], target="_top", tooltip=label)
        links[label] = anchors[label]
    structure = json.loads((BLUEPRINT / "verification/structure.json").read_text(encoding="utf-8"))
    explicit_edges = {tuple(edge) for edge in structure["edges"]}
    displayed_edges = {(str(a), str(b)) for a, b in graph.edges()}
    if set(links) != {node["label"] for node in structure["nodes"]}:
        raise ValueError("Rendered graph nodes differ from the mathematical Blueprint nodes")
    if not displayed_edges <= explicit_edges:
        raise ValueError("Rendered graph introduces edges absent from the Blueprint")
    outgoing = {label: set() for label in links}
    for dependency, owner in displayed_edges:
        outgoing[dependency].add(owner)
    def reaches(dependency, owner):
        seen, stack = {dependency}, [dependency]
        while stack:
            label = stack.pop()
            for next_label in outgoing[label] - seen:
                if next_label == owner:
                    return True
                seen.add(next_label)
                stack.append(next_label)
        return False
    if not all(reaches(dependency, owner) for dependency, owner in explicit_edges):
        raise ValueError("Rendered graph loses an explicit Blueprint dependency")
    graph.draw(str(WEB / "graph.svg"), prog="dot", format="svg")
    graph.write(str(BLUEPRINT / "verification/dependency_graph.dot"))
    if 'id="graph-fallback"' not in text:
        fallback = '''<div id="graph"><div id="graph-fallback" style="height:100%;overflow:auto">
<p style="padding:.5rem 1rem;margin:0">静的な依存グラフ。各ノードから対応する定義・定理へ移動できます。</p>
<object data="graph.svg" type="image/svg+xml" style="width:100%;height:calc(100% - 3rem)" aria-label="数学的依存グラフ">
<img src="graph.svg" alt="数学的依存グラフ" style="max-width:100%"></object>
</div></div>'''
        text, changed = re.subn(r'<div id="graph">\s*</div>', lambda _: fallback, text, count=1)
        if changed != 1:
            raise ValueError("Could not insert static graph fallback")
    if "BLUEPRINT_STATIC_FALLBACK" not in text:
        text, changed = re.subn(
            r"function interactive\(\)\s*\{",
            'function interactive() {\n    // BLUEPRINT_STATIC_FALLBACK: hide only after interactive graph rendering succeeds.\n'
            '    const fallback = document.getElementById("graph-fallback");\n'
            '    if (fallback) fallback.style.display = "none";',
            text, count=1,
        )
        if changed != 1:
            raise ValueError("Could not connect interactive graph completion")
    return text, {
        "nodes": graph.number_of_nodes(), "edges": graph.number_of_edges(),
        "explicit_mathematical_edges": len(explicit_edges),
        "all_explicit_dependencies_preserved": True,
        "no_extra_direct_edges": True,
        "source_links": links,
    }


def main() -> int:
    mathjax = WEB / "vendor/mathjax/tex-chtml.js"
    if not mathjax.is_file():
        raise ValueError("Copy MathJax's es5 tree to blueprint/web/vendor/mathjax/ before postprocessing")
    verification = BLUEPRINT / "verification"
    verification.mkdir(parents=True, exist_ok=True)
    overview = BLUEPRINT / "src/overview.svg"
    shutil.copyfile(overview, WEB / "overview.svg")
    report = {"generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "html_pages": 0, "lean_link_replacements": 0, "mathjax_replacements": 0}
    for page in sorted(WEB.rglob("*.html")):
        text = page.read_text(encoding="utf-8")
        text = re.sub(r'<html(?:\s+lang="[^"]*")?\s*>', '<html lang="ja">', text, count=1)
        text, count = re.subn(r"lean/find/#doc/", "lean/find/index.html#doc/", text)
        report["lean_link_replacements"] += count
        relative_mathjax = Path(os.path.relpath(mathjax, page.parent)).as_posix()
        text, count = re.subn(
            r'(src=["\'])https?://[^"\']*mathjax[^"\']*(["\'])',
            lambda match: match.group(1) + relative_mathjax + match.group(2), text,
            flags=re.IGNORECASE,
        )
        report["mathjax_replacements"] += count
        if "この Blueprint の読み方</h1>" in text and 'id="blueprint-overview"' not in text:
            figure = '''\n<figure id="blueprint-overview" style="margin:1.5rem 0">
<img src="overview.svg" alt="主分類・ファイバー・判定算法の証明経路" style="width:100%;height:auto;max-width:1100px">
<figcaption>形式化した証明経路の概観</figcaption></figure>'''
            text, count = re.subn(r'(<h1[^>]*>この Blueprint の読み方</h1>)', lambda match: match.group(1) + figure, text, count=1)
            if count != 1:
                raise ValueError("Could not display the Blueprint overview")
        if page.name == "dep_graph_document.html":
            text, report["static_graph"] = static_graph(text)
        page.write_text(text, encoding="utf-8")
        report["html_pages"] += 1
    if "static_graph" not in report:
        raise ValueError("Generated dependency graph HTML is missing")
    report["passed"] = True
    (verification / "web_postprocess.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    graph = report["static_graph"]
    print(f"Blueprint HTML finished: {report['html_pages']} pages; static graph {graph['nodes']} nodes, {graph['edges']} edges")
    print(f"Lean links normalized: {report['lean_link_replacements']}; MathJax scripts vendored: {report['mathjax_replacements']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
