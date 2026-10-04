#!/usr/bin/env python3
"""Build offline source links for the Blueprint's Lean declarations.

Run AFTER plasTeX.  Only blueprint/web/lean/ is written; generated chapter
pages are never rewritten.  A previous successful verify_lean_refs.py run
supplies compiler-derived declaration module and line positions.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
from html import escape
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


PROJECT = Path(__file__).resolve().parents[2]
BLUEPRINT = PROJECT / "blueprint"
WEB = BLUEPRINT / "web"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


STYLE = """
body{margin:0;font:16px system-ui,sans-serif;color:#182334;background:#fff}
header{padding:1rem 1.5rem;border-bottom:1px solid #dde3ea;background:#f6f8fa}
header h1{font-size:1.15rem;margin:0 0 .4rem}a{color:#145da0}
main{padding:1rem 1.5rem}pre{font:13px/1.55 ui-monospace,SFMono-Regular,Consolas,monospace;overflow:auto;margin:0;padding:1rem 0}
.line{display:block;white-space:pre;min-height:1.55em}.line:target{background:#fff1b8;outline:1px solid #e5c84c}
.number{display:inline-block;min-width:4.5em;padding:0 1em 0 .5em;color:#788493;text-align:right;text-decoration:none;user-select:none}
code{font-family:ui-monospace,SFMono-Regular,Consolas,monospace}.muted{color:#647285;font-size:.9rem}
"""


def source_html(path: Path, declarations: list[dict]) -> str:
    relative = path.relative_to(PROJECT).as_posix()
    # A page at lean/sources/SerreMarkov/Foo.lean.html goes three levels up
    # to the blueprint root.  This also supports deeper module directories.
    depth = len(Path(relative).parts)
    blueprint_home = "../" * (depth + 1) + "index.html"
    entries = " · ".join(f'<a href="#L{item["line"]}">{escape(item["name"])}</a>' for item in declarations)
    rows = []
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        rows.append(f'<span class="line" id="L{index}"><a class="number" href="#L{index}">{index}</a>{escape(line)}</span>')
    return f'''<!doctype html>
<html lang="ja"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{escape(relative)} — Lean source</title><style>{STYLE}</style></head><body>
<header><h1>{escape(relative)}</h1><a href="{blueprint_home}">Blueprint</a>
<p class="muted">Original project source · SHA256 {digest(path)}</p>
<div>{entries}</div></header><pre>{''.join(rows)}</pre></body></html>
'''


RESOLVER = '''<!doctype html>
<html lang="ja"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Lean declaration source</title><style>STYLE</style></head><body>
<header><h1>Lean declaration source</h1><a href="../../index.html">Blueprint</a></header>
<main><p id="status">宣言に対応する Lean ソースを開いています。</p><ul id="declarations"></ul></main>
<script src="declarations.js"></script><script>
"use strict";
function resolveDeclaration(){
  const prefix="#doc/";
  const entries=window.LEAN_BLUEPRINT_DECLARATIONS||{};
  const status=document.getElementById("status");
  const list=document.getElementById("declarations");
  list.replaceChildren();
  if(location.hash.startsWith(prefix)){
    let name;
    try{name=decodeURIComponent(location.hash.slice(prefix.length));}
    catch(error){status.textContent="宣言名の URL を読めません。";return;}
    const entry=entries[name];
    if(entry){location.replace(entry.href);return;}
    status.textContent="対応する宣言が見つかりません: "+name;
  }else{status.textContent="Blueprint に対応する Lean 宣言一覧";}
  for(const name of Object.keys(entries).sort()){
    const item=document.createElement("li");
    const link=document.createElement("a");
    link.href=entries[name].href;link.textContent=name;
    item.append(link);list.append(item);
  }
}
window.addEventListener("hashchange",resolveDeclaration);
resolveDeclaration();
</script></body></html>
'''


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "a":
            self.hrefs.extend(value for key, value in attrs if key == "href" and value is not None)


def verify_links(entries: dict[str, dict]) -> dict:
    found: list[dict] = []
    errors: list[str] = []
    pages = list(WEB.glob("*.html"))
    for page in pages:
        parser = LinkCollector()
        parser.feed(page.read_text(encoding="utf-8"))
        for href in parser.hrefs:
            split = urlsplit(href)
            if "lean/find" not in split.path or not split.fragment.startswith("doc/"):
                continue
            name = unquote(split.fragment[4:])
            record = {"html": str(page.relative_to(BLUEPRINT)), "href": href, "name": name}
            found.append(record)
            if name not in entries:
                errors.append(f"{page.name}: unknown Lean declaration {name}")
                continue
            entry = entries[name]
            target = (WEB / "lean/find" / entry["href"].split("#", 1)[0]).resolve()
            anchor = entry["href"].split("#", 1)[1]
            if not target.is_file() or f'id="{anchor}"' not in target.read_text(encoding="utf-8"):
                errors.append(f"{page.name}: missing source anchor for {name}")
    if not found:
        errors.append("No generated Blueprint declaration links were found; run plasTeX first")
    return {"passed": not errors, "html_pages": len(pages), "declaration_links": len(found), "errors": errors, "links": found}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-links", action="store_true", help="Require all generated Blueprint declaration links to resolve")
    args = parser.parse_args()
    audit_path = BLUEPRINT / "verification/lean_references.json"
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    if not audit["passed"]:
        raise ValueError("The Blueprint Lean declaration audit has not passed")
    entries = {}
    by_source: dict[str, list[dict]] = {}
    for entry in audit["declarations"]:
        path = PROJECT / entry["source"]
        if digest(path) != entry["source_sha256"]:
            raise ValueError(f"Source changed since reference audit: {entry['source']}")
        record = dict(entry)
        record["href"] = "../sources/" + entry["source"] + ".html#L" + str(entry["line"])
        entries[entry["name"]] = record
        by_source.setdefault(entry["source"], []).append(entry)
    find = WEB / "lean/find"
    find.mkdir(parents=True, exist_ok=True)
    sources = list(sorted((PROJECT / "SerreMarkov").rglob("*.lean")))
    sources.append(PROJECT / "SerreMarkov.lean")
    for path in sources:
        relative = path.relative_to(PROJECT).as_posix()
        target = WEB / "lean/sources" / (relative + ".html")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source_html(path, by_source.get(relative, [])), encoding="utf-8")
    (find / "declarations.json").write_text(json.dumps(entries, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (find / "declarations.js").write_text("window.LEAN_BLUEPRINT_DECLARATIONS=" + json.dumps(entries, ensure_ascii=False, separators=(",", ":")) + ";\n", encoding="utf-8")
    (find / "index.html").write_text(RESOLVER.replace("STYLE", STYLE), encoding="utf-8")
    report = {
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "reference_audit_sha256": digest(audit_path),
        "declarations": len(entries), "source_pages": len(sources),
        "offline_resolver": "web/lean/find/index.html",
    }
    if args.verify_links:
        report["link_validation"] = verify_links(entries)
    (BLUEPRINT / "verification/lean_links.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Generated offline Lean resolver: {len(entries)} declarations, {len(sources)} source pages")
    if args.verify_links:
        result = report["link_validation"]
        print(f"Blueprint links: {result['declaration_links']} checked; passed={result['passed']}")
        if not result["passed"]:
            for error in result["errors"]:
                print(error)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
