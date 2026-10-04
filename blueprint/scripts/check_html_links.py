#!/usr/bin/env python3
"""Check local asset paths and static anchors after Blueprint rendering."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import json

BLUEPRINT = Path(__file__).resolve().parents[1]
WEB = BLUEPRINT / "web"

class Parser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links, self.ids = [], set()

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key == "id" and value:
                self.ids.add(value)
            if key in ["href", "src", "data"] and value:
                self.links.append(value)

def main():
    parsers = {}
    for path in WEB.rglob("*.html"):
        parser = Parser()
        parser.feed(path.read_text(encoding="utf-8"))
        parsers[path.resolve()] = parser
    errors, count = [], 0
    for path, parser in parsers.items():
        for raw in parser.links:
            url = urlsplit(raw)
            if url.scheme or url.netloc:
                continue
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            if target.is_dir():
                target = target / "index.html"
            if not target.is_file():
                errors.append([str(path.relative_to(WEB)), raw, "file missing"])
                continue
            # #doc/ names are resolved by JavaScript and checked separately.
            if (url.fragment and not url.fragment.startswith("doc/") and
                target in parsers and unquote(url.fragment) not in parsers[target].ids):
                errors.append([str(path.relative_to(WEB)), raw, "anchor missing"])
            count += 1
    report = {"passed": not errors, "local_links_checked": count,
              "html_pages": len(parsers), "errors": errors}
    (BLUEPRINT / "verification/html_links.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False))
    return bool(errors)

if __name__ == "__main__":
    raise SystemExit(main())
