#!/usr/bin/env python3
"""Check Blueprint labels, references, explicit dependencies, and acyclicity.

This checks the author-supplied mathematical DAG, not Lean's complete compiled
declaration-dependency graph. Only Python's standard library is needed.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
import datetime as dt
import hashlib
import json
from pathlib import Path
import re


BLUEPRINT = Path(__file__).resolve().parents[1]
SRC = BLUEPRINT / "src"
MATH_ENVS = {"definition", "theorem", "proposition", "lemma", "corollary", "example", "remark"}
TOKEN = re.compile(
    r"\\(?P<environment>begin|end)\s*\{(?P<envname>[^{}]+)\}"
    r"|\\(?P<command>label|uses|ref|eqref|cref|Cref|autoref|nameref)\s*\{(?P<argument>[^{}]*)\}"
)


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def source_files() -> list[Path]:
    # Preserve the input order, since proof environments belong to the result
    # that precedes them. Explicit chapter input paths are resolved from src/.
    main = SRC / "content.tex"
    paths = [main]
    for match in re.finditer(r"\\input\s*\{([^{}]+)\}", strip_comments(main.read_text(encoding="utf-8"))):
        path = SRC / (match.group(1) + ("" if match.group(1).endswith(".tex") else ".tex"))
        if not path.is_file():
            raise ValueError(f"Missing chapter input: {path}")
        paths.append(path)
    return paths


def main() -> int:
    labels: dict[str, list[dict]] = defaultdict(list)
    uses: list[dict] = []
    references: list[dict] = []
    nodes: list[dict] = []
    errors: list[str] = []
    inputs = []
    for path in source_files():
        text = strip_comments(path.read_text(encoding="utf-8"))
        relative = str(path.relative_to(BLUEPRINT))
        inputs.append({"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        stack: list[dict] = []
        last_math: dict | None = None
        for match in TOKEN.finditer(text):
            location = {"path": relative, "line": text.count("\n", 0, match.start()) + 1}
            if match.group("environment"):
                env = match.group("envname")
                if match.group("environment") == "begin":
                    frame = {"env": env}
                    if env in MATH_ENVS:
                        node = {"label": None, "kind": env, **location}
                        nodes.append(node)
                        frame["node"] = node
                        last_math = node
                    stack.append(frame)
                else:
                    if not stack or stack[-1]["env"] != env:
                        errors.append(f"{relative}:{location['line']}: unmatched end {{{env}}}")
                    else:
                        stack.pop()
                continue
            command, argument = match.group("command", "argument")
            current = next((frame["node"] for frame in reversed(stack) if "node" in frame), None)
            if command == "label":
                label = argument.strip()
                labels[label].append(location)
                if current is not None and current["label"] is None:
                    current["label"] = label
            elif command == "uses":
                owner = current if current is not None else last_math
                if owner is None:
                    errors.append(f"{relative}:{location['line']}: dependency without a result")
                else:
                    uses.append({"owner": owner, "targets": [part.strip() for part in argument.split(",")], **location})
            else:
                references.append({"command": command, "targets": [part.strip() for part in argument.split(",")], **location})
        if stack:
            errors.append(f"{relative}: unclosed environments {[frame['env'] for frame in stack]}")
    for label, locations in labels.items():
        if len(locations) != 1:
            errors.append(f"Duplicate label {label}: {locations}")
    for node in nodes:
        if node["label"] is None:
            errors.append(f"Mathematical environment has no label: {node}")
    node_by_label = {node["label"]: node for node in nodes if node["label"] is not None}
    edges: set[tuple[str, str]] = set()
    for record in uses:
        owner = record["owner"]["label"]
        for target in record["targets"]:
            if target not in labels:
                errors.append(f"{record['path']}:{record['line']}: missing dependency label {target}")
            elif target not in node_by_label:
                errors.append(f"Dependency target is not a mathematical node: {target}")
            elif owner is not None:
                edges.add((target, owner))
    for record in references:
        for target in record["targets"]:
            if target not in labels:
                errors.append(f"{record['path']}:{record['line']}: missing {record['command']} label {target}")
    outgoing: dict[str, set[str]] = defaultdict(set)
    indegree = {label: 0 for label in node_by_label}
    for dependency, owner in edges:
        outgoing[dependency].add(owner)
        indegree[owner] += 1
    queue = deque(sorted(label for label, degree in indegree.items() if degree == 0))
    order = []
    while queue:
        label = queue.popleft()
        order.append(label)
        for owner in sorted(outgoing[label]):
            indegree[owner] -= 1
            if indegree[owner] == 0:
                queue.append(owner)
    dag = len(order) == len(node_by_label)
    if not dag:
        errors.append(f"Dependency cycle involves {[label for label, degree in indegree.items() if degree]}")
    report = {
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "passed": not errors, "acyclic": dag, "labels": len(labels),
        "mathematical_nodes": len(nodes), "mathematical_edges": len(edges),
        "node_kinds": dict(Counter(node["kind"] for node in nodes)),
        "dependency_occurrences": sum(len(record["targets"]) for record in uses),
        "reference_occurrences": sum(len(record["targets"]) for record in references),
        "inputs": inputs, "nodes": nodes, "edges": [list(edge) for edge in sorted(edges)],
        "topological_order": order, "errors": errors,
    }
    out = BLUEPRINT / "verification/structure.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    summary = f"Blueprint structure: {len(nodes)} mathematical nodes, {len(edges)} edges; DAG={dag}; passed={not errors}"
    (out.parent / "structure.log").write_text(summary + "\n" + "\n".join(errors), encoding="utf-8")
    print(summary)
    for error in errors:
        print(error)
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
