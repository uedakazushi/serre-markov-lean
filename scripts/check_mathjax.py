from pathlib import Path
import hashlib, json
p=Path(__file__).resolve().parents[1]
for name, expected in json.loads((p/'blueprint/mathjax-sha256.json').read_text()).items():
    path=p/'blueprint/web/vendor/mathjax'/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
        raise SystemExit('MathJax content differs from the original checked distribution: '+name)
print('MathJax file hashes verified.')
