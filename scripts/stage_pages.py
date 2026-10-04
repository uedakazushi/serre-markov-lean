#!/usr/bin/env python3
"""Package the current verified output; never changes mathematical sources."""
from pathlib import Path
import json, os, shutil, hashlib
p = Path(__file__).resolve().parents[1]
out = p / '_site'
if out.exists(): shutil.rmtree(out)
shutil.copytree(p/'blueprint/web', out)
shutil.copy2(p/'blueprint/print/print.pdf', out/'blueprint.pdf')
shutil.copytree(p/'blueprint/verification', out/'verification')
shutil.copy2(p/'LICENSE', out/'LICENSE.txt')
shutil.copytree(p/'LICENSES', out/'LICENSES')
(out/'.nojekyll').touch()
info = {'commit': os.environ.get('GITHUB_SHA'), 'repository': os.environ.get('GITHUB_REPOSITORY'),
        'lean_toolchain': (p/'lean-toolchain').read_text().strip(),
        'pdf_sha256': hashlib.sha256((out/'blueprint.pdf').read_bytes()).hexdigest(),
        'verification': 'See GitHub Actions for this commit; local staging alone does not certify a build.'}
(out/'build-info.json').write_text(json.dumps(info,ensure_ascii=False,indent=2))
index = out/'index.html'
text=index.read_text()
nav='<nav style="padding:1rem"><a href="blueprint.pdf">Blueprint PDF</a> · <a href="build-info.json">Build provenance</a>'
repo=os.environ.get('GITHUB_REPOSITORY')
if repo: nav += f' · <a href="https://github.com/{repo}">GitHub source and CI</a>'
nav+=' · <a href="LICENSE.txt">Licenses and attribution</a></nav>'
import re
text=re.sub(r'(<body[^>]*>)',lambda m:m[0]+nav,text,count=1)
index.write_text(text)
print('Staged HTML, PDF, verification records and commit provenance.')
