#!/usr/bin/env python3
"""Check that no TeX macro reaches a reader unrendered.

    python3 site/check_macros.py [--build site/_build]

Two checks over every built HTML page, reading the page as MathJax does
(``<body class="tex2jax_ignore">``, typesetting only inside ``tex2jax_process``):

1. Outside typeset math, no raw control sequence (``\\name``) may appear in
   the page text. Typeset math is: delimited ``\\(..\\)``, ``\\[..\\]`` and
   ``\\begin{env}..\\end{env}`` inside a ``tex2jax_process`` element, and the
   whole content of display blocks (``<div class="md ...">``). Not checked: the
   "TeX source" disclosures (``<details class="tex-src">``), ``<pre>``,
   ``<code>``, ``<script>``, ``<style>`` and ``<title>``.
2. Inside typeset math, every control sequence must be defined: by the MathJax
   configuration the page loads (inlined in the page, else
   ``assets/mathjax-config.js``; the paper's own macros) or by MathJax itself
   (``site/mathjax_builtins.json``, read from MathJax 3.2.2). Bodies of
   configured macros are checked the same way, and every ``\\begin{env}``
   must name an environment MathJax knows. Every page must load a
   configuration whose macros are the published ones.

Exit status 1 if anything is found. Standard library only.
"""

from __future__ import annotations

import argparse
import glob
import json
import re
import sys
from html.parser import HTMLParser
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILTINS = HERE / "mathjax_builtins.json"

TOKEN = re.compile(r"\\(?:([A-Za-z]+)|.)", re.S)
BEGIN = re.compile(r"\\(?:begin|end)\s*\{([^}]*)\}")
DELIMITED = re.compile(r"\\\((.*?)\\\)|\\\[(.*?)\\\]|(\\begin\{([^}]*)\}.*?\\end\{\4\})", re.S)
RAW = re.compile(r"\\[A-Za-z]+")
SKIP_TAGS = {"script", "style", "pre", "code", "title"}
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}


def builtins() -> tuple:
    d = json.loads(BUILTINS.read_text())
    return set(d["macros"]) | set(d["text_macros"]), set(d["environments"])


INLINE_CFG = re.compile(r"<script>\s*window\.MathJax\s*=\s*(.*?);?\s*</script>", re.S)


def parse_config(js: str) -> dict:
    js = re.sub(r"^\s*window\.MathJax\s*=\s*", "", js.strip()).rstrip(";")
    return json.loads(js.replace("<\\/", "</"))["tex"]["macros"]


def config_macros(build: Path) -> dict:
    return parse_config((build / "assets/mathjax-config.js").read_text())


def page_config(page: str):
    m = INLINE_CFG.search(page)
    if m:
        return parse_config(m.group(1))
    if 'src="assets/mathjax-config.js"' in page:
        return "external"
    return None


def names(tex: str) -> list:
    return [m.group(1) for m in TOKEN.finditer(tex) if m.group(1)]


class Segments(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack: list = []
        self.runs: list = []

    def handle_starttag(self, tag, attrs):
        if tag in VOID:
            return
        cls = (dict(attrs).get("class") or "").split()
        if tag in SKIP_TAGS or (tag == "details" and "tex-src" in cls):
            mode = "skip"
        elif tag == "div" and "md" in cls:
            mode = "math"
        elif "tex2jax_process" in cls:
            mode = "process"
        elif "tex2jax_ignore" in cls:
            mode = "text"
        else:
            mode = None
        self.stack.append((tag, mode))

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        for k in range(len(self.stack) - 1, -1, -1):
            if self.stack[k][0] == tag:
                del self.stack[k:]
                return

    def mode(self) -> str:
        modes = [m for _, m in self.stack if m]
        if "skip" in modes:
            return "skip"
        return modes[-1] if modes else "process"

    def handle_data(self, data):
        self.runs.append((self.mode(), data))


def split(page: str) -> tuple:
    parser = Segments()
    parser.feed(page)
    parser.close()
    joined: list = []
    for mode, data in parser.runs:
        if joined and joined[-1][0] == mode:
            joined[-1][1].append(data)
        else:
            joined.append((mode, [data]))
    prose, math = [], []
    for mode, datas in joined:
        text = "".join(datas)
        if mode == "math":
            math.append(text)
        elif mode == "process":
            for m in DELIMITED.finditer(text):
                math.append(m.group(1) or m.group(2) or m.group(3) or "")
            prose.append(DELIMITED.sub(" ", text))
        elif mode == "text":
            prose.append(text)
    return " ".join(prose), math


def math_spans(page: str) -> list:
    return split(page)[1]


def raw_macros(page: str) -> list:
    return RAW.findall(split(page)[0])


def undefined(tex: str, defined: set, envs: set) -> list:
    bad = [n for n in names(tex) if n not in defined]
    bad += ["{" + e + "}" for e in BEGIN.findall(tex) if e.strip() not in envs]
    return bad


def check(build: Path) -> list:
    macros, envs = builtins()
    cfg = config_macros(build)
    defined = macros | set(cfg)
    problems = []
    for name, body in sorted(cfg.items()):
        body = body[0] if isinstance(body, list) else body
        for n in sorted(set(undefined(body, defined, envs))):
            problems.append(("mathjax-config.js", "macro body", f"\\{name} uses undefined \\{n}"))
    for f in sorted(glob.glob(str(build / "*.html"))):
        page = Path(f).read_text()
        rel = Path(f).name
        prose, math = split(page)
        if math or "MathJax" in page:
            loaded = page_config(page)
            if loaded is None:
                problems.append((rel, "no MathJax configuration", "page loads no macro definitions"))
            elif loaded != "external" and loaded != cfg:
                problems.append((rel, "stale MathJax configuration", "inline macros differ from assets/mathjax-config.js"))
        for r in sorted(set(RAW.findall(prose))):
            problems.append((rel, "raw macro outside math", r))
        seen = set()
        for tex in math:
            for n in undefined(tex, defined, envs):
                if n not in seen:
                    seen.add(n)
                    problems.append((rel, "undefined in math", n if n.startswith("{") else "\\" + n))
    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build", default=str(HERE / "_build"))
    args = ap.parse_args()
    problems = check(Path(args.build))
    for page, kind, detail in problems[:200]:
        print(f"    {page}: {kind}: {detail}")
    print("MACROS OK" if not problems else f"MACRO PROBLEMS: {len(problems)}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
