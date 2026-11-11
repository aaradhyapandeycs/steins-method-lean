"""Build-time check of links into the repository at the pinned commit.

Every `<REPO>/blob/<rev>/<path>[#frag]` link on the site must name a file that exists at that
commit (not a directory), and a `#frag` into a Markdown file must be an anchor GitHub renders
there: an explicit `<a id="...">` / `<a name="...">`, or a heading slug. Line fragments
(`#L12`, `#L12-L30`) are not checked here.
"""

from __future__ import annotations

import html
import re
from urllib.parse import unquote

ANCHOR_TAG_RE = re.compile(r'<a\s+(?:id|name)="([^"]+)"', re.I)
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*#*\s*$")
LINE_FRAG_RE = re.compile(r"L\d+(?:-L\d+)?$")


def heading_slug(text: str) -> str:
    """GitHub's heading anchor: Markdown links/code reduced to their text, lower case, characters
    other than letters, digits, '_', '-' and spaces removed, spaces turned into '-'."""
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"<[^>]+>", "", text)
    text = text.lower()
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def md_anchors(text: str) -> set:
    """All fragment targets GitHub renders for a Markdown file (headings outside code fences)."""
    anchors = set(ANCHOR_TAG_RE.findall(text))
    seen: dict = {}
    fence = False
    for line in text.splitlines():
        if line.lstrip().startswith("```"):
            fence = not fence
            continue
        if fence:
            continue
        m = HEADING_RE.match(line)
        if not m:
            continue
        slug = heading_slug(m.group(2))
        n = seen.get(slug, 0)
        seen[slug] = n + 1
        anchors.add(slug if n == 0 else f"{slug}-{n}")
    return anchors


def repo_link_problems(pages: dict, repo: str, rev: str, files: set, read) -> list:
    """`pages`: page id -> HTML. `files`: every file path at `rev`. `read(path)`: file text at `rev`."""
    prefix = f"{repo}/blob/{rev}/"
    href_re = re.compile(r'href="(' + re.escape(prefix) + r'[^"]*)"')
    cache: dict = {}
    problems: list = []
    reported: set = set()
    for pid, text in pages.items():
        for raw in href_re.findall(text):
            href = html.unescape(raw)
            path, _, frag = href[len(prefix):].partition("#")
            path = unquote(path)
            key = (pid, path, frag)
            if key in reported:
                continue
            if path not in files:
                reported.add(key)
                problems.append(f"{pid}.html: link to {path or '(repository root)'}"
                                f"{'#' + frag if frag else ''}: no such file at {rev[:12]}")
                continue
            if not frag or LINE_FRAG_RE.match(frag) or not path.endswith(".md"):
                continue
            if path not in cache:
                cache[path] = md_anchors(read(path))
            if unquote(frag) not in cache[path]:
                reported.add(key)
                problems.append(f"{pid}.html: link to {path}#{frag}: no such anchor or heading in that file")
    return problems
