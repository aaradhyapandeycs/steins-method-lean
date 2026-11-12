"""TeX to HTML for the Stein's method paper reader.

Ported from the RL site reader with Ross's probability macros added.

The converter keeps every character offset of the source file (comments are
masked with spaces, never removed), so each block it emits knows its exact
file and line range.  Text-mode markup becomes HTML; math is passed through
as TeX for MathJax, with equation numbers taken from the inventory instead
of recomputed.

Ross's macros handled here (applied before ``parse_macros`` so they appear
even when the preamble macro definitions are not loaded):
  \\IE   → \\mathbb{E}       (expectation)
  \\IP   → \\mathbb{P}       (probability)
  \\I    → \\mathbb{I}       (indicator)
  \\dtv  → d_{\\mathrm{TV}}
  \\dw   → d_{\\mathrm{W}}
  \\dk   → d_{\\mathrm{K}}
  \\Po   → \\mathrm{Po}
  \\Exp  → \\mathrm{Exp}
  \\Ge   → \\mathrm{Ge}
  \\Geo  → \\mathrm{Geo}
  \\ER   → \\mathcal{G}(n,p)
  \\abs  → \\left|#1\\right|
  \\norm → \\left\\|#1\\right\\|
  \\var  → \\mathrm{Var}
  \\cov  → \\mathrm{Cov}
  \\ba / \\ee  → begin/end aligned
  \\ban / \\bes / \\be → begin/end equation-array shorthands
"""

from __future__ import annotations

import html
import re
import unicodedata
from bisect import bisect_right
from dataclasses import dataclass, field

CMD = re.compile(r"\\(?:([A-Za-z@]+)(\*?)|(.))", re.S)

DISPLAY_ENVS = {"equation", "align", "gather", "multline", "flalign", "alignat",
                "eqnarray", "displaymath", "math"}
THEOREM_ENVS = {"theorem", "lemma", "corollary", "proposition", "definition", "assumption",
                "claim", "example", "remark", "conjecture", "fact"}
RESULT_KINDS = {"theorem", "lemma", "corollary", "proposition", "claim"}
# For this paper sections are top-level (level=1) and subsections are level=2.
HEADINGS = {"part": -1, "chapter": 0, "section": 1, "subsection": 2, "subsubsection": 3,
            "paragraph": 4, "subparagraph": 5}

WRAP = {"emph": "em", "textit": "em", "textsl": "em", "textbf": "strong", "texttt": "code",
        "textsf": "span class=\"sf\"", "textsc": "span class=\"sc\"", "underline": "u",
        "textup": None, "textrm": None, "textnormal": None, "mbox": None, "text": None,
        "hbox": None, "textmd": None, "fbox": None, "makebox": None, "ensuremath": None}
SWITCH = {"em": "em", "it": "em", "itshape": "em", "sl": "em", "bf": "strong", "bfseries": "strong",
          "tt": "code", "ttfamily": "code", "sf": "span class=\"sf\"", "sffamily": "span class=\"sf\"",
          "sc": "span class=\"sc\"", "scshape": "span class=\"sc\"", "rm": None, "rmfamily": None,
          "normalfont": None, "upshape": None, "small": None, "footnotesize": None,
          "scriptsize": None, "tiny": None, "normalsize": None, "large": None, "Large": None,
          "LARGE": None, "huge": None, "Huge": None}
# command -> number of mandatory arguments to discard
DROP = {"noindent": 0, "medskip": 0, "smallskip": 0, "bigskip": 0, "centering": 0, "newpage": 0,
        "clearpage": 0, "indent": 0, "xspace": 0, "DontPrintSemicolon": 0, "SetAlgoLined": 0,
        "SetAlgoNoLine": 0, "LinesNumbered": 0, "raggedright": 0, "raggedleft": 0, "protect": 0,
        "relax": 0, "allowdisplaybreaks": 0, "hfill": 0, "vfill": 0, "null": 0, "nolinebreak": 0,
        "leavevmode": 0, "frenchspacing": 0, "ignorespaces": 0, "appendix": 0, "phantomsection": 0,
        "maketitle": 0, "tableofcontents": 0, "selectfont": 0, "displaystyle": 0, "nobreak": 0,
        "vspace": 1, "hspace": 1, "arxiv": 1, "color": 1, "pagestyle": 1, "thispagestyle": 1,
        "bibliographystyle": 1, "bibliography": 1, "usepackage": 1, "captionsetup": 1,
        "nocite": 1, "index": 1, "enlargethispage": 1, "addvspace": 1, "SetKwInOut": 2,
        "SetKwInput": 2, "SetKw": 2, "setlength": 2, "setcounter": 2, "addtocounter": 2,
        "addcontentsline": 3, "newtheorem": 2, "SetKwFunction": 2, "SetAlFnt": 1,
        "SetAlCapFnt": 1, "SetKwComment": 3, "vskip": 0}
SYMBOLS = {"LaTeX": "LaTeX", "TeX": "TeX", "S": "§", "P": "¶", "ldots": "…", "dots": "…",
           "textellipsis": "…", "cdots": "⋯", "textendash": "–", "textemdash": "—",
           "quad": "\u2003", "qquad": "\u2003\u2003", "enspace": "\u2002", "ss": "ß", "o": "ø",
           "O": "Ø", "ae": "æ", "AE": "Æ", "i": "ı", "l": "ł", "copyright": "©",
           "textbackslash": "\\", "textasciitilde": "~", "dag": "†", "ddag": "‡",
           "textbullet": "•", "checkmark": "✓", "linebreak": " ", "slash": "/",
           "textquoteright": "'", "textquoteleft": "'", "today": ""}
ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303",
           "=": "\u0304", ".": "\u0307", "u": "\u0306", "v": "\u030c", "H": "\u030b",
           "c": "\u0327", "k": "\u0328", "r": "\u030a"}
ALG_BLOCK = {"For": "for", "ForEach": "for each", "ForAll": "for all", "While": "while",
             "If": "if", "uIf": "if", "ElseIf": "else if", "lIf": "if", "lFor": "for",
             "lForEach": "for each", "lWhile": "while", "uElseIf": "else if"}
TRAILING_PUNCT = re.compile(r"[.,;:!?)]+")
ALG_INDENT_STYLE = "margin-left:0.5em;padding-left:1.5em"
ALG_DO = {"For": "do", "ForEach": "do", "ForAll": "do", "While": "do", "lFor": "do",
          "lForEach": "do", "lWhile": "do"}


def esc(text: str) -> str:
    return html.escape(text, quote=False)


def attr(text: str) -> str:
    return html.escape(text, quote=True)


CALLIGRAPHIC_RE = re.compile(r"\\%(?:\{([^{}]*)\}|([A-Za-z]))")


def expand_calligraphic(text: str) -> str:
    """Expand the paper's `\\def\\%#1{\\mathcal{#1}}`: `\\%F` and `\\%{A}` become `\\mathcal{F}` and
    `\\mathcal{A}`. MathJax would otherwise read `\\%` as a literal percent sign and print `%F`. A real
    percent sign (`\\%` before a digit, space or punctuation) is left alone; newlines are unchanged, so
    line numbers are preserved."""
    return CALLIGRAPHIC_RE.sub(lambda m: "{\\mathcal{" + (m.group(1) if m.group(1) is not None else m.group(2)) + "}}", text)


def mask_comments(text: str) -> str:
    """Replace unescaped % comments by spaces, keeping offsets and newlines."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "\\":
            i += 2
        elif c == "%":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out[i:j] = " " * (j - i)
            i = j
        else:
            i += 1
    return "".join(out)


def blank(text: str) -> str:
    return "".join("\n" if c == "\n" else " " for c in text)


def mask_env(text: str, name: str) -> str:
    pat = re.compile(r"\\begin\{" + re.escape(name) + r"\}(.*?)\\end\{" + re.escape(name) + r"\}", re.S)
    return pat.sub(lambda m: blank(m.group(0)), text)


def skip_ws(s: str, i: int, j: int) -> int:
    while i < j and s[i] in " \t\r\n":
        i += 1
    return i


def read_group(s: str, i: int, j: int):
    """Next argument after whitespace: (content_start, content_end, after)."""
    k = skip_ws(s, i, j)
    if k >= j:
        return k, k, k
    if s[k] == "{":
        depth, p = 1, k + 1
        while p < j:
            c = s[p]
            if c == "\\":
                p += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return k + 1, p, p + 1
            p += 1
        return k + 1, j, j
    if s[k] == "\\":
        m = CMD.match(s, k)
        return k, m.end(), m.end()
    return k, k + 1, k + 1


def read_opt(s: str, i: int, j: int, allow_space: bool = True):
    """Optional [..] argument: (content_start, content_end, after) or None."""
    k = skip_ws(s, i, j) if allow_space else i
    if k >= j or s[k] != "[":
        return None
    depth, p = 0, k + 1
    while p < j:
        c = s[p]
        if c == "\\":
            p += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == "]" and depth == 0:
            return k + 1, p, p + 1
        p += 1
    return None


ENV_TOKEN = re.compile(r"\\(begin|end)\s*\{([^{}]*)\}")


def find_env_end(s: str, i: int, j: int, name: str):
    """Given i just after \\begin{name}, return (body_end, after_end)."""
    depth = 1
    for m in ENV_TOKEN.finditer(s, i, j):
        if m.group(2) != name:
            continue
        depth += 1 if m.group(1) == "begin" else -1
        if depth == 0:
            return m.start(), m.end()
    return j, j


def top_level(s: str, i: int, j: int, token: re.Pattern):
    """Positions in s[i:j] matching token outside braces and nested environments."""
    hits, depth, p = [], 0, i
    while p < j:
        if depth == 0:
            m = token.match(s, p)
            if m and m.end() > p:
                hits.append((m.start(), m.end()))
                p = m.end()
                continue
        c = s[p]
        if c == "\\":
            m = ENV_TOKEN.match(s, p)
            if m and m.group(1) == "begin":
                _, after = find_env_end(s, m.end(), j, m.group(2))
                p = after
                continue
            p += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        p += 1
    return hits


ROW_SEP = re.compile(r"\\\\\*?(?:\s*\[[^\]]*\])?")
ITEM = re.compile(r"\\item(?![A-Za-z@])")
CELL = re.compile(r"(?<!\\)&")
CAPTION = re.compile(r"\\caption(?![A-Za-z@])")


def find_closing(s: str, i: int, j: int, closer: str) -> int:
    """Position of an unescaped closer (\\) or \\]) from i."""
    p = i
    while p < j - 1:
        if s[p] == "\\":
            if s[p + 1] == closer:
                return p
            p += 2
            continue
        p += 1
    return -1


def find_dollar(s: str, i: int, j: int, double: bool) -> int:
    p = i
    while p < j:
        c = s[p]
        if c == "\\":
            p += 2
            continue
        if c == "$":
            if not double:
                return p
            if p + 1 < j and s[p + 1] == "$":
                return p
        p += 1
    return -1


@dataclass
class Block:
    kind: str
    html: str
    file: str | None = None
    line_start: int | None = None
    line_end: int | None = None
    entry: dict | None = None
    labels: list = field(default_factory=list)
    level: int | None = None
    number: str | None = None
    title: str = ""
    in_proof: bool = False
    anchor: str | None = None
    tex: str = ""
    children: list = field(default_factory=list)  # nested numbered/labelled blocks, flattened


def _balanced_outer(t: str) -> bool:
    """True when t is "( ... )" and the first "(" closes at the last character."""
    depth = 0
    for i, ch in enumerate(t):
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0 and i < len(t) - 1:
            return False
    return depth == 0


def html_id(raw: str) -> str:
    """A valid HTML id fragment: every character outside [A-Za-z0-9:_.-] becomes `_`."""
    return re.sub(r"[^A-Za-z0-9:_.\-]", "_", raw)


def label_id(label: str) -> str:
    return "L-" + html_id(label)


class FileConverter:
    def __init__(self, book, file: str, text: str):
        self.book = book
        self.file = file
        self.raw = text
        masked = mask_comments(text)
        for env in ("comment",):
            masked = mask_env(masked, env)
        self.text = masked
        self.newlines = [m.start() for m in re.finditer("\n", text)]
        self.depth = 0

    # positions -----------------------------------------------------------
    def line(self, s: str, pos: int):
        if s is not self.text:
            return None
        return bisect_right(self.newlines, pos - 1) + 1

    def tex_lines(self, a: int, b: int) -> str:
        la, lb = self.line(self.text, a), self.line(self.text, b)
        return "\n".join(self.raw.splitlines()[la - 1:lb])

    # conversion ----------------------------------------------------------
    def convert(self):
        return self.conv(self.text, 0, len(self.text))

    def conv(self, s: str, i: int, j: int, alg: bool = False) -> list:
        parts: list = []
        p = i
        run = re.compile(r"[^\\$\{\}~\n`'\-&<>\"\\[\\]]+")
        while p < j:
            c = s[p]
            m = run.match(s, p, j)
            if m:
                parts.append(("i", esc(re.sub(r"[ \t\r]+", " ", m.group(0)))))
                p = m.end()
                continue
            if c == "\\":
                p = self.command(s, p, j, parts, alg)
            elif c == "$":
                double = p + 1 < j and s[p + 1] == "$"
                start = p + (2 if double else 1)
                end = find_dollar(s, start, j, double)
                if end < 0:
                    parts.append(("i", "$"))
                    p += 1
                    continue
                if double:
                    parts.append(("b", self.display(s, "$$", start, end, p, end + 2)))
                    p = end + 2
                else:
                    p = self.math_with_punct(s, start, end, end + 1, j, parts)
            elif c == "{":
                a, b, after = read_group(s, p, j)
                parts.extend(self.conv(s, a, b, alg))
                p = after
            elif c == "}":
                p += 1
            elif c == "\n":
                bl = re.compile(r"\n[ \t\r]*\n(?:[ \t\r]*\n)*").match(s, p, j)
                if bl:
                    parts.append(("p",))
                    p = bl.end()
                else:
                    parts.append(("i", " "))
                    p += 1
            elif c == "~":
                parts.append(("i", "&nbsp;"))
                p += 1
            elif c == "`":
                if s.startswith("``", p):
                    parts.append(("i", "\u201c"))
                    p += 2
                else:
                    parts.append(("i", "\u2018"))
                    p += 1
            elif c == "'":
                if s.startswith("''", p):
                    parts.append(("i", "\u201d"))
                    p += 2
                else:
                    parts.append(("i", "\u2019"))
                    p += 1
            elif c == "-":
                if s.startswith("---", p):
                    parts.append(("i", "\u2014"))
                    p += 3
                elif s.startswith("--", p):
                    parts.append(("i", "\u2013"))
                    p += 2
                else:
                    parts.append(("i", "-"))
                    p += 1
            else:
                parts.append(("i", esc(c)))
                p += 1
        return parts

    # helpers to turn parts into html --------------------------------------
    def inline(self, parts: list) -> str:
        out = []
        for part in parts:
            if part[0] == "i":
                out.append(part[1])
            elif part[0] == "b":
                out.append(part[1].html)
            elif part[0] == "p":
                out.append(" ")
        return "".join(out).strip()

    def flow(self, parts: list) -> str:
        return "".join(b.html for b in assemble(parts))

    def alg_html(self, parts: list) -> str:
        out = []
        for part in parts:
            if part[0] == "i":
                out.append(part[1])
            elif part[0] == "b":
                out.append(part[1].html)
            elif part[0] == "p":
                out.append("<br>")
        return "".join(out)

    def arg(self, s, p, j, alg=False):
        a, b, after = read_group(s, p, j)
        return self.inline(self.conv(s, a, b, alg)), after

    def raw_arg(self, s, p, j):
        a, b, after = read_group(s, p, j)
        return s[a:b].strip(), after

    # commands --------------------------------------------------------------
    def command(self, s: str, p: int, j: int, parts: list, alg: bool) -> int:
        m = CMD.match(s, p)
        if not m:
            parts.append(("i", "\\"))
            return p + 1
        name, star, sym = m.group(1), m.group(2), m.group(3)
        q = m.end()
        if name is None:
            return self.symbol(sym, s, q, j, parts, alg)
        if name == "begin":
            return self.environment(s, p, q, j, parts, alg)
        if name == "end":
            _, _, after = read_group(s, q, j)
            return after
        if name in HEADINGS:
            return self.heading(name, bool(star), s, p, q, j, parts)
        if name in ("ba", "ban", "be", "ben", "bes", "besn", "bg", "bgn", "bm", "bmn"):
            m_ee = re.search(r"\\ee\b", s[q:j])
            if m_ee:
                env_map = {
                    "ba": "align*", "ban": "align",
                    "be": "equation*", "ben": "equation",
                    "bes": "align*", "besn": "align",
                    "bg": "gather*", "bgn": "gather",
                    "bm": "multline*", "bmn": "multline",
                }
                body_start = q
                body_end = q + m_ee.start()
                after = q + m_ee.end()
                blk = self.display(s, env_map[name], body_start, body_end, p, after)
                parts.append(("b", blk))
                return after
        if name == "label":
            label, after = self.raw_arg(s, q, j)
            lid = label_id(label)
            anchors = f'<span class="anchor" id="{attr(lid)}"></span>'
            if lid != label:
                anchors += f'<span class="anchor" id="{attr(label)}"></span>'
            parts.append(("i", anchors))
            return after
        if name in ("ref", "eqref", "cref", "Cref", "autoref", "pageref", "nameref"):
            raw, after = self.raw_arg(s, q, j)
            refs = [r.strip() for r in raw.split(",") if r.strip()]
            parts.append(("i", ", ".join(f"@@REF|t|{name}|{r}@@" for r in refs)))
            return after
        if name.startswith("cite"):
            return self.cite(name, star, s, q, j, parts)
        if name in WRAP:
            a, b, after = read_group(s, q, j)
            inner = self.inline(self.conv(s, a, b, alg))
            tag = WRAP[name]
            pre = " " if s[a:b][:1].isspace() and inner else ""
            post = " " if s[a:b][-1:].isspace() and inner else ""
            parts.append(("i", pre + (f"<{tag}>{inner}</{tag.split()[0]}>" if tag else inner) + post))
            return after
        if name in SWITCH:
            rest = self.conv(s, q, j, alg)
            tag = SWITCH[name]
            if not tag:
                parts.extend(rest)
            else:
                close = tag.split()[0]
                for part in rest:
                    parts.append(("i", f"<{tag}>{part[1]}</{close}>") if part[0] == "i" else part)
            return j
        if name in SYMBOLS:
            parts.append(("i", SYMBOLS[name]))
            return q
        if name == "par":
            parts.append(("p",))
            return q
        if name == "newline":
            parts.append(("i", "<br>"))
            return q
        if name in ACCENTS:
            return self.accent(name, s, q, j, parts)
        if name in ("newcommand", "renewcommand", "providecommand", "DeclareMathOperator", "def"):
            return self.skip_definition(name, s, q, j)
        if name in DROP:
            after = q
            if name == "usepackage":
                o = read_opt(s, after, j)
                after = o[2] if o else after
            for _ in range(DROP[name]):
                _, _, after = read_group(s, after, j)
            return after
        if name in ("book",):
            a, b, after = read_group(s, q, j)
            parts.extend(self.conv(s, a, b, alg))
            return after
        if name in ("textcolor", "colorbox", "raisebox"):
            _, _, after = read_group(s, q, j)
            a, b, after = read_group(s, after, j)
            parts.extend(self.conv(s, a, b, alg))
            return after
        if name == "footnote":
            inner, after = self.arg(s, q, j)
            n = self.book.next_footnote()
            parts.append(("i", f'<span class="fn" tabindex="0"><sup>{n}</sup>'
                                f'<span class="fn-text" role="note">{inner}</span></span>'))
            return after
        if name == "url":
            url, after = self.raw_arg(s, q, j)
            parts.append(("i", f'<a href="{attr(url)}">{esc(url)}</a>'))
            return after
        if name == "href":
            url, after = self.raw_arg(s, q, j)
            text, after = self.arg(s, after, j)
            parts.append(("i", f'<a href="{attr(url)}">{text}</a>'))
            return after
        if name in ("input", "include"):
            path, after = self.raw_arg(s, q, j)
            parts.extend(self.book.include(path))
            return after
        if name == "includegraphics":
            o = read_opt(s, q, j)
            path, after = self.raw_arg(s, o[2] if o else q, j)
            parts.append(("i", self.book.image(path)))
            return after
        if name == "caption":
            o = read_opt(s, q, j)
            text, after = self.arg(s, o[2] if o else q, j)
            parts.append(("i", f'<span class="caption">{text}</span>'))
            return after
        if name == "item":
            o = read_opt(s, q, j, allow_space=False)
            if o:
                parts.append(("i", f"<strong>{self.inline(self.conv(s, o[0], o[1]))}</strong> "))
                return o[2]
            parts.append(("i", "• "))
            return q
        alg_result = self.algorithm_command(name, star, s, q, j, parts)
        if alg_result is not None:
            return alg_result
        macro = self.book.macros.get(name)
        if macro is not None:
            return self.expand(name, macro, s, q, j, parts, alg)
        self.book.unknown[name] = self.book.unknown.get(name, 0) + 1
        return q

    def symbol(self, sym: str, s: str, q: int, j: int, parts: list, alg: bool) -> int:
        if sym == "\\":
            if q < j and s[q] == "*":
                q += 1
            o = read_opt(s, q, j, allow_space=False)
            parts.append(("i", "<br>"))
            return o[2] if o else q
        if sym == "[":
            end = find_closing(s, q, j, "]")
            if end < 0:
                return q
            parts.append(("b", self.display(s, "\\[", q, end, q - 2, end + 2)))
            return end + 2
        if sym == "(":
            end = find_closing(s, q, j, ")")
            if end < 0:
                return q
            return self.math_with_punct(s, q, end, end + 2, j, parts)
        if sym in "%&$#_{}":
            parts.append(("i", esc(sym)))
            return q
        if sym in ACCENTS:
            return self.accent(sym, s, q, j, parts)
        if sym == ";" and alg:
            parts.append(("i", "<br>"))
            return q
        if sym in " \n\t":
            parts.append(("i", " "))
            return q
        if sym == ",":
            parts.append(("i", "\u2009"))
            return q
        if sym in ";:":
            parts.append(("i", "\u2005"))
            return q
        return q  # \! \/ \- \@ and others

    def accent(self, name: str, s: str, q: int, j: int, parts: list) -> int:
        a, b, after = read_group(s, q, j)
        base = s[a:b].strip()
        if base.startswith("\\"):
            base = {"\\i": "i", "\\j": "j"}.get(base, base[1:])
        if base:
            text = unicodedata.normalize("NFC", base[0] + ACCENTS[name] + base[1:])
        else:
            text = ""
        parts.append(("i", esc(text)))
        return after

    def skip_definition(self, name: str, s: str, q: int, j: int) -> int:
        if q < j and s[q] == "*":
            q += 1
        if name == "def":
            m = re.compile(r"\s*\\[A-Za-z@]+[^{]*").match(s, q, j)
            q = m.end() if m else q
            _, _, after = read_group(s, q, j)
            return after
        _, _, after = read_group(s, q, j)
        for _ in range(2):
            o = read_opt(s, after, j)
            if o:
                after = o[2]
        _, _, after = read_group(s, after, j)
        return after

    def expand(self, name: str, macro, s: str, q: int, j: int, parts: list, alg: bool) -> int:
        nargs, default, body = macro
        if body.strip() == "#1" and nargs == 1 and default is None:
            a, b, after = read_group(s, q, j)
            parts.extend(self.conv(s, a, b, alg))
            return after
        args, after = [], q
        if nargs and default is not None:
            o = read_opt(s, after, j)
            if o:
                args.append(s[o[0]:o[1]])
                after = o[2]
            else:
                args.append(default)
        while len(args) < nargs:
            a, b, after = read_group(s, after, j)
            args.append(s[a:b])
        text = re.sub(r"#(\d)", lambda m: args[int(m.group(1)) - 1] if int(m.group(1)) <= len(args) else "", body)
        if self.depth > 20:
            return after
        self.depth += 1
        try:
            parts.extend(self.conv(text, 0, len(text), alg))
        finally:
            self.depth -= 1
        return after

    def cite(self, name: str, star: str, s: str, q: int, j: int, parts: list) -> int:
        opts, after = [], q
        for _ in range(2):
            o = read_opt(s, after, j)
            if not o:
                break
            opts.append(self.inline(self.conv(s, o[0], o[1])))
            after = o[2]
        keys, after = self.raw_arg(s, after, j)
        keys = [k.strip() for k in keys.split(",") if k.strip()]
        parts.append(("i", self.book.cite(name, keys, opts)))
        return after

    # headings ------------------------------------------------------------
    def heading(self, name: str, starred: bool, s: str, p: int, q: int, j: int, parts: list) -> int:
        o = read_opt(s, q, j)
        a, b, after = read_group(s, o[2] if o else q, j)
        title = self.inline(self.conv(s, a, b))
        level = HEADINGS[name]
        if level >= 4:
            parts.append(("p",))
            parts.append(("i", f'<strong class="runin">{title}</strong> '))
            return after
        line = self.line(s, p)
        entry = self.book.inventory_at(self.file, line, ("heading",)) if line else None
        number = None if starred or not entry else entry.get("number")
        anchor = f"sec-{number}" if number else f"sec-{self.file.rsplit('/', 1)[-1][:-4]}-{line}"
        blk = Block("heading", "", self.file, line, line, entry, list(entry.get("labels", [])) if entry else [],
                    level, number, title, anchor=anchor)
        tag = f"h{min(level + 1, 4)}" if level >= 0 else "h1"
        num = f'<span class="secnum">{esc(number)}</span> ' if number else ""
        blk.html = f'<{tag} class="h-l{level}" id="{attr(anchor)}">{num}{title}</{tag}>'
        parts.append(("b", blk))
        return after

    # math ------------------------------------------------------------------
    def clean_math(self, m: str) -> str:
        m = mathjax_compat(m)
        m = re.sub(r"\\label\s*\{[^{}]*\}", "", m)
        m = re.sub(r"\\(?:nonumber|notag)(?![A-Za-z])", "", m)

        def ref(x):
            kind = x.group(1)
            return "".join(f"\\text{{@@REF|m|{kind}|{r.strip()}@@}}" for r in x.group(2).split(",") if r.strip())

        m = re.sub(r"\\(eqref|ref|cref|Cref)\s*\{([^{}]*)\}", ref, m)
        m = re.sub(r"\\cite[a-z]*\*?(?:\[[^\]]*\])*\s*\{([^{}]*)\}",
                   lambda x: "\\text{" + self.book.cite_plain(x.group(1)) + "}", m)
        m = re.sub(r"\\(arxiv)\s*\{[^{}]*\}", "", m)
        return m

    def math_with_punct(self, s: str, a: int, b: int, after: int, j: int, parts: list) -> int:
        """Inline math s[a:b]; punctuation right after it is kept on the same line."""
        math = self.inline_math(s[a:b])
        m = TRAILING_PUNCT.match(s, after, j)
        if not m:
            parts.append(("i", math))
            return after
        parts.append(("i", f'<span class="nobr">{math}{esc(m.group(0))}</span>'))
        return m.end()

    def inline_math(self, m: str) -> str:
        return f'<span class="tex2jax_process">\\({esc(self.clean_math(m))}\\)</span>'

    def display(self, s: str, env: str, a: int, b: int, start: int, end: int) -> Block:
        body = s[a:b]
        line = self.line(s, start)
        line_end = self.line(s, end - 1)
        entry = self.book.inventory_at(self.file, line, ("display",)) if line else None
        labels, tags_ok = [], False
        base = env.rstrip("*")
        rows_meta = entry.get("rows", []) if entry else []
        if entry:
            labels = list(dict.fromkeys([l for row in rows_meta for l in row.get("labels", [])]
                                        + list(entry.get("labels", []))))
        else:
            labels = re.findall(r"\\label\s*\{([^{}]*)\}", body)
        numbers = [row.get("number") for row in rows_meta]
        if env in ("$$", "\\["):
            tex = self.clean_math(body)
            math = f"\\[{tex}\\]"
            tags_ok = True
        else:
            if any(numbers):
                seps = top_level(body, 0, len(body), ROW_SEP)
                pieces, last = [], 0
                for sa, sb in seps:
                    pieces.append([body[last:sa], body[sa:sb]])
                    last = sb
                pieces.append([body[last:], ""])
                if len(pieces) == len(numbers) + 1 and not pieces[-1][0].strip():
                    numbers = numbers + [None]
                if len(pieces) == len(numbers):
                    tags_ok = True
                    out = []
                    for (text, sep), num in zip(pieces, numbers):
                        tag = f"\\tag{{{num}}}" if num else ""
                        out.append(text + tag + sep)
                    body = "".join(out)
                else:
                    self.book.warn(f"{self.file}:{line}: {len(pieces)} rows vs {len(numbers)} inventory rows; numbers omitted")
            else:
                tags_ok = True
            starred = base if base in ("eqnarray", "displaymath", "math") else base + "*"
            if base in ("displaymath", "math"):
                math = f"\\[{self.clean_math(body)}\\]"
            else:
                opt = ""
                if base == "alignat":
                    m = re.match(r"\s*\{[^{}]*\}", body)
                    if m:
                        opt, body = m.group(0), body[m.end():]
                math = f"\\begin{{{starred}}}{opt}{self.clean_math(body)}\\end{{{starred}}}"
        anchors = "".join(f'<span class="anchor" id="{attr(label_id(l))}"></span>' for l in labels)
        html_ = f'<div class="md tex2jax_process">{anchors}{esc(math)}</div>'
        blk = Block("display", html_, self.file, line, line_end, entry, labels)
        if not tags_ok:
            blk.html = html_.replace('class="md ', 'class="md untagged ')
        return blk

    # environments -----------------------------------------------------------
    def environment(self, s: str, p: int, q: int, j: int, parts: list, alg: bool) -> int:
        a, b, after = read_group(s, q, j)
        env = s[a:b].strip()
        body_start = after
        body_end, env_end = find_env_end(s, after, j, env)
        base = env.rstrip("*")
        line = self.line(s, p)
        if base in DISPLAY_ENVS:
            parts.append(("b", self.display(s, env, body_start, body_end, p, env_end)))
        elif base == "subequations":
            parts.extend(self.conv(s, body_start, body_end, alg))
        elif base in THEOREM_ENVS:
            parts.append(("b", self.theorem(base, s, p, body_start, body_end, env_end, line)))
        elif base == "proof":
            o = read_opt(s, body_start, body_end)
            head = self.inline(self.conv(s, o[0], o[1])) if o else "Proof"
            start = o[2] if o else body_start
            pentry = self.book.inventory_at(self.file, line, ("proof",)) if line else None
            panchor = f'<span class="anchor" id="{attr("E-" + html_id(pentry["id"]))}"></span>' if pentry else ""
            parts.append(("proof_on",))
            parts.append(("p",))
            parts.append(("i", f'{panchor}<em class="proof-head">{head}.</em> '))
            parts.extend(self.conv(s, start, body_end, alg))
            parts.append(("i", ' <span class="qed" aria-label="end of proof">∎</span>'))
            parts.append(("proof_off",))
        elif base in ("itemize", "enumerate", "description"):
            parts.append(("b", self.list_env(base, s, body_start, body_end, alg)))
        elif base in ("algorithm", "algorithm2e"):
            parts.append(("b", self.algorithm(s, p, body_start, body_end, env_end, line)))
        elif base in ("algorithmic",):
            o = read_opt(s, body_start, body_end)
            parts.extend(self.conv(s, o[2] if o else body_start, body_end, True))
        elif base in ("figure", "table"):
            parts.append(("b", self.figure(base, s, p, body_start, body_end, env_end, line)))
        elif base == "subfigure":
            o = read_opt(s, body_start, body_end)
            _, _, start = read_group(s, o[2] if o else body_start, body_end)
            inner = self.inline(self.conv(s, start, body_end))
            self.subfig = getattr(self, "subfig", 0) + 1
            letter = "(" + "abcdefghij"[(self.subfig - 1) % 10] + ") "
            inner = inner.replace('<span class="caption">', '<span class="caption">' + letter, 1)
            parts.append(("i", f'<span class="subfigure">{inner}</span>'))
        elif base in ("center", "flushleft", "flushright", "quote", "quotation", "minipage",
                      "acknowledgements", "abstract"):
            start = body_start
            if base == "minipage":
                o = read_opt(s, start, body_end)
                _, _, start = read_group(s, o[2] if o else start, body_end)
            inner = self.flow(self.conv(s, start, body_end, alg))
            parts.append(("b", Block("box", f'<div class="{base}">{inner}</div>', self.file, line)))
        elif base in ("tabular", "array"):
            parts.append(("b", self.tabular(s, body_start, body_end)))
        else:
            self.book.unknown["env:" + env] = self.book.unknown.get("env:" + env, 0) + 1
            parts.extend(self.conv(s, body_start, body_end, alg))
        return env_end

    def theorem(self, kind: str, s: str, p: int, a: int, b: int, end: int, line) -> Block:
        entry = self.book.inventory_at(self.file, line, (kind,)) if line else None
        o = read_opt(s, a, b)
        title = self.inline(self.conv(s, o[0], o[1])) if o else ""
        start = o[2] if o else a
        number = entry.get("number") if entry else None
        name = self.book.env_title(kind)
        head = f'<strong>{esc(name)}{(" " + esc(number)) if number else ""}</strong>'
        if title:
            plain = re.sub(r"<[^>]+>", "", title).strip()
            head += f" {title}" if plain.startswith("(") and _balanced_outer(plain) else f" ({title})"
        body_parts = self.conv(s, start, b)
        inner = [("i", f'<span class="env-head">{head}.</span> ')] + body_parts
        labels = list(entry.get("labels", [])) if entry else re.findall(r"\\label\s*\{([^{}]*)\}", s[a:b])
        anchor = f"E-{html_id(entry['id'])}" if entry else None
        html_ = (f'<div class="env env-{kind}"{f" id={chr(34)}{attr(anchor)}{chr(34)}" if anchor else ""}>'
                 f'{self.flow(inner)}</div>')
        blk = Block("env", html_, self.file, line, self.line(s, end - 1), entry, labels,
                    number=number, title=title, anchor=anchor)
        blk.tex = self.tex_lines(p, end - 1)
        blk.children = collect(body_parts)
        blk.level = None
        blk.kind_name = kind  # type: ignore[attr-defined]
        return blk

    def list_env(self, kind: str, s: str, a: int, b: int, alg: bool) -> Block:
        o = read_opt(s, a, b)
        start = o[2] if o else a
        hits = top_level(s, start, b, ITEM)
        items, children = [], []
        for k, (ia, ib) in enumerate(hits):
            iend = hits[k + 1][0] if k + 1 < len(hits) else b
            label = ""
            o = read_opt(s, ib, iend, allow_space=False)
            content_start = ib
            if o:
                label = self.inline(self.conv(s, o[0], o[1]))
                content_start = o[2]
            item_parts = self.conv(s, content_start, iend, alg)
            children.extend(collect(item_parts))
            body = self.flow(item_parts)
            if kind == "description" or label:
                tag = f'<span class="item-label">{label}</span>'
                body = body.replace("<p>", "<p>" + tag, 1) if body.startswith("<p>") else tag + body
                items.append(f'<li class="labelled">{body}</li>')
            else:
                items.append(f"<li>{body}</li>")
        tag = "ol" if kind == "enumerate" else "ul"
        blk = Block("list", f'<{tag} class="{kind}">{"".join(items)}</{tag}>', self.file, self.line(s, a))
        blk.children = children
        return blk

    def split_caption(self, s: str, a: int, b: int):
        hits = top_level(s, a, b, CAPTION)
        if not hits:
            return None, [(a, b)]
        m = type("M", (), {"start": lambda self_: hits[0][0], "end": lambda self_: hits[0][1]})()
        o = read_opt(s, m.end(), b)
        ca, cb, after = read_group(s, o[2] if o else m.end(), b)
        cap = self.inline(self.conv(s, ca, cb))
        return cap, [(a, m.start()), (after, b)]

    def algorithm(self, s: str, p: int, a: int, b: int, end: int, line) -> Block:
        entry = self.book.inventory_at(self.file, line, ("algorithm",)) if line else None
        o = read_opt(s, a, b)
        start = o[2] if o else a
        cap, ranges = self.split_caption(s, start, b)
        parts = []
        for ra, rb in ranges:
            parts.extend(self.conv(s, ra, rb, True))
        body = self.alg_html(parts)
        body = re.sub(r"^\s*((?:<span class=\"anchor\"[^>]*></span>\s*)*)(\\s|<br>)+", r"\1", body)
        body = re.sub(r'(<div class="alg-indent">)(\s|<br>)+', r"\1", body)
        body = re.sub(r"(\s|<br>)+(</div>)", r"\2", body)
        body += "</div>" * max(0, body.count("<div") - body.count("</div>"))
        body = body.replace('<div class="alg-indent">', f'<div class="alg-indent" style="{ALG_INDENT_STYLE}">')
        number = entry.get("number") if entry else None
        anchor = f"E-{html_id(entry['id'])}" if entry else None
        labels = list(entry.get("labels", [])) if entry else []
        head = f'<strong>Algorithm{(" " + esc(number)) if number else ""}</strong>'
        html_ = (f'<figure class="algorithm"{f" id={chr(34)}{attr(anchor)}{chr(34)}" if anchor else ""}>'
                 f'<figcaption>{head} {cap or ""}</figcaption><div class="alg-body">{body}</div></figure>')
        blk = Block("algorithm", html_, self.file, line, self.line(s, end - 1), entry, labels,
                    number=number, title=cap or "", anchor=anchor)
        blk.tex = self.tex_lines(p, end - 1)
        return blk

    def algorithm_command(self, name, star, s, q, j, parts):
        if name in ALG_BLOCK:
            cond, after = self.arg(s, q, j, True)
            a, b, after = read_group(s, after, j)
            body = self.alg_html(self.conv(s, a, b, True))
            word = ALG_BLOCK[name]
            tail = f' <b>{ALG_DO[name]}</b>' if name in ALG_DO else (" <b>then</b>" if "If" in name else "")
            if name.startswith("l"):
                parts.append(("i", f'<div class="alg-line"><b>{word}</b> {cond}{tail} {body}</div>'))
            else:
                parts.append(("i", f'<div class="alg-line"><b>{word}</b> {cond}{tail}</div>'
                                    f'<div class="alg-indent">{body}</div>'))
            return after
        if name in ("Else", "uElse", "lElse"):
            a, b, after = read_group(s, q, j)
            body = self.alg_html(self.conv(s, a, b, True))
            parts.append(("i", f'<div class="alg-line"><b>else</b></div><div class="alg-indent">{body}</div>'))
            return after
        if name == "eIf":
            cond, after = self.arg(s, q, j, True)
            a, b, after = read_group(s, after, j)
            yes = self.alg_html(self.conv(s, a, b, True))
            a, b, after = read_group(s, after, j)
            no = self.alg_html(self.conv(s, a, b, True))
            parts.append(("i", f'<div class="alg-line"><b>if</b> {cond} <b>then</b></div>'
                                f'<div class="alg-indent">{yes}</div><div class="alg-line"><b>else</b></div>'
                                f'<div class="alg-indent">{no}</div><div class="alg-line"><b>end</b></div>'))
            return after
        if name in ("KwIn", "KwOut", "KwData", "KwResult", "KwRet", "Return", "KwTo"):
            text, after = self.arg(s, q, j, True)
            word = {"KwIn": "Input:", "KwOut": "Output:", "KwData": "Data:", "KwResult": "Result:",
                    "KwRet": "return", "Return": "return", "KwTo": "to"}[name]
            parts.append(("i", f"<b>{word}</b> {text}<br>"))
            return after
        if name in ("tcc", "tcp", "tcc*", "tcp*"):
            if star:
                o = read_opt(s, q, j)
                q = o[2] if o else q
            text, after = self.arg(s, q, j, True)
            parts.append(("i", f'<span class="alg-comment">{text}</span><br>'))
            return after
        if name in ("STATE", "State", "Statex"):
            parts.append(("i", "<br>"))
            return q
        if name in ("FOR", "For_", "FORALL", "WHILE", "IF", "ELSIF"):
            cond, after = self.arg(s, q, j, True)
            word = {"FOR": "for", "FORALL": "for all", "WHILE": "while", "IF": "if", "ELSIF": "else if"}.get(name, "for")
            tail = "do" if name in ("FOR", "FORALL", "WHILE") else "then"
            close = '</div>' if name == "ELSIF" else ""
            parts.append(("i", f'{close}<div class="alg-line"><b>{word}</b> {cond} <b>{tail}</b></div><div class="alg-indent">'))
            return after
        if name in ("ENDFOR", "ENDWHILE", "ENDIF"):
            word = {"ENDFOR": "end for", "ENDWHILE": "end while", "ENDIF": "end if"}[name]
            parts.append(("i", f'</div><div class="alg-line"><b>{word}</b></div>'))
            return q
        if name == "ELSE":
            parts.append(("i", '</div><div class="alg-line"><b>else</b></div><div class="alg-indent">'))
            return q
        if name in ("REQUIRE", "ENSURE", "RETURN"):
            word = {"REQUIRE": "Require:", "ENSURE": "Ensure:", "RETURN": "return"}[name]
            parts.append(("i", f"<br><b>{word}</b> "))
            return q
        if name == "COMMENT":
            text, after = self.arg(s, q, j, True)
            parts.append(("i", f' <span class="alg-comment">{text}</span>'))
            return after
        return None

    def figure(self, kind: str, s: str, p: int, a: int, b: int, end: int, line) -> Block:
        entry = self.book.inventory_at(self.file, line, ("figure",)) if line else None
        self.subfig = 0
        o = read_opt(s, a, b)
        start = o[2] if o else a
        cap, ranges = self.split_caption(s, start, b)
        parts = []
        for ra, rb in ranges:
            parts.extend(self.conv(s, ra, rb))
        body = self.inline(parts)
        number = entry.get("number") if entry else None
        anchor = f"E-{html_id(entry['id'])}" if entry else None
        word = "Figure" if kind == "figure" else "Table"
        head = f'<strong>{word}{(" " + esc(number)) if number else ""}.</strong>'
        html_ = (f'<figure class="figure"{f" id={chr(34)}{attr(anchor)}{chr(34)}" if anchor else ""}>'
                 f'<div class="figure-body">{body}</div>'
                 f'<figcaption>{head} {cap or ""}</figcaption></figure>')
        return Block("figure", html_, self.file, line, self.line(s, end - 1), entry,
                     list(entry.get("labels", [])) if entry else [], number=number, anchor=anchor)

    def tabular(self, s: str, a: int, b: int) -> Block:
        _, _, start = read_group(s, a, b)  # column spec
        rows = []
        last = start
        bounds = top_level(s, start, b, ROW_SEP) + [(b, b)]
        for ra, rb in bounds:
            seg = (last, ra)
            last = rb
            text = s[seg[0]:seg[1]]
            if not re.sub(r"\\(hline|toprule|midrule|bottomrule|cline\{[^}]*\})", "", text).strip():
                continue
            cells = top_level(s, seg[0], seg[1], CELL)
            cuts = [seg[0]] + [c[1] for c in cells]
            ends = [c[0] for c in cells] + [seg[1]]
            tds = []
            for ca, cb in zip(cuts, ends):
                sub = re.sub(r"\\(hline|toprule|midrule|bottomrule)", " ", s[ca:cb])
                tds.append(f"<td>{self.inline(self.conv(sub, 0, len(sub)))}</td>")
            rows.append(f"<tr>{''.join(tds)}</tr>")
        return Block("table", f'<div class="table-wrap"><table>{"".join(rows)}</table></div>',
                     self.file, self.line(s, a))


MATHOP_TOKEN = re.compile(r"\\mathop\s*(\\(?:mathbb|mathrm|mathsf|mathcal|mathbf|mathds|operatorname)\s*\{[^{}]*\})")


def mathjax_compat(m: str) -> str:
    """TeX accepts `\\mathop\\mathbb{E}` (one-token argument); MathJax needs braces."""
    return MATHOP_TOKEN.sub(r"\\mathop{\1}", m)


def collect(parts: list) -> list:
    """Numbered or labelled blocks inside parts, with their own descendants, in order."""
    out = []
    for part in parts:
        if part[0] == "b":
            b = part[1]
            if b.kind in ("env", "algorithm", "display", "figure"):
                out.append(b)
            out.extend(b.children)
    return out


def assemble(parts: list, file_name: str | None = None) -> list:
    """Group inline parts into paragraphs; keep blocks; mark proof regions."""
    blocks, cur, depth = [], [], 0

    def flush():
        text = "".join(cur).strip()
        cur.clear()
        labels = re.findall(r'<span class="anchor" id="([^"]+)">', text)
        for l in list(labels):
            if l.startswith("L-") and l[2:].isdigit():
                labels.append(l[2:])
        if re.sub(r'<span class="anchor"[^>]*></span>|&nbsp;|\s', "", text):
            blocks.append(Block("p", f"<p>{text}</p>", file=file_name, labels=labels, in_proof=depth > 0))
        elif text:
            blocks.append(Block("p", text, file=file_name, labels=labels, in_proof=depth > 0))

    for part in parts:
        tag = part[0]
        if tag == "i":
            cur.append(part[1])
        elif tag == "p":
            flush()
        elif tag == "b":
            flush()
            blk = part[1]
            blk.in_proof = blk.in_proof or depth > 0
            blocks.append(blk)
        elif tag == "proof_on":
            flush()
            depth += 1
        elif tag == "proof_off":
            flush()
            depth = max(0, depth - 1)
    flush()
    return blocks


def parse_macros(text: str) -> dict:
    """\\newcommand-style definitions: name -> (nargs, default, body)."""
    out = {}
    s = mask_comments(text)
    for m in re.finditer(r"\\(newcommand|renewcommand|providecommand|DeclareMathOperator)(\*?)", s):
        q = m.end()
        a, b, after = read_group(s, q, len(s))
        name = s[a:b].strip().lstrip("\\")
        if not re.fullmatch(r"[A-Za-z@]+", name):
            continue
        nargs, default = 0, None
        if m.group(1) == "DeclareMathOperator":
            a, b, after = read_group(s, after, len(s))
            op = "operatorname*" if m.group(2) else "operatorname"
            out[name] = (0, None, f"\\{op}{{{s[a:b]}}}")
            continue
        o = read_opt(s, after, len(s))
        if o:
            nargs = int(s[o[0]:o[1]].strip() or 0)
            after = o[2]
            o = read_opt(s, after, len(s))
            if o:
                default = s[o[0]:o[1]]
                after = o[2]
        a, b, after = read_group(s, after, len(s))
        out[name] = (nargs, default, s[a:b])
    return out
