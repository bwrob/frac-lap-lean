#!/usr/bin/env python3
"""Generate the "Knowledge" section of the documentation site.

For every chapter ``blueprint/src/<Path>.tex`` (ordered as in ``content.tex``) this writes
``docs/knowledge/<Path>.md``. Each blueprint node (definition, theorem, lemma, ...) becomes a
section with three linked tabs: the rendered **Blueprint** statement and proof, the **Lean**
source of the declarations named in ``\\lean{...}``, and the raw **LaTeX source**. Because the
tabs are linked (``content.tabs.link``), choosing "Lean" once switches every node on the site.

It also writes ``docs/knowledge/index.md`` (progress table), ``docs/knowledge/bibliography.md``
(from ``blueprint/src/references.bib``) and rewrites the generated block of ``zensical.toml``'s
``nav``. ``--check`` verifies that the committed nav block is current.
"""

from __future__ import annotations

import fnmatch
import re
import tomllib
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Annotated, Any

import typer
from logsetup import init as init_logging

app = typer.Typer(add_completion=False, help=__doc__)

ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT = ROOT / "blueprint" / "src"
LEAN_ROOT = ROOT / "FracLap"
OUT = ROOT / "docs" / "knowledge"
REPO_URL = "https://github.com/bwrob/frac-lap-lean"
NAV_BEGIN = "# BEGIN GENERATED NAV"
NAV_END = "# END GENERATED NAV"


_PROV: dict[str, Any] = {}
PROVENANCE = ROOT / "docs" / "provenance.toml"
STATUS_LABEL = {
    "active": "active",
    "in-progress": "in progress",
    "planned": "planned",
    "paused": "paused",
    "aspirational": "aspirational",
}

KINDS = {
    "definition": "Definition",
    "theorem": "Theorem",
    "lemma": "Lemma",
    "proposition": "Proposition",
    "corollary": "Corollary",
    "remark": "Remark",
    "example": "Example",
}

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom|opaque)\s+"
    r"([^\s:({\[]+)"
)
CHUNK_START_RE = re.compile(
    r"^(/--|@\[|theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom|opaque|"
    r"noncomputable|private|protected|namespace|end\b|section|open\b|variable|universe|"
    r"set_option|attribute|/-!|public\b|omit|include|local|scoped|macro|syntax|elab|notation|"
    r"example|deriving|import|module)"
)
ACCENTS = {
    r"\'e": "é", r"\'a": "á", r"\"o": "ö", r"\"u": "ü", r"\~n": "ñ", r"\'o": "ó",
    r"\'i": "í", r"\c{c}": "ç", r"\'E": "É", r"\l": "ł", r"\L": "Ł", r"\v{s}": "š",
    r"\'{e}": "é", r"\"{o}": "ö", r"\~{n}": "ñ", r"\'c": "ć",
}  # fmt: skip


@dataclass
class Node:
    """One theorem-like blueprint environment."""

    kind: str
    title: str
    label: str
    number: str
    lean: list[str]
    uses: list[str]
    leanok: bool
    mathlibok: bool
    statement: str
    raw: str
    proof: str = ""
    proof_leanok: bool = False
    proof_uses: list[str] = field(default_factory=list)
    proof_raw: str = ""


@dataclass
class Chapter:
    """A parsed blueprint chapter."""

    path: str  # e.g. ``Core/AnalyticSemigroup``
    title: str
    number: int
    intro: str
    nodes: list[Node]
    origin: str = ""
    projects: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# LaTeX -> Markdown (restricted subset used by the blueprint)
# ---------------------------------------------------------------------------


def _match_brace(s: str, i: int) -> int:
    """Return the index of the ``}`` matching the ``{`` at ``s[i]``."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{" and (j == 0 or s[j - 1] != "\\"):
            depth += 1
        elif s[j] == "}" and (j == 0 or s[j - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return j
    return len(s) - 1


def _extract_cmd(s: str, name: str) -> tuple[str, list[str]]:
    """Remove ``\\name{...}`` occurrences from ``s``; return ``(rest, [arguments])``."""
    args: list[str] = []
    pat = re.compile(r"\\" + name + r"\s*\{")
    while True:
        m = pat.search(s)
        if not m:
            return s, args
        end = _match_brace(s, m.end() - 1)
        args.append(s[m.end() : end])
        s = s[: m.start()] + s[end + 1 :]


def _split_list(arg: str) -> list[str]:
    return [x.strip() for x in arg.replace("\n", " ").split(",") if x.strip()]


MATH_ENVS = ("align*", "align", "equation*", "equation", "gather*", "gather", "multline*")


def _protect_math(s: str) -> tuple[str, list[str]]:
    """Replace math by placeholders so that text rewriting cannot touch it."""
    store: list[str] = []

    def put(tex: str, display: bool) -> str:
        store.append(f"\\[{tex.strip()}\\]" if display else f"\\({tex.strip()}\\)")
        return f"\n\n@@MATH{len(store) - 1}@@\n\n" if display else f"@@MATH{len(store) - 1}@@"

    for env in MATH_ENVS:
        e = re.escape(env)
        s = re.sub(
            r"\\begin\{" + e + r"\}(.*?)\\end\{" + e + r"\}",
            lambda m, env=env: put(f"\\begin{{{env}}}{m.group(1)}\\end{{{env}}}", True),
            s,
            flags=re.S,
        )
    s = re.sub(r"\\\[(.*?)\\\]", lambda m: put(m.group(1), True), s, flags=re.S)
    s = re.sub(r"\$\$(.*?)\$\$", lambda m: put(m.group(1), True), s, flags=re.S)
    s = re.sub(r"(?<!\\)\$(.+?)(?<!\\)\$", lambda m: put(m.group(1), False), s, flags=re.S)
    return s, store


def tex_to_md(s: str, resolve_ref: Callable[[str], str]) -> str:
    """Convert a LaTeX fragment (prose with math) to Markdown with MathJax delimiters."""
    s = re.sub(r"(?m)^\s*%.*$", "", s)
    s, math = _protect_math(s)
    s = re.sub(r"\\verb\|([^|]*)\|", lambda m: f"`{m.group(1)}`", s)
    for tex, uni in ACCENTS.items():
        s = s.replace(tex, uni)
    for _ in range(3):
        s = re.sub(r"\\texttt\{([^{}]*)\}", lambda m: "`" + m.group(1).replace("\\_", "_") + "`", s)
        s = re.sub(r"\\(?:emph|textit)\{([^{}]*)\}", r"*\1*", s)
        s = re.sub(r"\\textbf\{([^{}]*)\}", r"**\1**", s)
        s = re.sub(r"\\textsc\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\(?:eqref|ref)\{([^}]*)\}", lambda m: resolve_ref(m.group(1)), s)
    s = re.sub(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", r"[\1]", s)
    s = re.sub(r"\\footnote\{([^{}]*)\}", r" (\1)", s)
    s = re.sub(r"\\item\s*", "\n- ", s)
    s = re.sub(r"\\begin\{(?:itemize|enumerate)\}", "\n", s)
    s = re.sub(r"\\end\{(?:itemize|enumerate)\}", "\n", s)
    s = s.replace("---", "—").replace("--", "–").replace("``", "“").replace("''", "”")
    s = s.replace("~", " ").replace("\\&", "&").replace("\\%", "%").replace("\\_", "_")
    s = s.replace("\\\\", "\n")
    s = re.sub(r"\\[a-zA-Z]+\*?(?![a-zA-Z])\s*", "", s) if False else s  # keep unknown macros
    s = re.sub(r"@@MATH(\d+)@@", lambda m: math[int(m.group(1))], s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


# ---------------------------------------------------------------------------
# Blueprint parsing
# ---------------------------------------------------------------------------


def chapter_order() -> list[str]:
    """Chapter paths in ``content.tex`` order."""
    content = (BLUEPRINT / "content.tex").read_text(encoding="utf-8")
    return re.findall(r"^\\input\{([^}]+)\}", content, flags=re.M)


ENV_RE = re.compile(
    r"\\begin\{(" + "|".join(KINDS) + r"|proof)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", flags=re.S
)


def parse_chapter(path: str, number: int) -> Chapter:
    """Parse one blueprint chapter into structured nodes (raw text, resolved later)."""
    text = (BLUEPRINT / f"{path}.tex").read_text(encoding="utf-8")
    text = re.sub(r"\A\s*/-.*?-/\s*", "", text, flags=re.S)  # licence header
    m = re.search(r"\\chapter\{(.*)\}", text)
    title = m.group(1) if m else path
    first_env = ENV_RE.search(text)
    intro_end = first_env.start() if first_env else len(text)
    intro = text[m.end() if m else 0 : intro_end]
    nodes: list[Node] = []
    counter = 0
    for em in ENV_RE.finditer(text):
        env, opt, body = em.group(1), em.group(2) or "", em.group(3)
        raw = em.group(0)
        if env == "proof":
            if not nodes:
                continue
            body, uses = _extract_cmd(body, "uses")
            ok = bool(re.search(r"\\leanok", body))
            body = body.replace("\\leanok", "")
            nodes[-1].proof, nodes[-1].proof_raw = body, raw
            nodes[-1].proof_leanok = ok
            nodes[-1].proof_uses = [u for a in uses for u in _split_list(a)]
            continue
        counter += 1
        body, labels = _extract_cmd(body, "label")
        body, lean = _extract_cmd(body, "lean")
        body, uses = _extract_cmd(body, "uses")
        body, _ = _extract_cmd(body, "discussion")
        leanok = "\\leanok" in body
        mathlibok = "\\mathlibok" in body
        body = body.replace("\\leanok", "").replace("\\mathlibok", "").replace("\\notready", "")
        nodes.append(
            Node(
                kind=env,
                title=opt,
                label=labels[0].strip() if labels else "",
                number=f"{number}.{counter}",
                lean=[n for a in lean for n in _split_list(a)],
                uses=[u for a in uses for u in _split_list(a)],
                leanok=leanok,
                mathlibok=mathlibok,
                statement=body,
                raw=raw,
            )
        )
    return Chapter(path=path, title=title, number=number, intro=intro, nodes=nodes)


# ---------------------------------------------------------------------------
# Provenance (origin of each chapter and the projects it belongs to)
# ---------------------------------------------------------------------------


def load_provenance() -> dict[str, Any]:
    """Parse ``docs/provenance.toml``."""
    return tomllib.loads(PROVENANCE.read_text(encoding="utf-8"))


def classify(path: str, prov: dict[str, Any]) -> tuple[str, list[str]] | None:
    """Origin and projects of a chapter: explicit ``modules`` entry, else the first rule."""
    explicit = prov.get("modules", {}).get(path)
    if explicit:
        return explicit["origin"], list(explicit.get("projects", []))
    for rule in prov.get("rules", []):
        if fnmatch.fnmatch(path, rule["glob"]):
            return rule["origin"], list(rule.get("projects", []))
    return None


def apply_provenance(chapters: list[Chapter], prov: dict[str, Any]) -> list[str]:
    """Annotate chapters; return a list of problems (unclassified, unknown names, bad pages)."""
    problems: list[str] = []
    origins, projects = prov.get("origins", {}), prov.get("projects", {})
    for c in chapters:
        hit = classify(c.path, prov)
        if hit is None:
            problems.append(f"chapter {c.path} has no origin (add a rule to docs/provenance.toml)")
            continue
        c.origin, c.projects = hit
        if c.origin not in origins:
            problems.append(f"chapter {c.path}: unknown origin {c.origin!r}")
        problems += [
            f"chapter {c.path}: unknown project {p!r}" for p in c.projects if p not in projects
        ]
    for pid, proj in projects.items():
        if not (ROOT / "docs" / proj["page"]).exists():
            problems.append(f"project {pid}: page docs/{proj['page']} does not exist")
        if proj.get("parent") and proj["parent"] not in projects:
            problems.append(f"project {pid}: unknown parent {proj['parent']!r}")
    return problems


def project_links(c: Chapter, prov: dict[str, Any], from_path: str) -> str:
    from posixpath import relpath

    base = Path(from_path).parent.as_posix()
    links = []
    for pid in c.projects:
        proj = prov["projects"][pid]
        target = relpath(f"projects/{Path(proj['page']).name}", start=f"knowledge/{base}")
        links.append(f"[{proj['title']}]({target})")
    return ", ".join(links)


# ---------------------------------------------------------------------------
# Lean source index
# ---------------------------------------------------------------------------


@dataclass
class Chunk:
    """A contiguous top-level Lean item."""

    file: str
    start: int  # 1-based
    end: int
    text: str


def _file_chunks(f: Path) -> list[tuple[str, Chunk]]:
    """Top-level chunks of one Lean file with the (first) declared short name of each."""
    lines = f.read_text(encoding="utf-8").splitlines()
    rel = f.relative_to(ROOT).as_posix()
    starts = [
        i
        for i, ln in enumerate(lines)
        if CHUNK_START_RE.match(ln) and (i == 0 or lines[i - 1].strip() == "")
    ]
    out: list[tuple[str, Chunk]] = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        while e > s and lines[e - 1].strip() == "":
            e -= 1
        chunk_lines = lines[s:e]
        decl = next((m for m in map(DECL_RE.match, chunk_lines) if m), None)
        if decl:
            short = decl.group(1).split(".")[-1]
            out.append((short, Chunk(rel, s + 1, e, "\n".join(chunk_lines))))
    return out


def index_lean() -> dict[str, list[Chunk]]:
    """Map the last component of each declaration name to the chunks that declare it."""
    index: dict[str, list[Chunk]] = defaultdict(list)
    for f in sorted(LEAN_ROOT.rglob("*.lean")):
        for short, chunk in _file_chunks(f):
            index[short].append(chunk)
    return index


def module_doc(lean_file: Path) -> str:
    """The ``/-! ... -/`` module docstring (Markdown) of a Lean file, if any."""
    if not lean_file.exists():
        return ""
    m = re.search(r"/-!(.*?)-/", lean_file.read_text(encoding="utf-8"), flags=re.S)
    if not m:
        return ""
    doc = m.group(1).strip()
    return re.sub(r"\A#[^\n]*\n+", "", doc)  # drop the redundant H1


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def indent(text: str, n: int = 4) -> str:
    pad = " " * n
    return "\n".join(pad + ln if ln.strip() else "" for ln in text.splitlines())


def _resolver(ch: Chapter, labels: dict[str, tuple[str, Node]]) -> Callable[[str], str]:
    def resolve(label: str) -> str:
        hit = labels.get(label)
        if not hit:
            return f"`{label}`"
        page, node = hit
        target = "" if page == ch.path else _rel(ch.path, page)
        return f"[{KINDS[node.kind]} {node.number}]({target}#{label})"

    return resolve


def _lean_tab(n: Node, ch: Chapter, lean_idx: dict[str, list[Chunk]], miss: list[str]) -> str:
    own_file = f"FracLap/{ch.path}.lean"
    parts: list[str] = []
    for full in n.lean:
        cands = lean_idx.get(full.split(".")[-1], [])
        own = [c for c in cands if c.file == own_file]
        chunk = (own or cands or [None])[0]
        if chunk is None:
            miss.append(f"{ch.path}: {full}")
            parts.append(f"`{full}` is not a standalone declaration (generated or field).")
            continue
        link = f"{REPO_URL}/blob/main/{chunk.file}#L{chunk.start}-L{chunk.end}"
        parts.append(
            f'```lean title="{full}"\n{chunk.text}\n```\n\n'
            f"[`{chunk.file}` L{chunk.start}–L{chunk.end}]({link})"
        )
    if not parts:
        parts.append("*No Lean declaration is attached to this node (standard result or prose).*")
    return "\n\n".join(parts)


def render_node(
    n: Node,
    ch: Chapter,
    labels: dict[str, tuple[str, Node]],
    lean_idx: dict[str, list[Chunk]],
    miss: list[str],
) -> str:
    resolve = _resolver(ch, labels)
    head = f"{KINDS[n.kind]} {n.number}" + (f" ({n.title})" if n.title else "")
    anchor = f" {{#{n.label}}}" if n.label else ""
    out = [f"### {head}{anchor}", ""]
    uses = list(dict.fromkeys(n.uses + n.proof_uses))
    bp = [tex_to_md(n.statement, resolve)]
    if n.proof:
        bp += ["", '??? note "Proof"', "", indent(tex_to_md(n.proof, resolve))]
    if uses:
        bp += ["", "*Depends on:* " + ", ".join(resolve(u) for u in uses)]
    out += ['=== "Blueprint"', "", indent("\n".join(bp)), ""]
    out += ['=== "Lean"', "", indent(_lean_tab(n, ch, lean_idx, miss)), ""]
    raw = n.raw + ("\n\n" + n.proof_raw if n.proof_raw else "")
    out += ['=== "LaTeX source"', "", indent(f"```latex\n{raw.strip()}\n```"), ""]
    return "\n".join(out)


def _rel(from_path: str, to_path: str) -> str:
    """Relative ``.md`` link between two chapters."""
    from posixpath import relpath

    return relpath(f"{to_path}.md", start=Path(from_path).parent.as_posix() or ".")


def render_chapter(
    ch: Chapter,
    labels: dict[str, tuple[str, Node]],
    lean_idx: dict[str, list[Chunk]],
    miss: list[str],
) -> str:
    resolve = _resolver(ch, labels)
    lean_rel = f"FracLap/{ch.path}.lean"
    has_lean = (ROOT / lean_rel).exists()
    parts = [
        f"# {ch.number}. {tex_to_md(ch.title, resolve)}",
        "",
    ]
    links = [f"[Blueprint source]({REPO_URL}/blob/main/blueprint/src/{ch.path}.tex)"]
    if has_lean:
        links.insert(0, f"[Lean source]({REPO_URL}/blob/main/{lean_rel})")
    parts += [" · ".join(links), ""]
    intro = tex_to_md(ch.intro, resolve)
    if intro:
        parts += [intro, ""]
    doc = module_doc(ROOT / lean_rel)
    if doc:
        parts += ['??? abstract "Lean module overview"', "", indent(doc), ""]
    for n in ch.nodes:
        parts += [render_node(n, ch, labels, lean_idx, miss), "---", ""]
    return "\n".join(parts)


def section_of(path: str) -> str:
    return path.split("/")[0] if "/" in path else "General"


def render_index(chapters: list[Chapter]) -> str:
    total = sum(len(c.nodes) for c in chapters)
    ok = sum(1 for c in chapters for n in c.nodes if n.leanok or n.mathlibok)
    proofs = sum(1 for c in chapters for n in c.nodes if n.proof and n.proof_leanok)
    with_proof = sum(1 for c in chapters for n in c.nodes if n.proof)
    lines = [
        "# Knowledge",
        "",
        "Every page below is generated from the repository: the **blueprint** chapter "
        "(`blueprint/src/<Path>.tex`) and the **Lean** module (`FracLap/<Path>.lean`) it mirrors. "
        "Pick the **Blueprint**, **Lean** or **LaTeX source** tab on any statement; the choice "
        "applies to the whole site.",
        "",
        f"**{len(chapters)} chapters · {total} nodes · {ok} with a formalized statement "
        f"(or standard result) · {proofs}/{with_proof} proofs marked formalized.**",
        "",
        "The interactive dependency graph of the blueprint is published next to this site: "
        "[open the blueprint](../blueprint/index.html).",
        "",
    ]
    by_section: dict[str, list[Chapter]] = defaultdict(list)
    for c in chapters:
        by_section[section_of(c.path)].append(c)
    for sec, cs in by_section.items():
        lines += [f"## {sec}", "", "| Chapter | Nodes | Formalized |", "|---|---|---|"]
        for c in cs:
            d = sum(1 for n in c.nodes if n.leanok or n.mathlibok)
            lines.append(f"| [{c.number}. {_plain(c.title)}]({c.path}.md) | {len(c.nodes)} | {d} |")
        lines.append("")
    lines += ["## Bibliography", "", "[All cited sources](bibliography.md).", ""]
    return "\n".join(lines)


def _plain(s: str) -> str:
    s = re.sub(r"\\texttt\{([^}]*)\}", r"\1", s)
    return re.sub(r"\$([^$]*)\$", r"\1", s).replace("\\", "")


def render_bibliography() -> str:
    bib = (ROOT / "blueprint" / "src" / "references.bib").read_text(encoding="utf-8")
    rows: list[tuple[str, str, str, str]] = []
    for entry in re.split(r"(?=^@\w+\s*\{)", bib, flags=re.M):
        if not entry.startswith("@"):
            continue
        key = re.match(r"@\w+\s*\{\s*([^,\s]+)", entry)
        if not key:
            continue

        def field_of(name: str, entry: str = entry) -> str:
            m = re.search(name + r"\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}", entry, flags=re.S | re.I)
            return re.sub(r"[{}\s]+", " ", m.group(1)).strip() if m else ""

        arx = field_of("eprint")
        link = f"[arXiv:{arx}](https://arxiv.org/abs/{arx})" if arx else ""
        rows.append(
            (
                key.group(1),
                field_of("author"),
                field_of("year"),
                field_of("title") + (f" — {link}" if link else ""),
            )
        )
    out = [
        "# Bibliography",
        "",
        "Literature cited by the blueprint and the Lean sources (`blueprint/src/references.bib`).",
        "",
        f"{len(rows)} entries.",
        "",
        "| Key | Authors | Year | Title |",
        "|---|---|---|---|",
    ]
    for key, au, yr, ti in sorted(rows, key=lambda r: (r[1].lower(), r[2])):
        out.append(
            "| " + " | ".join(x.replace("|", "\\|") for x in (f"`{key}`", au, yr, ti)) + " |"
        )
    return "\n".join(out) + "\n"


def nav_block(chapters: list[Chapter]) -> str:
    by_section: dict[str, list[Chapter]] = defaultdict(list)
    for c in chapters:
        by_section[section_of(c.path)].append(c)
    lines = ['        { "Overview" = "knowledge/index.md" },']
    for sec, cs in by_section.items():
        items = ", ".join(
            f'{{ "{c.number}. {_plain(c.title).replace(chr(34), "")}" = "knowledge/{c.path}.md" }}'
            for c in cs
        )
        lines.append(f'        {{ "{sec}" = [{items}] }},')
    lines.append('        { "Bibliography" = "knowledge/bibliography.md" },')
    return "\n".join(lines)


def patched_toml(chapters: list[Chapter]) -> str:
    toml = (ROOT / "zensical.toml").read_text(encoding="utf-8")
    pat = re.compile(re.escape(NAV_BEGIN) + r".*?" + re.escape(NAV_END), flags=re.S)
    block = f"{NAV_BEGIN}\n{nav_block(chapters)}\n        {NAV_END}"
    toml = pat.sub(lambda _m: block, toml)
    return toml


@app.command()
def main(
    check: Annotated[bool, typer.Option("--check", help="Only verify the nav block.")] = False,
) -> None:
    """Generate docs/knowledge/ and refresh the generated nav block of zensical.toml."""
    order = chapter_order()
    chapters = [parse_chapter(p, i + 1) for i, p in enumerate(order)]
    _PROV.update(load_provenance())
    problems = apply_provenance(chapters, _PROV)
    if problems:
        for pr in problems:
            typer.secho(f"provenance: {pr}", fg="red", err=True)
        raise typer.Exit(1)
    if check:
        if patched_toml(chapters) != (ROOT / "zensical.toml").read_text(encoding="utf-8"):
            typer.secho("zensical.toml nav is stale: run `just docs-gen`.", fg="red", err=True)
            raise typer.Exit(1)
        typer.echo("docs nav is current")
        return
    labels = {n.label: (c.path, n) for c in chapters for n in c.nodes if n.label}
    lean_idx = index_lean()
    miss: list[str] = []
    if OUT.exists():
        for f in OUT.rglob("*.md"):
            f.unlink()
    for c in chapters:
        target = OUT / f"{c.path}.md"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(render_chapter(c, labels, lean_idx, miss), encoding="utf-8")
    (OUT / "index.md").write_text(render_index(chapters), encoding="utf-8")
    (OUT / "bibliography.md").write_text(render_bibliography(), encoding="utf-8")
    (ROOT / "zensical.toml").write_text(patched_toml(chapters), encoding="utf-8")
    nodes = sum(len(c.nodes) for c in chapters)
    typer.echo(f"{len(chapters)} chapters, {nodes} nodes, {len(miss)} Lean names not found")
    for m in miss[:20]:
        typer.echo(f"  missing: {m}")


if __name__ == "__main__":
    init_logging(__file__)
    app()
