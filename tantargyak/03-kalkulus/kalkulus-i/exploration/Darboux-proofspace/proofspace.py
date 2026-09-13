#!/usr/bin/env python3
"""
A sketching prototype for proof spaces.  EXPLORATORY ONLY.

Nothing this script prints is verified: it is a napkin, meant for trying a shape out
before writing it down in Lean.  Everything it does has a machine-checked counterpart in
RequestProject/Explore/ (Graph.lean for the primitives, Shapes.lean for the theorems,
Loop.lean for the harvest-and-remap loop), and only the Lean version proves anything.

Usage:
    python3 scripts/proofspace.py              # the example space
    python3 scripts/proofspace.py --dot        # Graphviz source
    python3 scripts/proofspace.py my_space.txt # your own space

A space file is one implication per line, "a => b", with blank lines and #-comments
ignored; "a & b => c" adds a hyperedge (two hypotheses acting together), and a line
"node: x" adds an isolated node.
"""

from __future__ import annotations

import sys
from itertools import combinations

# ---------------------------------------------------------------- the space


class Space:
    def __init__(self, nodes=None, edges=None, hyperedges=None):
        self.nodes: list[str] = list(nodes or [])
        self.edges: list[tuple[str, str]] = list(edges or [])
        self.hyperedges: list[tuple[list[str], str]] = list(hyperedges or [])
        for a, b in self.edges:
            for x in (a, b):
                if x not in self.nodes:
                    self.nodes.append(x)
        for hs, c in self.hyperedges:
            for x in hs + [c]:
                if x not in self.nodes:
                    self.nodes.append(x)

    # --- local structure -------------------------------------------------
    def succs(self, a):
        return [y for (x, y) in self.edges if x == a]

    def preds(self, a):
        return [x for (x, y) in self.edges if y == a]

    def foundations(self):
        return [a for a in self.nodes if not self.succs(a)]

    def frontier(self):
        return [a for a in self.nodes if not self.preds(a)]

    def leaves(self):
        return [a for a in self.nodes if len(self.succs(a)) + len(self.preds(a)) == 1]

    def isolated(self):
        return [a for a in self.nodes if not self.succs(a) and not self.preds(a)]

    def single_entry(self):
        """Conclusions reached by exactly one implication: a bottleneck, and so a
        lemma shape — the 'spot' step of the loop."""
        return [a for a in self.nodes if len(self.preds(a)) == 1]

    # --- global structure ------------------------------------------------
    def closure(self, start):
        """Forward closure under edges *and* hyperedges: what a set of assumptions
        gets you.  With hyperedges this is strictly stronger than reachability."""
        seen = set(start)
        changed = True
        while changed:
            changed = False
            for a, b in self.edges:
                if a in seen and b not in seen:
                    seen.add(b)
                    changed = True
            for hs, c in self.hyperedges:
                if all(h in seen for h in hs) and c not in seen:
                    seen.add(c)
                    changed = True
        return sorted(seen)

    def cone(self, a):
        return self.closure([a])

    def reaches(self, a, b):
        return b in self.cone(a)

    def locked_pairs(self):
        return [(a, b) for a, b in combinations(self.nodes, 2)
                if self.reaches(a, b) and self.reaches(b, a)]

    def routes(self, a, b, path=None):
        """All simple chains a -> ... -> b (ordinary edges only)."""
        path = (path or []) + [a]
        if a == b:
            return [path]
        out = []
        for c in self.succs(a):
            if c not in path:
                out += self.routes(c, b, path)
        return out

    def meets(self, a, b):
        """For each pair of routes, the nodes they have in common."""
        rs = self.routes(a, b)
        return [(r1, r2, [x for x in r1 if x in r2]) for r1, r2 in combinations(rs, 2)]

    def diamonds(self, a, b):
        return [(r1, r2) for r1, r2, m in self.meets(a, b) if m == [a, b]]

    # --- holes: where to look next ---------------------------------------
    def open_pairs(self):
        """Pairs the map is silent about: neither direction derivable.  These are the
        candidate conjectures, and they cluster around isolated and leaf nodes."""
        return [(a, b) for a in self.nodes for b in self.nodes
                if a != b and not self.reaches(a, b) and not self.reaches(b, a)]

    def hyperedge_candidates(self):
        """The high-yield pattern: a pair of hypotheses neither of which alone reaches
        the conclusion.  Every such triple is a lemma-shaped hole worth testing."""
        out = []
        for a, b in combinations(self.nodes, 2):
            joint = set(self.closure([a, b]))
            alone = set(self.closure([a])) | set(self.closure([b]))
            for c in sorted(joint - alone):
                out.append((a, b, c))
        return out


# ---------------------------------------------------------------- reporting


def report(S: Space) -> str:
    lines = [f"nodes ({len(S.nodes)}): " + ", ".join(S.nodes),
             f"edges ({len(S.edges)}): " + ", ".join(f"{a}=>{b}" for a, b in S.edges)]
    if S.hyperedges:
        lines.append(f"hyperedges ({len(S.hyperedges)}): " +
                     ", ".join(f"{'&'.join(hs)}=>{c}" for hs, c in S.hyperedges))
    lines += ["foundations : " + ", ".join(S.foundations()),
              "frontier    : " + ", ".join(S.frontier()),
              "leaves      : " + ", ".join(S.leaves()),
              "isolated    : " + (", ".join(S.isolated()) or "(none)"),
              "single-entry conclusions (bottlenecks): " + ", ".join(S.single_entry()),
              "locked pairs: " + (", ".join(f"{a}<->{b}" for a, b in S.locked_pairs())
                                  or "none (acyclic)")]
    lines.append("")
    lines.append("shapes between every pair with more than one route:")
    found = False
    for a in S.nodes:
        for b in S.nodes:
            if a == b:
                continue
            rs = S.routes(a, b)
            if len(rs) > 1:
                found = True
                lines.append(f"  {a} => {b}: {len(rs)} routes")
                for r in rs:
                    lines.append("    " + " -> ".join(r))
                for _r1, _r2, m in S.meets(a, b):
                    kind = ("diamond" if m == [a, b]
                            else "braided at " + ", ".join(m[1:-1]))
                    lines.append(f"    {kind}")
    if not found:
        lines.append("  (none — the map is a forest of chains)")
    lines.append("")
    op = S.open_pairs()
    lines.append(f"open pairs ({len(op)}) — the candidate one-hypothesis conjectures:")
    lines.append("  " + ", ".join(f"{a}?{b}" for a, b in op[:40]))
    hc = S.hyperedge_candidates()
    lines.append("")
    lines.append(f"joint consequences already implied by the hyperedges ({len(hc)}):")
    lines.append("  " + (", ".join(f"{a}&{b}=>{c}" for a, b, c in hc) or "(none)"))
    return "\n".join(lines)


def to_dot(S: Space, title="proof space") -> str:
    out = [f'digraph "{title}" {{', "  rankdir=LR;"]
    for a in S.nodes:
        shape = "box" if not S.succs(a) else "ellipse"
        style = ", style=dashed" if a in S.isolated() else ""
        out.append(f'  "{a}" [shape={shape}{style}];')
    for a, b in S.edges:
        out.append(f'  "{a}" -> "{b}";')
    for i, (hs, c) in enumerate(S.hyperedges):
        j = f"h{i}"
        out.append(f'  "{j}" [shape=point];')
        for h in hs:
            out.append(f'  "{h}" -> "{j}" [arrowhead=none];')
        out.append(f'  "{j}" -> "{c}";')
    out.append("}")
    return "\n".join(out)


# ---------------------------------------------------------------- input


def parse(text: str) -> Space:
    nodes, edges, hyper = [], [], []
    for raw in text.splitlines():
        line = raw.split("#")[0].strip()
        if not line:
            continue
        if line.startswith("node:"):
            nodes.append(line[5:].strip())
        elif "=>" in line:
            lhs, rhs = (p.strip() for p in line.split("=>", 1))
            if "&" in lhs:
                hyper.append(([p.strip() for p in lhs.split("&")], rhs))
            else:
                edges.append((lhs, rhs))
    return Space(nodes, edges, hyper)


EXAMPLE = """
# the proved implications of the graph-property vocabulary ...
complete    => connected
complete    => regular
edgeless    => regular
edgeless    => maxDegLeOne
edgeless    => triangleFree
maxDegLeOne => triangleFree
node: hasEdge
# ... and the four hyperedges harvested from the chest
complete & triangleFree  => maxDegLeOne
edgeless & connected     => complete
connected & maxDegLeOne  => complete
connected & maxDegLeOne  => regular
"""


def main(argv: list[str]) -> None:
    args = [a for a in argv[1:] if not a.startswith("--")]
    text = open(args[0]).read() if args else EXAMPLE
    S = parse(text)
    print(to_dot(S) if "--dot" in argv else report(S))


if __name__ == "__main__":
    main(sys.argv)
