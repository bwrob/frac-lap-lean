# How the work is done

## A loop with a machine-checked core

1. **Look up the source.** Before every new group of lemmas the canonical statement, proof route and constants are taken from the literature and Mathlib is searched for existing helpers. The route is followed unless it does not fit Mathlib; sources are cited in the module docstring or the blueprint.
2. **State the intuition.** Each lemma group starts with the idea in a sentence or two: what is being compared, which cancellation, convexity or symmetry is used, which estimate is sharp and why. The same idea goes into the blueprint proof sketch.
3. **Formalize** in small, verified commits: one coherent milestone (a lemma group, a chapter, a tooling step) per commit, with a conventional-commit message.
4. **Guard the core.** The strict gates (zero `sorry`, 1-to-1 blueprint parity, axiom and gap audits) apply to everything on `main`.

## AI assistance

This repository is developed in collaboration with an AI coding assistant (Claude Code). The assistant drafts Lean proofs and blueprint text, runs the builds, and records its sessions in the commit trailers (`Co-Authored-By`, `Claude-Session`). The trust model does not rest on who wrote a proof: **the Lean kernel checks every proof, the axiom and gap audits check what the proofs depend on, and the human maintainer fixes the specifications.** Standing rules for the assistant (spec-locking, claim discipline, query the literature before inventing, explain the intuition, never push without being asked) live in `AGENTS.md`.

## Conventions

- Conventional Commits: `<type>(<scope>): <imperative summary, at most 72 characters>`; hooks enforce this and are never bypassed.
- Blueprint prose never cites library lemma names; standard facts are `\mathlibok` nodes.
- Strict linters (`warningAsError`, `autoImplicit = false`, missing-docs, long-line, header) apply to the whole library.
- Heavy verification (`verify-all`, multi-kernel replay, `comparator`) runs at milestones and on request, not on every edit.
