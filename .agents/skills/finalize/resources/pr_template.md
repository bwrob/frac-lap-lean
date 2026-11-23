# Pull Request Template (`.agents/skills/finalize/resources/pr_template.md`)

```markdown
## Summary

- **Scope:** <1-2 sentence overview of formalized definitions, lemmas, and theorems>
- **Literature Source:** <Paper/book citation key from `blueprint/src/references.bib`>

### Blueprint & Lean Synchronization
- **Lean Modules:** `FracLap/<Module>.lean`
- **Blueprint Nodes:** `<label_1>`, `<label_2>`

### Verification Gates
- [x] `just build` — Lean 4 compilation clean
- [x] `just check-axioms` — Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`), zero `sorryAx`
- [x] `just blueprint` — `leanblueprint all` (`checkdecls`, web dependency graph, and PDF) clean
- [x] `just lint-py && just test` — Python checks green
```
