---
name: skill-creator
description: >-
  Guide, scaffold, and validate new Antigravity skills in .agents/skills/, ensuring all
  multi-line templates and skeletons are externalized into dedicated files in resources/.
  Use whenever designing, authoring, or refactoring workspace skills.
---

# Skill Creator (`skill-creator`)

Standards and workflow for authoring **Antigravity Skills** in `.agents/skills/`.

---

## Core Principles

1. **Progressive Disclosure**: Keep `SKILL.md` focused on triggers, workflow, and invariants; put deep manuals in `references/`, reusable templates in `resources/`, and CLI automation in `scripts/`.
2. **Externalize Templates (Never Inline)**: Multi-line code skeletons or document outlines must live in `resources/<name>_template.<ext>` and be linked from `SKILL.md`.
3. **Verification**: After editing Python helpers or skills, run `just lint-py` and `just verify-all`.

---

## Workflow

1. **Scaffold**:
   ```bash
   just new-skill <skill-name> "<Trigger description>"
   ```
2. **Author `SKILL.md`**: Fill frontmatter (`name`, `description`), sequential workflow, and links to externalized `resources/` and `references/`.
3. **Validate**:
   ```bash
   just lint-py
   ```

---

## Reusable Assets

- **Starter Skill Template**: [resources/skill_template.md](./resources/skill_template.md)
- **Scaffolding Utility**: [scripts/scaffold_skill.py](./scripts/scaffold_skill.py)
