---
name: ${SKILL_NAME}
description: >-
  ${SKILL_DESCRIPTION}
---

# ${SKILL_TITLE} Skill (`${SKILL_NAME}`)

${SKILL_SUMMARY}

---

## Core Objectives & Responsibilities

1. **Primary Goal**: Clear description of what the agent accomplishes when executing this skill.
2. **Operational Boundaries**: What is in-scope vs. out-of-scope.
3. **Invariants & Non-Negotiables**: Critical constraints that must never be violated.

---

## Standard Workflow

1. **Preparation & Pre-flight**: Inspect state and prerequisites.
2. **Execution**: Apply changes following repository invariants.
3. **Verification**: Run `just verify-all`.

---

## External Templates & Reference Manuals

- **Templates (`resources/`)**: [resources/template.md](./resources/template.md)
- **Deep References (`references/`)**: [references/manual.md](./references/manual.md)
