# Documentation

| Directory | Role | Normative? |
|---|---|---|
| [`spec/`](spec/) | The specification: goals, mathematical framework, the constructors and what each promises, axiom analysis, verification plan. | **Yes.** The code follows it; a design change edits it first. |
| [`decisions/`](decisions/) | One short record per design decision: context, options, decision, consequences, and who decided. | Records what was decided; the spec says what follows. |
| [`plans/`](plans/) | Plans for larger pieces of work; each doubles as the hand-off for the conversation or contributor who takes it on. | No. |
| [`notes/`](notes/) | Analyses, design reviews, history. Dated in the file name. | No. Where a note and the spec differ, the spec wins. |
| [`tutorial/`](tutorial/) | A tutorial with interpreter transcripts: where the work came from, how the design differs and why, nine use cases, known issues. The transcripts come from `tutorial.input`. | No. |
| [`INDEX.md`](INDEX.md) | Every label in the spec (goals G1–G8, conditions, axioms, results) with its section, its standing and the tests that check it. | Bookkeeping. |

Words are defined in the [glossary](../GLOSSARY.md); the [orientation](../ORIENTATION.md) is the place to start.
