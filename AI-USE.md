# AI use and authorship

Last reviewed: 25 November 2026.

## Who does what

- **Bill Page** owns the repository and directs the work: he sets the goals, decides the design (decision records name him where he decided), reviews, and merges every change to `main`. He wrote the original 2016–17 implementation.
- **Claude** (Anthropic), working in a Claude project with Bill, drafts specifications, notes, code and tests, runs FriCAS to check them, and proposes options. It does not choose among design options or approve its own work as the final check.
- Other contributors are welcome; see [`CONTRIBUTING.md`](CONTRIBUTING.md).

Claude's commits carry a `Co-Authored-By: Claude` trailer. Claude is not listed as an author of the package or its documents: authorship implies responsibility for the work, which rests with the people who review and accept it.

## What this means for a reader

Every claim about FriCAS behaviour in the documents is meant to rest on a run, and every result on a test or a proof in the specification. Nothing here has had external review. Treat the specification as a careful draft: check a proof before relying on it, and report what you find.

## Delivery

Claude pushes only to branches named `claude/<topic>`. `main` changes only through pull requests that the maintainer merges.

## Copyright

The documents and code were drafted with AI assistance under Bill Page's direction, selection and editing. How copyright applies to AI-assisted text is still being settled in several jurisdictions; the licences in `LICENSE` and `LICENSE-DOCS` are granted to the extent the contributors hold rights in the material. Both licences are permissive, so the practical effect on a user is small.
