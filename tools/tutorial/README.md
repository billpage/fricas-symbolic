# Tutorial generator

`docs/tutorial/tutorial.md` is generated. Every FriCAS result in it is copied
from a recorded run, never typed, and this directory holds the tool that does
the copying.

| File | Role |
|---|---|
| `../../docs/tutorial/tutorial.src.md` | The text of the tutorial, with a placeholder `<!--run:NAME:SECTION-->` wherever a transcript goes. **Edit this file.** |
| `../../docs/tutorial/transcripts/NAME.out` | A recorded run: the commands echoed with FriCAS's results, in one-line (`Format1D`) form. |
| `../../docs/tutorial/*.input` | The scripts that were run. Each has `-- ==== SECTION` marker lines that divide its transcript into the sections the placeholders name. |
| `build_tutorial.py` | Replaces each placeholder by the commands and results of that section, in a `text` block. |
| `parse_run.py` | Reads a transcript and splits it into sections, commands, results, messages and types. |

## Use

```sh
python3 tools/tutorial/build_tutorial.py           # rewrite docs/tutorial/tutorial.md
python3 tools/tutorial/build_tutorial.py --check   # exit 1, with a diff, if it is out of date
make tutorial-md / make tutorial-md-check          # the same, through make
```

Python 3 only; FriCAS is not needed. `make lint` also runs the check.

The display rules are fixed in `build_tutorial.py` and listed at its head: `)clear`
lines are dropped; macro definitions, declarations and function definitions show no
result; the `Type:` line is dropped when it is `Boolean`, `Void`, `InputForm`,
`String` or a `SymbolicExpression`-family type, because the text says what the type is.
Nothing else is changed. A placeholder that names a missing transcript or section stops
the build.

## Re-recording a transcript

A transcript must come from a run that echoes every input line and prints results in
one-line form: the `run_fricas` tool (project skill `research:fricas`) does both. The
plain log of `fricas -nosman < file` (what `make tutorial` writes) prints results in
two-dimensional form with equation numbers, and the parser does not read it.

1. Compile `src/algebra/gsexpr.spad` and `symterm.spad` in a run of their own, and
   note the run directory. (Or `)compile` them at the top of the script below.)
2. Run this script, with `COMMIT` a pushed commit that contains the `.input` file,
   `DIR` the compile run's directory, and `SCRIPT` one of `tutorial`,
   `known-issue-integrate-first`, `known-issue-sum-first`:

   ```
   )lib )dir DIR
   )lib )dir DIR
   )system curl -sSfo s.input https://raw.githubusercontent.com/billpage/fricas-symbolic/COMMIT/docs/tutorial/SCRIPT.input && sha256sum s.input
   )read s.input
   -- ==== end
   ```

   `)lib` is run twice because of a FriCAS 1.4.0 ordering problem described in the
   `research:fricas` skill. The `-- ==== end` line closes the transcript; the parser
   ignores everything after it.
3. Save the returned text, unchanged from the line `status:` through the
   `-- ==== end` line, as `docs/tutorial/transcripts/NAME.out`. (A tool result over
   about 100 KB is saved to a file by the harness, which is a convenient way to get
   the text exactly; `head -c 100000 /dev/zero | tr '\000' '.'` after the end marker
   makes a short run that long. Cut the dots off before saving.)
4. `python3 tools/tutorial/build_tutorial.py`, read the diff of `tutorial.md`, and
   update the run names and commit in §8 of the template.

Do not edit a transcript by hand. If a result changes, that is the news: look at why
before updating the text around it.
