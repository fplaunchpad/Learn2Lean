# Lean exercise checker (submit & check)

A tiny Flask server that compiles a student's Lean snippet and returns ✓ or the
error. Powers the "Write some Lean" exercises in `web/addition.html`.

It does **not** give a live infoview — it's submit-and-check, which is enough for
the short one-line exercises. On a wrong/unfinished proof, Lean's error message
(returned to the page) includes the goal still left to prove.

## What it does
- `POST /check` with `{ "exercise": "<id>", "code": "<your Lean>" }`
- splices your code into the exercise's scaffold (in `app.py`),
- writes a temp `.lean` file and runs `lake env lean` against this repo,
- returns `{ ok, output }` — `output` is Lean's first error block on failure.
- `GET /` serves `web/addition.html`, so the page and checker share an origin
  (no CORS setup needed).

The scaffolds' reference answers are verified to compile in
`Arithmetic_Formalization/ExerciseScaffolds.lean`.

## What YOU need to do
1. **Build the Lean project once** (so imports resolve fast):
   ```bash
   cd Lean_formalization        # the repo root (has lakefile.toml)
   lake exe cache get
   lake build
   ```
2. **Install Flask and run the server**, from the repo root:
   ```bash
   pip install -r web/checker/requirements.txt
   # point it at this repo if the path differs from the default in app.py:
   #   (Windows)  set LEAN_PROJECT=C:\path\to\Lean_formalization
   #   (mac/linux) export LEAN_PROJECT=/path/to/Lean_formalization
   python web/checker/app.py
   ```
3. Open **http://localhost:5000/addition.html** and use the exercises in §6.
   (Opening the file directly via `file://` also works — the page falls back to
   `http://localhost:5000/check` — but serving through Flask is simplest.)

## Adding exercises
Add an entry to the `EXERCISES` dict in `app.py`: a Lean scaffold string with one
`__CODE__` slot. Add the matching widget in `addition.html` (copy a `WRITE LEAN`
block and call `attachChecker("<id>", …)`). Verify the reference fill compiles by
adding it to `ExerciseScaffolds.lean` and running `lake build`.

## Important caveats
- **Bind to localhost only** (the default). Do **not** expose this to the public
  internet without a sandbox: it runs arbitrary submitted Lean, and `native_decide`
  compiles and runs C. For a class/demo, localhost or a throwaway VM is fine.
- Each check spawns a fresh `lake env lean`, which cold-loads Mathlib, so the
  **first** check can take ~30–60 s; there's a 120 s timeout. Later checks in the
  same session are usually faster (the OS caches the oleans).
- Needs `lake`/Lean on PATH (via `elan`) in the environment running the server.
