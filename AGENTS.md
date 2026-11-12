# AGENTS.md

;Notes for an AI agent (Claude Code or otherwise) working in this repo.

## Tool-call reliability: avoid large/repetitive inline string parameters

During the session that added `ERecMut`/`VClosureMut` (mutual recursion)
and the records feature before it, `Edit`/`Write`/`Bash` tool calls
failed repeatedly and in several distinct ways whenever a parameter
value was long and/or highly repetitive:

- `Edit`/`Write` calls failing with `InputValidationError: ... type is
  expected as string but provided as unknown`, with no file change
  applied -- this happened specifically on `old_string`/`new_string`
  values that were long, deeply nested, and/or contained many repeated
  identical substrings (e.g. Json.v's cascading `match expect ... with`
  parser, whose closing line is 30+ repetitions of the literal word
  `end`; deeply nested `""tag"":""..."` JSON text).
- Generated text itself getting corrupted mid-flight: specific words or
  paths silently gaining/losing characters on retype (`claude-1001` ->
  `claaude-1001`/`cla-1001`/`clode-1001`, `cat` -> `findat`, `Not yet`
  -> `Notot yet`, `open(path` -> `open open open(path`). This is not a
  shell-quoting bug (plain commands with no special characters failed
  the same way) -- it is specifically triggered by re-typing the *same*
  long, low-entropy token (a long path, a repeated word) many times
  across nearby tool calls.
- Occasionally emitting malformed tool-call XML directly in a response
  (missing the `antml:` prefix, mismatched parameter tags), which
  surfaces to the user as a garbled/failed turn rather than a clean
  tool error.
- Stray junk files silently created on disk by the malformed commands
  above (e.g. a bash command whose intended argument got mis-parsed
  into a bare word, which the shell then treated as a redirect target)
  -- always `git status`/`ls` and clean these up before committing.

None of this is a Coq/project problem -- it is a tool-calling
reliability problem, and it gets *worse*, not better, the more times a
long literal string gets retyped in one stretch of the conversation.

### What to do instead

1. **Never hand-edit a large or highly repetitive block via `Edit`'s
   `old_string`/`new_string`.** If a change involves >1 repeated-token
   line (e.g. "N copies of `end`", a long auto-generated JSON literal,
   a big mechanical find/replace across many near-identical call
   sites), write a small Python script with `Write`, run it with
   `Bash`, and have *it* do the substitution with an explicit `assert`
   on the expected input shape before writing. This is strictly more
   reliable than a giant inline Edit, and the `assert` catches drift
   immediately instead of silently corrupting the file.
2. **Never retype a long/low-entropy identifier (a scratch-dir path, a
   repeated word) from memory more than once.** Get it from a tool
   result and reuse it: `find`/`ls`/`grep` once, then copy the exact
   string that command printed into the next call rather than retyping
   it. If a `Bash` command with such a path fails with "No such file or
   directory" on a path that was just listed successfully, do **not**
   retry the same spelling hoping it works -- re-derive the path via
   `find` (e.g. `find /tmp -maxdepth 1 -iname '*1001*'`) and use
   whatever it prints, verbatim.
3. **After any tool-call `InputValidationError` or "failed to produce a
   valid tool call" message, switch strategy on the next attempt
   instead of resubmitting the same call.** Repeating the identical
   call tends to fail identically. Prefer: shrink the change, split it
   into smaller Edits, or move the logic into a script file.
4. **Verify ground truth before constructing an `old_string`.** Re-read
   the exact file region with `Read` (or `grep -n`) immediately before
   writing an `Edit` for it, rather than relying on a value echoed back
   in a previous (possibly garbled) error message -- those echoes have
   shown stray duplicated characters that were never actually written
   to disk.
5. **After a stretch of tool-call failures, run `git status` before
   committing anything.** Malformed commands in this session left
   empty/junk files behind (e.g. a bare word from a broken redirect
   turning into a 0-byte or multi-MB accidental file); these are not
   proof of a working change and must be removed, not committed.
