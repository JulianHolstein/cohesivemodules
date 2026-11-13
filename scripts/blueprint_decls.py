#!/usr/bin/env python3
"""Dump the project's declarations for the blueprint generator (documentation plan B3, B10).

Runs a Lean program against the compiled environment (`import Cohesivemodules`) and writes one
JSON object per project constant (module prefix `Cohesivemodules.`) to
`blueprint/.cache/decls.jsonl`:

  n  name               k  kind (def, abbrev, theorem, instance, structure, inductive, ...)
  m  module             p  private?          i  internal detail (aux, match, proof_...)?
  d  docstring or null  u  project constants used by the type and the value (proofs included)

Proofs are included in `u` on purpose: the blueprint's `\\uses` edges are informal dependencies,
which include those of proofs. `scripts/blueprint_gen.py` reads the file to seed the item ->
Lean-name table (B10) and to check the `\\uses` edges against the Lean dependencies (B3).

Usage: scripts/blueprint_decls.py [--out PATH]
Needs a built project (`lake build`).
"""
import os
import subprocess
import sys
import tempfile

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_OUT = os.path.join(ROOT_DIR, 'blueprint', '.cache', 'decls.jsonl')

LEAN = r'''
import Cohesivemodules
open Lean Meta Elab Command

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "Cohesivemodules"
  | none => false

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if isInstanceCore env n then "instance" else if isStructure env n then "structure" else
  match ci with
  | .defnInfo d => if d.hints.isAbbrev then "abbrev" else "def"
  | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let path := (← IO.getEnv "BP_DECLS_OUT").getD "decls.jsonl"
  let h ← IO.FS.Handle.mk path .write
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    unless isProject env n do continue
    let mut used : NameSet := {}
    for c in ci.type.getUsedConstants do
      if isProject env c && c != n then used := used.insert c
    if let some v := ci.value? (allowOpaque := true) then
      for c in v.getUsedConstants do
        if isProject env c && c != n then used := used.insert c
    if let .inductInfo d := ci then
      for c in d.ctors do used := used.insert c
    let doc ← findDocString? env n
    let mod := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => ""
    let j := Json.mkObj [("n", toJson n.toString), ("k", toJson (kindOf env n ci)),
      ("m", toJson mod), ("p", toJson (isPrivateName n)), ("i", toJson n.isInternalDetail),
      ("d", toJson doc), ("u", toJson (used.toList.map (·.toString)))]
    h.putStrLn j.compress
    count := count + 1
  logInfo m!"{count} project constants written to {path}"
'''


def main(argv):
    out = DEFAULT_OUT
    if '--out' in argv:
        out = os.path.abspath(argv[argv.index('--out') + 1])
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write(LEAN)
        path = f.name
    try:
        env = dict(os.environ, BP_DECLS_OUT=out)
        res = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT_DIR, env=env,
                             capture_output=True, text=True)
    finally:
        os.unlink(path)
    if res.returncode != 0:
        sys.stderr.write('Lean failed:\n' + res.stdout[-4000:] + res.stderr[-4000:])
        return 1
    print(res.stdout.strip().splitlines()[-1] if res.stdout.strip() else f'written to {out}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
