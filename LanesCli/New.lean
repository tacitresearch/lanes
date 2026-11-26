/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# `lanes new`

Creates a new application from the template in `templates/app`. The template is a starting
point, not a convention: the files are yours to reshape.
-/

namespace Lanes.Cli.New

/-- Where a generated application gets Lanes from. -/
inductive Source where
  | git (url rev : String)
  /-- A local checkout, for developing Lanes itself. -/
  | path (dir : String)

def Source.toToml : Source → String
  | .git url rev => s!"git = \"{url}\"\nrev = \"{rev}\""
  | .path dir => s!"path = \"{dir}\""

/-- `my-app` becomes `MyApp`: the Lean module name of an application. -/
def moduleName (name : String) : String :=
  String.join ((name.split fun c => c == '-' || c == '_').toList.map fun part =>
    part.toString.capitalize)

def validName (name : String) : Bool :=
  match name.toList with
  | c :: _ => c.isLower && name.all fun c => c.isLower || c.isDigit || c == '-' || c == '_'
  | [] => false

def files : List (String × String) :=
  [ ("lakefile.toml", include_str "../templates/app/lakefile.toml.tmpl"),
    ("{{Name}}/Counter.lean", include_str "../templates/app/Counter.lean.tmpl"),
    ("{{Name}}/Proofs.lean", include_str "../templates/app/Proofs.lean.tmpl"),
    ("Check.lean", include_str "../templates/app/Check.lean.tmpl"),
    ("Main.lean", include_str "../templates/app/Main.lean.tmpl"),
    ("AGENTS.md", include_str "../templates/app/AGENTS.md.tmpl"),
    ("TRUSTED.md", include_str "../templates/app/TRUSTED.md.tmpl"),
    (".gitignore", include_str "../templates/app/gitignore.tmpl"),
    ("lean-toolchain", include_str "../lean-toolchain") ]

def fill (name : String) (source : Source) (text : String) : String :=
  text.replace "{{name}}" name |>.replace "{{Name}}" (moduleName name)
    |>.replace "{{lanes_source}}" source.toToml

def run (name : String) (dir : System.FilePath) (source : Source) : IO UInt32 := do
  if !validName name then
    IO.eprintln s!"lanes new: '{name}' is not a valid name; use lowercase letters, digits, - and _"
    return 1
  if ← dir.pathExists then
    IO.eprintln s!"lanes new: {dir} already exists"
    return 1
  for (path, contents) in files do
    let target := dir / fill name source path
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeFile target (fill name source contents)
  IO.println s!"Created {dir}. Next:"
  IO.println s!"  cd {dir}"
  IO.println "  lake exe cache get"
  IO.println "  lake test"
  IO.println s!"  lake exe {name}"
  return 0

end Lanes.Cli.New
