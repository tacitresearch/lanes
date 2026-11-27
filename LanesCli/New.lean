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
  /-- `why` is written above it, as comments of the lakefile. -/
  | git (url rev : String) (why : List String := [])
  /-- A local checkout, for developing Lanes itself. -/
  | path (dir : String)

def Source.toToml : Source → String
  | .git url rev why =>
    String.join (why.map (s!"# {·}\n")) ++ s!"git = \"{url}\"\nrev = \"{rev}\""
  | .path dir => s!"path = \"{dir}\""

def repository : String := "https://github.com/tacitresearch/lanes"

/-- What the lakefile requires when `lanes new` is given no `--rev`: the release tag of the
checkout it runs from, else that checkout's commit. Either way the app builds against the Lanes
it was made with, and a later `lake update` does not move it, as it would move `main`. -/
def pinned (tag? : Option String) (commit : String) (released : Bool) : Source :=
  let move := "To move to another version, change `rev` and run `lake update lanes`."
  match tag? with
  | some tag => .git repository tag [s!"Lanes {tag}, the release this app was made from.", move]
  | none =>
    let why := if released then "No release tag of Lanes is at the commit this app was made from"
      else "Lanes has no release yet"
    .git repository commit [s!"{why}, so this is the commit of Lanes it was made from.", move]

private def runGit (dir : System.FilePath) (args : List String) : IO (Option String) := do
  let out ← try
      IO.Process.output { cmd := "git", args := #["-C", dir.toString] ++ args.toArray }
    catch _ => return none
  if out.exitCode != 0 then return none
  let text := out.stdout.trimAscii.toString
  return if text.isEmpty then none else some text

/-- What `pinned` gives for the checkout this executable was built in
(`<checkout>/.lake/build/bin/lanes`), or `none` if git cannot say. -/
def ofCheckout : IO (Option Source) := do
  let some dir := (← IO.appPath).parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | return none
  let some commit ← runGit dir ["rev-parse", "HEAD"] | return none
  let tag? ← runGit dir ["describe", "--tags", "--exact-match", "--match", "v*", "HEAD"]
  let released := (← runGit dir ["tag", "--list", "v*"]).isSome
  return some (pinned tag? commit released)

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
