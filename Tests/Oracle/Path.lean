/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Lib.Path
import Lanes.Lib.Glob

/-! `Lanes.Path` and `Lanes.Glob` against Go's own tests of `path` and against Go's `path`. -/

namespace Tests.Oracle.Path

open Lanes

/-- Go's `cleantests`, in `path/path_test.go`. -/
def cleanCases : List (String × String) :=
  [("", "."), ("abc", "abc"), ("abc/def", "abc/def"), ("a/b/c", "a/b/c"), (".", "."), ("..", ".."),
    ("../..", "../.."), ("../../abc", "../../abc"), ("/abc", "/abc"), ("/", "/"), ("abc/", "abc"),
    ("abc/def/", "abc/def"), ("a/b/c/", "a/b/c"), ("./", "."), ("../", ".."), ("../../", "../.."),
    ("/abc/", "/abc"), ("abc//def//ghi", "abc/def/ghi"), ("//abc", "/abc"), ("///abc", "/abc"),
    ("//abc//", "/abc"), ("abc//", "abc"), ("abc/./def", "abc/def"), ("/./abc/def", "/abc/def"),
    ("abc/.", "abc"), ("abc/def/ghi/../jkl", "abc/def/jkl"), ("abc/def/../ghi/../jkl", "abc/jkl"),
    ("abc/def/..", "abc"), ("abc/def/../..", "."), ("/abc/def/../..", "/"),
    ("abc/def/../../..", ".."), ("/abc/def/../../..", "/"),
    ("abc/def/../../../ghi/jkl/../../../mno", "../../mno"), ("abc/./../def", "def"),
    ("abc//./../def", "def"), ("abc/../../././../def", "../../def")]

/-- Go's `matchTests`, in `path/match_test.go`, with `none` for `ErrBadPattern`. -/
def matchCases : List (String × String × Option Bool) :=
  [("abc", "abc", some true), ("*", "abc", some true), ("*c", "abc", some true),
    ("a*", "a", some true), ("a*", "abc", some true), ("a*", "ab/c", some false),
    ("a*/b", "abc/b", some true), ("a*/b", "a/c/b", some false),
    ("a*b*c*d*e*/f", "axbxcxdxe/f", some true), ("a*b*c*d*e*/f", "axbxcxdxexxx/f", some true),
    ("a*b*c*d*e*/f", "axbxcxdxe/xxx/f", some false), ("a*b*c*d*e*/f", "axbxcxdxexxx/fff", some false),
    ("a*b?c*x", "abxbbxdbxebxczzx", some true), ("a*b?c*x", "abxbbxdbxebxczzy", some false),
    ("ab[c]", "abc", some true), ("ab[b-d]", "abc", some true), ("ab[e-g]", "abc", some false),
    ("ab[^c]", "abc", some false), ("ab[^b-d]", "abc", some false), ("ab[^e-g]", "abc", some true),
    ("a\\*b", "a*b", some true), ("a\\*b", "ab", some false), ("a?b", "a☺b", some true),
    ("a[^a]b", "a☺b", some true), ("a???b", "a☺b", some false), ("a[^a][^a][^a]b", "a☺b", some false),
    ("[a-ζ]*", "α", some true), ("*[a-ζ]", "A", some false), ("a?b", "a/b", some false),
    ("a*b", "a/b", some false), ("[\\]a]", "]", some true), ("[\\-]", "-", some true),
    ("[x\\-]", "x", some true), ("[x\\-]", "-", some true), ("[x\\-]", "z", some false),
    ("[\\-x]", "x", some true), ("[\\-x]", "-", some true), ("[\\-x]", "a", some false),
    ("[]a]", "]", none), ("[-]", "-", none), ("[x-]", "x", none), ("[x-]", "-", none),
    ("[x-]", "z", none), ("[-x]", "x", none), ("[-x]", "-", none), ("[-x]", "a", none),
    ("\\", "a", none), ("[a-b-c]", "a", none), ("[", "a", none), ("[^", "a", none),
    ("[^bc", "a", none), ("a[", "a", none), ("a[", "ab", none), ("a[", "x", none),
    ("a/b[", "x", none), ("*x", "xxx", some true)]

def tests : List (String × Bool) :=
  [ ("path: clean agrees with Go's tests of path.Clean",
      cleanCases.all fun (p, want) => Path.clean p == want),
    ("path: clean is idempotent on Go's tests", cleanCases.all fun (p, _) => Path.clean (Path.clean p) == Path.clean p),
    ("path: join as Go's path.Join",
      Path.join ["a", "b", "c"] == "a/b/c" && Path.join ["a", ""] == "a" && Path.join ["", ""] == ""
        && Path.join ["", "a"] == "a" && Path.join ["a/", "../b"] == "b" && Path.join ["/", "a"] == "/a"
        && Path.join [] == ""),
    ("path: under keeps a request below its root",
      Path.under "/srv/www" "/a/b.html" == some "/srv/www/a/b.html"
        && Path.under "/srv/www/" "a/../b" == some "/srv/www/b"
        && Path.under "/srv/www" "" == some "/srv/www" && Path.under "/srv/www" "/" == some "/srv/www"
        && Path.under "/" "a//b/" == some "/a/b" && Path.under "public" "x" == some "public/x"
        && Path.under "/srv/www" "../etc/passwd" == none && Path.under "/srv/www" "/a/../../b" == none
        && Path.under "/srv/www" "a/../.." == none && Path.under "/srv/www" "a\x00b" == none
        && Path.under "/srv/www" "a/b/../../c" == some "/srv/www/c"),
    ("glob: matches as Go's tests of path.Match",
      matchCases.all fun (p, n, want) => Glob.check p n == want),
    ("glob: ** as a whole name matches across /",
      [("a/**/b", "a/b", true), ("a/**/b", "a/x/b", true), ("a/**/b", "a/x/y/b", true),
        ("a/**/b", "a/xb", false), ("a/**/b", "ab", false), ("**/b", "b", true), ("**/b", "x/y/b", true),
        ("**/b", "xb", false), ("a/**", "a/x", true), ("a/**", "a/x/y", true), ("a/**", "a", false),
        ("**", "x/y/z", true), ("a**", "ab", true), ("a**", "a/b", false), ("**.lean", "a/b.lean", false),
        ("src/**/*.lean", "src/Lanes/Lib/Path.lean", true), ("src/**/*.lean", "src/Path.lean", true),
        ("src/**/*.lean", "src/a/Path.c", false)].all fun (p, n, want) => Glob.check p n == some want) ]

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "clean", some s => some (.str (Path.clean s))
  | "join", some s => some (.str (Path.join (s.splitOn "\x00")))
  | "match", some s =>
    match s.splitOn "\x00" with
    | [p, n] => (Glob.check p n).map .bool
    | _ => none
  | _, _ => none

def hasWholeDoubleStar (p : String) : Bool :=
  let names := p.splitOn "/"
  names.any (· == "**")

/-- `**` as a whole name is ours; Go reads it as `*`. -/
def known (c : Case) (_ : Answer) : Option String :=
  match c.op, String.fromUTF8? c.input with
  | "match", some s =>
    match s.splitOn "\x00" with
    | [p, _] => if hasWholeDoubleStar p then some "** as a whole name matches across /" else none
    | _ => none
  | _, _ => none

def pathGen : Gen String := do
  let names ← Gen.list (← Gen.below 7) (Gen.pick ["a", "bc", ".", "..", "", "é", ".a", "...", "a."])
  return (← Gen.pick ["", "", "/", "//"]) ++ "/".intercalate names ++ (← Gen.pick ["", "", "/"])

def patternAlphabet : List Char := "ab*?[]^-\\/é".toList

def case : Gen Case := do
  match ← Gen.below 3 with
  | 0 => return text (← pathGen) "clean"
  | 1 => return text ("\x00".intercalate (← Gen.list (← Gen.below 4) pathGen)) "join"
  | _ =>
    let p ← Gen.text patternAlphabet 8
    let n ← if ← Gen.chance 40 then
        Gen.mutate "ab/-]".toList (String.ofList (p.toList.map fun c => if c == '*' || c == '?' then 'a' else c))
      else Gen.text "ab/-]\\*^é".toList 8
    return text (p ++ "\x00" ++ n) "match"

def edges : List Case :=
  cleanCases.map (text ·.1 "clean") ++ matchCases.map fun (p, n, _) => text (p ++ "\x00" ++ n) "match"

def package : Package where
  name := "path"
  edges
  case
  answer
  known
  shrinks := false

end Tests.Oracle.Path
