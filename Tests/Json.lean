/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Tests of the JSON library: the parser against RFC 8259 on well-formed and malformed input, the
printers, the round trip `parse (compress j) = j` on a hand-written corpus, and the `ToJson` and
`FromJson` instances.
-/

namespace Tests.Json

/-- Results are compared in these tests. Core Lean has no `BEq` for `Except`. -/
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

open Lanes

def parsesTo (text : String) (expected : Json) : Bool :=
  match Json.parse text with
  | .ok j => j == expected
  | .error _ => false

def rejects (text : String) : Bool :=
  match Json.parse text with
  | .ok _ => false
  | .error _ => true

def failsWith (text message : String) : Bool :=
  match Json.parse text with
  | .ok _ => false
  | .error e => e == message

def nested : (depth : Nat) → Json
  | 0 => .null
  | depth + 1 => .arr #[nested depth]

def nestedText (depth : Nat) : String :=
  "".pushn '[' depth ++ "null" ++ "".pushn ']' depth

/-- Numbers of every shape: zero, negative, fractional, tiny, and too large for a machine word. -/
def numbers : List Json :=
  [ 0, 1, 42, .num (-1), .num (-17), .num 1.5, .num (-0.001), .num 3.14159, .num 1e-7,
    .num 1e-30, .num (-2.5e-12), .num 1e30, .num 12345678901234567890123456789012345678901234567890,
    .num (-98765432109876543210.0123456789), .num 100, .num 0.1, .num 120.034 ]

/-- Strings with quotes, backslashes, control characters and non-ASCII text. -/
def strings : List Json :=
  [ "", "plain", "with space", "quote \" backslash \\ slash /", "line\nbreak\r\ttab",
    "controls \x00 \x01 \x08 \x0c \x1f \x7f", "é ü ß", "日本語", "😀 🎉", "\u2028 \u2029 \uffff",
    "\\u0041 is not an escape here", "null", "[1,2]" ]

def containers : List Json :=
  [ .arr #[], .mkObj [], .arr #[.arr #[], .mkObj []], .arr #[1, "a", .null, true, false, .num 1.5],
    .mkObj [("b", 1), ("a", "x")],
    .mkObj [("", "empty key"), ("ключ", "значение"), ("quote\"key", 1), ("line\nkey", .null)],
    .mkObj [("list", .arr #[1, 2, .mkObj [("deep", .arr #[.arr #[.arr #[true]]])]]),
            ("object", .mkObj [("x", .num (-1.5)), ("y", .mkObj [("z", "w")])])],
    nested 100 ]

def corpus : List Json :=
  [.null, .bool true, .bool false] ++ numbers ++ strings ++ containers

def sample : Json :=
  .mkObj [("name", "Ada"), ("tags", .arr #["a", "b"]), ("age", 36), ("empty", .arr #[]),
          ("nested", .mkObj [("ok", true), ("none", .null), ("unit", .mkObj [])])]

def roundTrips {α : Type} [ToJson α] [FromJson α] [BEq α] (a : α) : Bool :=
  match Json.parse (toJson a).compress with
  | .ok j =>
    match (fromJson? j : Except String α) with
    | .ok b => b == a
    | .error _ => false
  | .error _ => false

def undecodable (α : Type) [FromJson α] (j : Json) : Bool :=
  match (fromJson? j : Except String α) with
  | .ok _ => false
  | .error _ => true

def parserTests : List (String × Bool) :=
  [ ("json: literals and surrounding whitespace",
      parsesTo "null" .null && parsesTo " true\n" (.bool true) &&
      parsesTo "\t\r\nfalse " (.bool false)),
    ("json: numbers with signs, fractions and exponents",
      parsesTo "0" 0 && parsesTo "-0" 0 && parsesTo "-12.340e5" (.num (-1234000)) &&
      parsesTo "1E-3" (.num 0.001) && parsesTo "1e+2" 100 && parsesTo "1e01" 10 &&
      parsesTo "0.0" 0 && parsesTo "100e-2" 1 && parsesTo "1.50" (.num 1.5) &&
      parsesTo "123456789012345678901234567890" (.num 123456789012345678901234567890)),
    ("json: string escapes, \\u escapes and surrogate pairs",
      parsesTo "\"a\\\"b\\\\c\\/d\\b\\f\\n\\r\\t\"" "a\"b\\c/d\x08\x0c\n\r\t" &&
      parsesTo "\"\\u00e9\\u00E9\\u65e5\"" "éé日" && parsesTo "\"\\ud83d\\ude00\"" "😀" &&
      parsesTo "\"\\uD834\\uDD1E\"" "𝄞" && parsesTo "\"\\u0000\"" "\x00" &&
      parsesTo "\"é 😀 \x7f\"" "é 😀 \x7f"),
    ("json: arrays and objects with whitespace everywhere",
      parsesTo " [ ] " (.arr #[]) && parsesTo " { } " (.mkObj []) &&
      parsesTo "[1 , [2,[ 3 ]],\n{\"a\" : null} ]"
        (.arr #[1, .arr #[2, .arr #[3]], .mkObj [("a", .null)]])),
    ("json: object fields are sorted by key, whatever their order in the text",
      parsesTo "{\"b\":1,\"a\":2,\"c\":3}" (.obj #[("a", 2), ("b", 1), ("c", 3)]) &&
      Json.parse "{\"b\":1,\"a\":{\"y\":1,\"x\":2}}" ==
        Json.parse "{\"a\":{\"x\":2,\"y\":1},\"b\":1}"),
    ("json: an error names its byte offset",
      failsWith "[1,]" "offset 3: JSON value expected" &&
      failsWith "\"é\\x\"" "offset 4: invalid escape sequence" &&
      failsWith "[1] x" "offset 4: end of input expected") ]

def rejectionTests : List (String × Bool) :=
  [ ("json: rejects empty input", rejects "" && rejects " \n"),
    ("json: rejects trailing, leading and missing commas",
      rejects "[1,]" && rejects "{\"a\":1,}" && rejects "[,1]" && rejects "[1,,2]" &&
      rejects "[1 2]" && rejects "{\"a\":1 \"b\":2}" && rejects "{,}"),
    ("json: rejects unterminated strings, arrays and objects",
      rejects "\"abc" && rejects "\"abc\\\"" && rejects "\"\\" && rejects "[1" && rejects "[1," &&
      rejects "{\"a\":1" && rejects "{\"a\":" && rejects "{\"a\"" && rejects "{" && rejects "["),
    ("json: rejects bad escapes",
      rejects "\"\\x\"" && rejects "\"\\a\"" && rejects "\"\\u12\"" && rejects "\"\\u12g4\"" &&
      rejects "\"\\U0041\"" && rejects "\"\\ \""),
    ("json: rejects lone surrogates",
      rejects "\"\\ud83d\"" && rejects "\"\\ud83dx\"" && rejects "\"\\ude00\"" &&
      rejects "\"\\ud83d\\u0041\"" && rejects "\"\\ud83d\\ud83d\"" && rejects "\"\\ud83d\\n\""),
    ("json: rejects raw control characters in strings",
      rejects "\"a\nb\"" && rejects "\"a\tb\"" && rejects "\"\x00\"" && rejects "\"\x1f\""),
    ("json: rejects leading zeros and malformed numbers",
      rejects "01" && rejects "-01" && rejects "00" && rejects "[1, 007]" && rejects "+1" &&
      rejects "-" && rejects "1." && rejects ".5" && rejects "1e" && rejects "1e+" &&
      rejects "1.e3" && rejects "0x10" && rejects "1_000" && rejects "--1"),
    ("json: rejects trailing garbage",
      rejects "1 2" && rejects "true false" && rejects "{} x" && rejects "[1]]" &&
      rejects "nulll" && rejects "\"a\" \"b\"" && rejects "[1] // comment"),
    ("json: rejects what is not JSON",
      rejects "nul" && rejects "True" && rejects "NaN" && rejects "Infinity" && rejects "'a'" &&
      rejects "{a:1}" && rejects "{1:2}" && rejects "{\"a\" 1}" && rejects "undefined"),
    ("json: a key given twice keeps its last value",
      parsesTo "{\"a\":1,\"a\":2}" (.obj #[("a", 2)]) &&
      parsesTo "{\"a\":1,\"b\":2,\"a\":3}" (.obj #[("a", 3), ("b", 2)]) &&
      parsesTo "{\"\\u0061\":1,\"a\":2}" (.obj #[("a", 2)]) &&
      parsesTo "{\"a\":1,\"A\":2}" (.obj #[("A", 2), ("a", 1)])),
    ("json: nesting up to the depth limit is accepted, one level more is rejected",
      parsesTo (nestedText 128) (nested 128) && rejects (nestedText 129) &&
      failsWith (nestedText 129) "offset 128: maximum nesting depth exceeded"),
    ("json: the depth limit is a parameter and counts objects too",
      (Json.parse "[[1]]" (maxDepth := 2)).isOk && !(Json.parse "[[1]]" (maxDepth := 1)).isOk &&
      !(Json.parse "{\"a\":[1]}" (maxDepth := 1)).isOk && (Json.parse "1" (maxDepth := 0)).isOk &&
      !(Json.parse "[]" (maxDepth := 0)).isOk &&
      (Json.parse (nestedText 2000) (maxDepth := 2000)).isOk),
    ("json: exponents up to the limit are accepted, larger ones are rejected",
      !rejects "1e1000" && !rejects "1e-1000" && rejects "1e1001" && rejects "1e-1001" &&
      rejects "1e99999999999999999999" && !(Json.parse "1e5" (maxDigits := 4)).isOk &&
      (Json.parse "1e4" (maxDigits := 4)).isOk &&
      parsesTo "1e-1000" (.num (.ofScientific 1 (-1000)))),
    ("json: numbers up to the digit limit are accepted, longer ones are rejected",
      !rejects ("".pushn '7' 1000) && rejects ("".pushn '7' 1001) &&
      !rejects ("".pushn '7' 400 ++ "." ++ "".pushn '7' 600) &&
      rejects ("".pushn '7' 400 ++ "." ++ "".pushn '7' 601) &&
      rejects ("1e" ++ "".pushn '0' 1001) && (Json.parse "12.34" (maxDigits := 4)).isOk &&
      !(Json.parse "12.345" (maxDigits := 4)).isOk &&
      Json.parse "[123456]" (maxDigits := 5) == .error "offset 6: number longer than 5 digits") ]

def printerTests : List (String × Bool) :=
  [ ("json: compress writes no whitespace and sorts keys",
      sample.compress ==
        "{\"age\":36,\"empty\":[],\"name\":\"Ada\"," ++
        "\"nested\":{\"none\":null,\"ok\":true,\"unit\":{}},\"tags\":[\"a\",\"b\"]}"),
    ("json: pretty writes one element or field per line",
      (Json.arr #[1, .mkObj [("a", .arr #[]), ("b", .arr #[true, .mkObj []])]]).pretty ==
        "[\n  1,\n  {\n    \"a\": [],\n    \"b\": [\n      true,\n      {}\n    ]\n  }\n]" &&
      (Json.arr #[]).pretty == "[]" && (Json.mkObj []).pretty == "{}" &&
      (Json.arr #[.null]).pretty (indent := 4) == "[\n    null\n]"),
    ("json: strings are escaped, non-ASCII text is not",
      (Json.str "a\"b\\c/d").compress == "\"a\\\"b\\\\c/d\"" &&
      (Json.str "\n\r\t\x08\x0c").compress == "\"\\n\\r\\t\\b\\f\"" &&
      (Json.str "\x00\x01\x1f\x7f").compress == "\"\\u0000\\u0001\\u001f\x7f\"" &&
      (Json.str "é 日本語 😀 \u2028").compress == "\"é 日本語 😀 \u2028\"" &&
      (Json.mkObj [("k\"\n", 1)]).compress == "{\"k\\\"\\n\":1}"),
    ("json: numbers print exactly, in scientific notation only when tiny",
      (numbers.map Json.compress) ==
        ["0", "1", "42", "-1", "-17", "1.5", "-0.001", "3.14159", "0.0000001", "1e-30", "-2.5e-12",
         "1000000000000000000000000000000", "12345678901234567890123456789012345678901234567890",
         "-98765432109876543210.0123456789", "100", "0.1", "120.034"]),
    ("json: parse (compress j) = j on the corpus",
      corpus.length == 41 && corpus.all fun j => parsesTo j.compress j),
    ("json: parse (pretty j) = j on the corpus", corpus.all fun j => parsesTo j.pretty j),
    ("json: compress (parse text) is a fixed point",
      corpus.all fun j => (Json.parse j.compress).map Json.compress == .ok j.compress) ]

def valueTests : List (String × Bool) :=
  [ ("json: equal numbers are equal values",
      (1.50 : JsonNumber) == 1.5 && (1.0 : JsonNumber) == 1 && (100e-2 : JsonNumber) == 1 &&
      (0.0 : JsonNumber) == 0 && (-0.0 : JsonNumber) == 0 && (1.5 : JsonNumber) != 1.05 &&
      hash (1.50 : JsonNumber) == hash (1.5 : JsonNumber)),
    ("json: objects are equal and hash alike whatever order their fields were given in",
      Json.mkObj [("b", 1), ("a", "x")] == Json.mkObj [("a", "x"), ("b", 1)] &&
      hash (Json.mkObj [("b", 1), ("a", "x")]) == hash (Json.mkObj [("a", "x"), ("b", 1)]) &&
      Json.mkObj [("a", 1)] != Json.mkObj [("a", 2)] &&
      Json.mkObj [("a", 1)] != Json.mkObj [("b", 1)] &&
      Json.arr #[1, 2] != Json.arr #[2, 1] && Json.arr #[] != Json.mkObj [] &&
      Json.str "1" != (1 : Json) && Json.null != Json.bool false),
    ("json: mkObj keeps the last of two fields with one key, mkObj? rejects them",
      Json.mkObj [("a", 1), ("b", 2), ("a", 3)] == .obj #[("a", 3), ("b", 2)] &&
      (Json.mkObj? [("a", 1), ("b", 2), ("a", 3)]).isOk == false &&
      (Json.mkObj? [("b", 2), ("a", 1)]).toOption == some (.obj #[("a", 1), ("b", 2)])),
    ("json: accessors return the value or an error",
      sample.getObjVal? "name" == .ok "Ada" && !(sample.getObjVal? "missing").isOk &&
      !((1 : Json).getObjVal? "name").isOk && sample.getObjValD "missing" == .null &&
      (sample.getObjValD "tags").getArrVal? 1 == .ok "b" &&
      !((sample.getObjValD "tags").getArrVal? 2).isOk &&
      (sample.getObjValD "age").getNat? == .ok 36 && (Json.num (-3)).getInt? == .ok (-3) &&
      !(Json.num (-3)).getNat?.isOk && !(Json.num 1.5).getInt?.isOk &&
      !(Json.str "1").getNat?.isOk &&
      (Json.bool true).getBool? == .ok true && (Json.str "s").getStr? == .ok "s" &&
      (Json.num 1.5).getNum? == .ok 1.5 && (Json.arr #[1]).getArr? == .ok #[1] &&
      Json.null.isNull && !(Json.bool false).isNull),
    ("json: Repr prints the term that builds the value",
      reprStr (Json.arr #[1, .mkObj [("a", .null)]]) ==
        "Lanes.Json.arr #[Lanes.Json.num (Lanes.JsonNumber.ofDecimal 1 0), " ++
        "Lanes.Json.obj #[(\"a\", Lanes.Json.null)]]"),
    ("json: Bool, Nat, Int, String, Fin and Unit round-trip",
      roundTrips true && roundTrips false && roundTrips (0 : Nat) && roundTrips (2 ^ 80 : Nat) &&
      roundTrips (-5 : Int) && roundTrips (-(2 : Int) ^ 70) && roundTrips "" &&
      roundTrips "é \"quoted\"\n😀" && roundTrips (3 : Fin 5) && roundTrips ()),
    ("json: Option, List, Array and pairs round-trip",
      roundTrips (some 3 : Option Nat) && roundTrips (none : Option Nat) &&
      roundTrips ([] : List Nat) && roundTrips [1, 2, 3] && roundTrips #["a", "b"] &&
      roundTrips ((1 : Nat), "one") && roundTrips [((1 : Int), some true), (-2, none)] &&
      roundTrips (#[[some "x", none], []], ((), (4 : Fin 9))) && roundTrips sample &&
      roundTrips (1.25 : JsonNumber)),
    ("json: instances encode as documented",
      (toJson ((some (-5 : Int), (none : Option Nat)), ((), #[true, false]))).compress ==
        "[[-5,null],[{},[true,false]]]" && toJson [1, 2] == Json.arr #[1, 2]),
    ("json: decoding the wrong shape fails",
      undecodable Nat (.num (-1)) && undecodable Nat (.num 1.5) && undecodable Nat "1" &&
      undecodable Int (.num 0.5) && undecodable Bool 1 && undecodable String .null &&
      undecodable (Fin 3) 3 && undecodable Unit (.arr #[]) && undecodable (List Nat) (.mkObj []) &&
      undecodable (List Nat) (.arr #[1, "2"]) && undecodable (Nat × Nat) (.arr #[1, 2, 3]) &&
      undecodable (Nat × Nat) (.arr #[1, "2"]) && undecodable (Option Nat) "x"),
    ("json: getObjValAs? decodes a field, opt leaves out a missing one",
      (sample.getObjValAs? String "name").toOption == some "Ada" &&
      (sample.getObjValAs? (List String) "tags").toOption == some ["a", "b"] &&
      (sample.getObjValAs? (Option Nat) "missing").toOption == some none &&
      !(sample.getObjValAs? Nat "missing").isOk && !(sample.getObjValAs? Nat "name").isOk &&
      Json.mkObj (Json.opt "a" (some 1) ++ Json.opt "b" (none : Option Nat)) == .obj #[("a", 1)]) ]

def tests : List (String × Bool) :=
  parserTests ++ rejectionTests ++ printerTests ++ valueTests

/-!
The parsing tests of JSONTestSuite (github.com/nst/JSONTestSuite, MIT licence, in
`Tests/data/JSONTestSuite`): a `y_` file must be accepted and print to text that parses to the
same value, an `n_` file must be refused, and an `i_` file, which RFC 8259 leaves to the
implementation, must do what `acceptedByChoice` records. A file that is not UTF-8 is refused
before it reaches the parser, as an adapter refuses it.
-/

def suiteDir : System.FilePath := "Tests" / "data" / "JSONTestSuite"

/-- Two files of the suite are built here rather than stored: they are 350 kB of one pattern. -/
def builtFiles : List (String × ByteArray) :=
  [ ("n_structure_100000_opening_arrays.json", ("".pushn '[' 100000).toUTF8),
    ("n_structure_open_array_object.json",
      (String.join (List.replicate 50000 "[{\"\":") ++ "\n").toUTF8) ]

def acceptedByChoice : List String :=
  [ "i_number_double_huge_neg_exp.json", "i_number_too_big_neg_int.json",
    "i_number_too_big_pos_int.json", "i_number_very_big_negative_int.json" ]

def suiteOutcome (name : String) (bytes : ByteArray) : Option Bool :=
  let parsed := (String.fromUTF8? bytes).map Json.parse
  let accepted := match parsed with
    | some (.ok j) => Json.parse j.compress == .ok j
    | _ => false
  let refused := match parsed with
    | some (.ok _) => false
    | _ => true
  if name.startsWith "y_" then some accepted
  else if name.startsWith "n_" then some refused
  else if name.startsWith "i_" then
    some (if acceptedByChoice.contains name then accepted else refused)
  else none

def suite : IO (List (String × Bool)) := do
  let entries ← suiteDir.readDir
  let stored ← entries.toList.mapM fun entry => do
    return (entry.fileName, ← IO.FS.readBinFile entry.path)
  let files := (stored ++ builtFiles).filterMap fun (name, bytes) =>
    (suiteOutcome name bytes).map fun ok => (s!"json suite: {name}", ok)
  return ("json suite: every file is there", files.length == 318) :: files

end Tests.Json
