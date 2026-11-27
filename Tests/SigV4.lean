/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Signature Version 4 against AWS's test suite and the S3 examples of AWS's documentation.

The suite's cases are AWS's `aws4_testsuite` (as botocore keeps it under
`tests/unit/auth/aws4_testsuite`), each its request, its canonical request and its
`Authorization`, with the suite's key `AKIDEXAMPLE` on 2015-08-30 for the service `service`.
The S3 cases are the examples of "Signature Calculations for the Authorization Header:
Transferring Payload in a Single Chunk" and "Authenticating Requests: Using Query Parameters",
with the documentation's key `AKIAIOSFODNN7EXAMPLE` on 2013-05-24; botocore computes the same
signatures for the GET, list, lifecycle and presigned examples. The suite's cases that normalize
a path (`get-slash`, `get-relative`) are for services that S3 is not and are left out, as is
`get-header-value-multiline`, a folded header the client cannot send.
-/

namespace Tests.SigV4

open Lanes Lanes.SigV4 Lanes.Http

def suiteTime : Civil.DateTime := Civil.DateTime.ofUnix 1440938160

def suiteKey : Credentials :=
  { accessKeyId := "AKIDEXAMPLE", secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"⟩ }

def suiteScope : Scope := ⟨"us-east-1", "service"⟩

def emptyHash : String := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

/-- A case of the suite: its request, and its canonical request and signature as AWS gives
them. -/
structure Case where
  name : String
  verb : String := "GET"
  path : List String := []
  query : List (String × String) := []
  headers : List (String × String) := []
  body : String := ""
  canonical : String
  signature : String

def suiteHeaders (more : List (String × String) := []) : List (String × String) :=
  [("Host", "example.amazonaws.com")] ++ more ++ [("X-Amz-Date", "20150830T123600Z")]

def plainCanonical (verb : String) (query : String := "") : String :=
  verb ++ "\n/\n" ++ query ++ "\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\n"
    ++ "host;x-amz-date\n" ++ emptyHash

def oneHeaderCanonical (verb header : String) : String :=
  verb ++ "\n/\n\nhost:example.amazonaws.com\n" ++ header ++ "\nx-amz-date:20150830T123600Z\n\n"
    ++ "host;my-header1;x-amz-date\n" ++ emptyHash

def unreserved : String := "-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

def token : String :=
  "AQoDYXdzEPT//////////wEXAMPLEtc764bNrC9SAPBSM22wDOk4x4HIZ8j4FZTwdQWLWsKWHGBuFqwAeMicRXmxfpSPf"
    ++ "IeoIYRqTflfKD8YUuwthAx7mSEI/qkPpKPi/kMcGdQrmGdeehM4IC1NtBmUpp2wUE8phUZampKsburEDy0KPkyQDYwT7W"
    ++ "Z0wq5VSXDvp75YU9HFvlRd8Tx6q6fE8YQcHNVXAkiY9q6d+xo0rKwT38xVqr7ZD0u0iPPkUL64lIZbqBAz+scqKmlzm8F"
    ++ "DrypNC9Yjc8fPOLn9FX9KSYvKTr4rvx3iSIlTJabIQwj2ICCR/oLxBA=="

def suite : List Case := [
  { name := "get-vanilla", headers := suiteHeaders, canonical := plainCanonical "GET",
    signature := "5fa00fa31553b73ebf1942676e86291e8372ff2a2260956d9b8aae1d763fbf31" },
  { name := "get-vanilla-empty-query-key", query := [("Param1", "value1")],
    headers := suiteHeaders, canonical := plainCanonical "GET" "Param1=value1",
    signature := "a67d582fa61cc504c4bae71f336f98b97f1ea3c7a6bfe1b6e45aec72011b9aeb" },
  { name := "get-vanilla-query-order-key", query := [("Param1", "value2"), ("Param1", "Value1")],
    headers := suiteHeaders, canonical := plainCanonical "GET" "Param1=Value1&Param1=value2",
    signature := "eedbc4e291e521cf13422ffca22be7d2eb8146eecf653089df300a15b2382bd1" },
  { name := "get-vanilla-query-order-key-case",
    query := [("Param2", "value2"), ("Param1", "value1")], headers := suiteHeaders,
    canonical := plainCanonical "GET" "Param1=value1&Param2=value2",
    signature := "b97d918cfa904a5beff61c982a1b6f458b799221646efd99d3219ec94cdf2500" },
  { name := "get-vanilla-query-order-value", query := [("Param1", "value2"), ("Param1", "value1")],
    headers := suiteHeaders, canonical := plainCanonical "GET" "Param1=value1&Param1=value2",
    signature := "5772eed61e12b33fae39ee5e7012498b51d56abc0abb7c60486157bd471c4694" },
  { name := "get-vanilla-query-unreserved", query := [(unreserved, unreserved)],
    headers := suiteHeaders, canonical := plainCanonical "GET" (unreserved ++ "=" ++ unreserved),
    signature := "9c3e54bfcdf0b19771a7f523ee5669cdf59bc7cc0884027167c21bb143a40197" },
  { name := "get-vanilla-utf8-query", query := [("ሴ", "bar")], headers := suiteHeaders,
    canonical := plainCanonical "GET" "%E1%88%B4=bar",
    signature := "2cdec8eed098649ff3a119c94853b13c643bcf08f8b0a1d91e12c9027818dd04" },
  { name := "get-header-key-duplicate",
    headers := suiteHeaders [("My-Header1", "value2"), ("My-Header1", "value2"),
      ("My-Header1", "value1")],
    canonical := oneHeaderCanonical "GET" "my-header1:value2,value2,value1",
    signature := "c9d5ea9f3f72853aea855b47ea873832890dbdd183b4468f858259531a5138ea" },
  { name := "get-header-value-order",
    headers := suiteHeaders [("My-Header1", "value4"), ("My-Header1", "value1"),
      ("My-Header1", "value3"), ("My-Header1", "value2")],
    canonical := oneHeaderCanonical "GET" "my-header1:value4,value1,value3,value2",
    signature := "08c7e5a9acfcfeb3ab6b2185e75ce8b1deb5e634ec47601a50643f830c755c01" },
  { name := "get-header-value-trim",
    headers := suiteHeaders [("My-Header1", " value1"), ("My-Header2", " \"a   b   c\"")],
    canonical := "GET\n/\n\nhost:example.amazonaws.com\nmy-header1:value1\nmy-header2:\"a b c\"\n"
      ++ "x-amz-date:20150830T123600Z\n\nhost;my-header1;my-header2;x-amz-date\n" ++ emptyHash,
    signature := "acc3ed3afb60bb290fc8d2dd0098b9911fcaa05412b367055dee359757a9c736" },
  { name := "get-unreserved", path := [unreserved], headers := suiteHeaders,
    canonical := "GET\n/" ++ unreserved ++ "\n\nhost:example.amazonaws.com\n"
      ++ "x-amz-date:20150830T123600Z\n\nhost;x-amz-date\n" ++ emptyHash,
    signature := "07ef7494c76fa4850883e2b006601f940f8a34d404d0cfa977f52a65bbf5f24f" },
  { name := "get-utf8", path := ["ሴ"], headers := suiteHeaders,
    canonical := "GET\n/%E1%88%B4\n\nhost:example.amazonaws.com\n"
      ++ "x-amz-date:20150830T123600Z\n\nhost;x-amz-date\n" ++ emptyHash,
    signature := "8318018e0b0f223aa2bbf98705b62bb787dc9c0e678f255a891fd03141be5d85" },
  { name := "post-vanilla", verb := "POST", headers := suiteHeaders,
    canonical := plainCanonical "POST",
    signature := "5da7c1a2acd57cee7505fc6676e4e544621c30862966e37dddb68e92efbe5d6b" },
  { name := "post-vanilla-query", verb := "POST", query := [("Param1", "value1")],
    headers := suiteHeaders, canonical := plainCanonical "POST" "Param1=value1",
    signature := "28038455d6de14eafc1f9222cf5aa6f1a96197d7deb8263271d420d138af7f11" },
  { name := "post-header-key-sort", verb := "POST", headers := suiteHeaders [("My-Header1", "value1")],
    canonical := oneHeaderCanonical "POST" "my-header1:value1",
    signature := "c5410059b04c1ee005303aed430f6e6645f61f4dc9e1461ec8f8916fdf18852c" },
  { name := "post-header-value-case", verb := "POST",
    headers := suiteHeaders [("My-Header1", "VALUE1")],
    canonical := oneHeaderCanonical "POST" "my-header1:VALUE1",
    signature := "cdbc9802e29d2942e5e10b5bccfdd67c5f22c7c4e8ae67b53629efa58b974b7d" },
  { name := "post-x-www-form-urlencoded", verb := "POST", body := "Param1=value1",
    headers := [("Content-Type", "application/x-www-form-urlencoded")] ++ suiteHeaders,
    canonical := "POST\n/\n\ncontent-type:application/x-www-form-urlencoded\n"
      ++ "host:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\n"
      ++ "content-type;host;x-amz-date\n"
      ++ "9095672bbd1f56dfc5b65f3e153adc8731a4a654192329106275f4c7b24d0b6e",
    signature := "ff11897932ad3f4e8b18135d722051e5ac45fc38421b1da7b9d196a0fe09473a" },
  { name := "post-x-www-form-urlencoded-parameters", verb := "POST", body := "Param1=value1",
    headers := [("Content-Type", "application/x-www-form-urlencoded; charset=utf8")]
      ++ suiteHeaders,
    canonical := "POST\n/\n\ncontent-type:application/x-www-form-urlencoded; charset=utf8\n"
      ++ "host:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\n"
      ++ "content-type;host;x-amz-date\n"
      ++ "9095672bbd1f56dfc5b65f3e153adc8731a4a654192329106275f4c7b24d0b6e",
    signature := "1a72ec8f64bd914b0e42e42607c7fbce7fb2c7465f63e3092b3b0d39fa77a6fe" },
  { name := "post-sts-header-before", verb := "POST",
    headers := suiteHeaders [] ++ [("X-Amz-Security-Token", token)],
    canonical := "POST\n/\n\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n"
      ++ "x-amz-security-token:" ++ token ++ "\n\nhost;x-amz-date;x-amz-security-token\n"
      ++ emptyHash,
    signature := "85d96828115b5dc0cfc3bd16ad9e210dd772bbebba041836c64533a82be05ead" } ]

def Case.authorization (c : Case) (creds : Credentials) (t : Civil.DateTime) (scope : Scope) :
    String :=
  SigV4.authorization creds t scope c.verb c.path c.query c.headers (payloadHash c.body.toUTF8)

def suiteTests : List (String × Bool) :=
  suite.flatMap fun c =>
    let hash := payloadHash c.body.toUTF8
    let signedNames := ";".intercalate ((canonicalHeaders c.headers).map (·.1))
    [ (s!"sigv4 suite {c.name}: the canonical request",
        canonicalRequest c.verb c.path c.query c.headers hash == c.canonical),
      (s!"sigv4 suite {c.name}: the Authorization header",
        c.authorization suiteKey suiteTime suiteScope
          == "AWS4-HMAC-SHA256 Credential=AKIDEXAMPLE/20150830/us-east-1/service/aws4_request, "
            ++ "SignedHeaders=" ++ signedNames ++ ", Signature=" ++ c.signature) ]

def suiteStringToSign : List (String × Bool) :=
  [ ("sigv4 suite get-vanilla: the string to sign",
      stringToSign suiteTime suiteScope (plainCanonical "GET")
        == "AWS4-HMAC-SHA256\n20150830T123600Z\n20150830/us-east-1/service/aws4_request\n"
          ++ "bb579772317eb040ac9ed261061d46c1f17a8133879d6129b6e1c25292927e63") ]

/-- `sign` on a request as the client holds it: the query out of order, the session token given
as a credential. -/
def signTests : List (String × Bool) :=
  let r : Request := { method := .get, path := [], query := [("Param1", "value2"), ("Param1", "Value1")] }
  let signed := sign suiteKey suiteTime suiteScope "example.amazonaws.com" "GET" emptyHash r
  let withToken := { suiteKey with sessionToken := some ⟨token⟩ }
  let post := sign withToken suiteTime suiteScope "example.amazonaws.com" "POST" emptyHash
    { method := .post, path := [] }
  [ ("sigv4 sign: a request's query is put in canonical order and signed as the suite's",
      signed.query == [("Param1", "Value1"), ("Param1", "value2")]
        && signed.headers.lookup "authorization" == some ("AWS4-HMAC-SHA256 Credential="
          ++ "AKIDEXAMPLE/20150830/us-east-1/service/aws4_request, SignedHeaders=host;x-amz-date, "
          ++ "Signature=eedbc4e291e521cf13422ffca22be7d2eb8146eecf653089df300a15b2382bd1")
        && signed.target == "/?Param1=Value1&Param1=value2"),
    ("sigv4 sign: a session token is sent and signed (suite post-sts-header-before)",
      post.headers.lookup "x-amz-security-token" == some token
        && post.headers.lookup "authorization" == some ("AWS4-HMAC-SHA256 Credential="
          ++ "AKIDEXAMPLE/20150830/us-east-1/service/aws4_request, "
          ++ "SignedHeaders=host;x-amz-date;x-amz-security-token, "
          ++ "Signature=85d96828115b5dc0cfc3bd16ad9e210dd772bbebba041836c64533a82be05ead")) ]

/-! ## S3's examples -/

def docTime : Civil.DateTime := Civil.DateTime.ofUnix 1369353600

def docKey : Credentials :=
  { accessKeyId := "AKIAIOSFODNN7EXAMPLE",
    secretAccessKey := ⟨"wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"⟩ }

def s3 : Scope := ⟨"us-east-1", "s3"⟩

def docHost : String := "examplebucket.s3.amazonaws.com"

def docAuthorization (signed signature : String) : String :=
  "AWS4-HMAC-SHA256 Credential=AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/aws4_request, "
    ++ "SignedHeaders=" ++ signed ++ ", Signature=" ++ signature

def getObjectHeaders : List (String × String) :=
  [("Host", docHost), ("Range", "bytes=0-9"), ("x-amz-content-sha256", emptyHash),
    ("x-amz-date", "20130524T000000Z")]

def getObjectCanonical : String :=
  "GET\n/test.txt\n\nhost:examplebucket.s3.amazonaws.com\nrange:bytes=0-9\n"
    ++ "x-amz-content-sha256:" ++ emptyHash ++ "\nx-amz-date:20130524T000000Z\n\n"
    ++ "host;range;x-amz-content-sha256;x-amz-date\n" ++ emptyHash

def putBody : String := "Welcome to Amazon S3."

def putHash : String := "44ce7dd67c959e0d3524ffac1771dfbba87d2b6b4b4e99e42034a8b803f8b072"

def s3Tests : List (String × Bool) :=
  let hex (b : ByteArray) := Bytes.hex b
  [ ("sigv4 s3 GET object: the canonical request", canonicalRequest "GET" ["test.txt"] []
      getObjectHeaders emptyHash == getObjectCanonical),
    ("sigv4 s3 GET object: the string to sign",
      stringToSign docTime s3 getObjectCanonical
        == "AWS4-HMAC-SHA256\n20130524T000000Z\n20130524/us-east-1/s3/aws4_request\n"
          ++ "7344ae5b7ee6c3e7e6b0fe0640412a37625d1fbfff95c48bbb2dc43964946972"),
    ("sigv4 s3 GET object: the Authorization header",
      authorization docKey docTime s3 "GET" ["test.txt"] [] getObjectHeaders emptyHash
        == docAuthorization "host;range;x-amz-content-sha256;x-amz-date"
          "f0e8bdb87c964420e857bd35b5d6ed310bd44f0170aba48dd91039c6036bdb41"),
    ("sigv4 s3 PUT object: the body's hash", payloadHash putBody.toUTF8 == putHash),
    ("sigv4 s3 PUT object: a key with $, and a Date header beside x-amz-date",
      authorization docKey docTime s3 "PUT" ["test$file.text"] []
        [("Date", "Fri, 24 May 2013 00:00:00 GMT"), ("Host", docHost),
          ("x-amz-date", "20130524T000000Z"), ("x-amz-storage-class", "REDUCED_REDUNDANCY"),
          ("x-amz-content-sha256", putHash)] putHash
        == docAuthorization "date;host;x-amz-content-sha256;x-amz-date;x-amz-storage-class"
          "98ad721746da40c64f1a55b78f14c238d841ea1380cd77a1b5971af0ece108bd"),
    ("sigv4 s3 GET bucket lifecycle: a parameter without a value",
      authorization docKey docTime s3 "GET" [] [("lifecycle", "")]
        [("Host", docHost), ("x-amz-content-sha256", emptyHash), ("x-amz-date", "20130524T000000Z")]
        emptyHash
        == docAuthorization "host;x-amz-content-sha256;x-amz-date"
          "fea454ca298b7da1c68078a5d1bdbfbbe0d65c699e0f91ac7a200a0136783543"),
    ("sigv4 s3 GET bucket (list objects): two parameters",
      authorization docKey docTime s3 "GET" [] [("prefix", "J"), ("max-keys", "2")]
        [("Host", docHost), ("x-amz-content-sha256", emptyHash), ("x-amz-date", "20130524T000000Z")]
        emptyHash
        == docAuthorization "host;x-amz-content-sha256;x-amz-date"
          "34b48302e7b5fa45bde8084f4b7868a86f0a534bc59db6670ed5711ef69dc6f7"),
    ("sigv4 s3 the signing key of the examples' day",
      hex (signingKey docKey.secretAccessKey docTime s3)
        == hex (Hmac.reference (Hmac.reference (Hmac.reference (Hmac.reference
          ("AWS4" ++ docKey.secretAccessKey.reveal).toUTF8 "20130524".toUTF8) "us-east-1".toUTF8)
          "s3".toUTF8) "aws4_request".toUTF8)),
    ("sigv4 s3 presigned GET object, for a day",
      presign docKey docTime s3 docHost "GET" ["test.txt"] [] ⟨86400, by decide⟩
        == [("X-Amz-Algorithm", "AWS4-HMAC-SHA256"),
          ("X-Amz-Credential", "AKIAIOSFODNN7EXAMPLE/20130524/us-east-1/s3/aws4_request"),
          ("X-Amz-Date", "20130524T000000Z"), ("X-Amz-Expires", "86400"),
          ("X-Amz-SignedHeaders", "host"),
          ("X-Amz-Signature", "aeeed9bbccd4d02ee5c0109b86d86835f995330da4c265957d157751f604d404")]) ]

/-! ## The parts -/

def partTests : List (String × Bool) :=
  [ ("sigv4 stamp and day", stamp docTime == "20130524T000000Z" && day docTime == "20130524"),
    ("sigv4 encode: unreserved bytes kept, the rest as %XX in capitals, a slash included",
      encode unreserved == unreserved && encode "a b/c+d=é*" == "a%20b%2Fc%2Bd%3D%C3%A9%2A"),
    ("sigv4 canonical path: segments escaped, empty ones kept",
      canonicalPath ["photos", "a b", "", "x.jpg"] == "/photos/a%20b//x.jpg"
        && canonicalPath [] == "/"),
    ("sigv4 canonical query: by escaped name, then value; empty values kept",
      canonicalQuery [("b", "2"), ("a", ""), ("A", "x y"), ("a", "1")] == "A=x%20y&a=&a=1&b=2"),
    ("sigv4 trim: blanks at the ends dropped, runs inside as one space",
      trimValue "  a \t b   c  " == "a b c" && trimValue "" == "" && trimValue "   " == ""),
    ("sigv4 headers: names lowercased, sorted, repeated names joined in order",
      canonicalHeaders [("B", "1"), ("a", "2"), ("b", " 3 ")]
        == [("a", "2"), ("b", "1,3")]),
    ("sigv4 secrets print as nothing",
      let shown := toString (repr { docKey with sessionToken := some ⟨"session"⟩ })
      (shown.splitOn "wJalrXUtnFEMI").length == 1 && (shown.splitOn "session\"").length == 1 && toString docKey.secretAccessKey == "<secret>") ]

def tests : List (String × Bool) :=
  suiteTests ++ suiteStringToSign ++ signTests ++ s3Tests ++ partTests

end Tests.SigV4
