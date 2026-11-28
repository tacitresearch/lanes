/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Compress.Gzip
public import Lanes.Web.Http.Basic

/-!
# Content codings

What the server and the client decide about `Content-Encoding` (RFC 9110 §8.4, §12.5.3), as pure
functions. The server compresses a response with gzip when the client's `Accept-Encoding` takes
it (`accepts`), the response is of a type that compresses, large enough, not already encoded and
not marked `no-transform`, and gzip makes it smaller (`Compression.respond`); a response of such
a type says `Vary: Accept-Encoding` either way, so that a cache keeps the two apart. A strong
`ETag` is made weak, since the bytes differ. The client decodes a response in gzip or `deflate`
(zlib's format, or raw DEFLATE, as browsers read it), at most `max` bytes (`decode`).

Compression is off by default (`ServerConfig.compression`): a page that holds a secret and text
an attacker chose can leak the secret through its compressed size (BREACH), so it is turned on
knowingly.
-/

@[expose] public section

namespace Lanes.Http

/-- The value of the first header named `name`, in any case. -/
def headerValue? (headers : List (String × String)) (name : String) : Option String :=
  (headers.find? (·.1.toLower == name)).map (·.2)

/-- Whether an `Accept-Encoding` value takes gzip: named, as `gzip` or `x-gzip`, or matched by
`*`, with a weight above zero. -/
def accepts (acceptEncoding : String) : Bool :=
  let items := (acceptEncoding.splitOn ",").map fun item =>
    match (item.splitOn ";").map (·.trimAscii.toString) with
    | coding :: params =>
      let q := params.findSome? fun p =>
        match p.splitOn "=" with
        | [k, v] => if k.trimAscii.toString.toLower == "q" then some v.trimAscii.toString else none
        | _ => none
      (coding.toLower, q.all fun v => v.any (fun c => c.isDigit && c != '0'))
    | [] => ("", false)
  match items.find? fun (c, _) => c == "gzip" || c == "x-gzip" with
  | some (_, ok) => ok
  | none => (items.find? (·.1 == "*")).any (·.2)

/-- What the server compresses. -/
structure Compression where
  /-- A smaller body is sent as it is. -/
  bytes_min : Nat := 1024
  /-- A larger body is sent as it is: compressing it would hold the connection's thread. -/
  bytes_max : Nat := 8388608
  /-- The media types that compress, or their prefixes when they end in `/`. -/
  types : List String :=
    ["text/", "application/json", "application/javascript", "application/xml",
      "application/xhtml+xml", "application/rss+xml", "application/atom+xml",
      "application/manifest+json", "image/svg+xml"]

namespace Compression

def compressible (c : Compression) (contentType : String) : Bool :=
  let type := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  c.types.any fun t => if t.endsWith "/" then type.startsWith t else type == t

/-- Whether the response is one that compression would change: a type that compresses, of a
size within the bounds, with a status that has a body, not encoded and not `no-transform`. -/
def eligible (c : Compression) (r : Response) : Bool :=
  200 ≤ r.status && r.status != 204 && r.status != 206 && r.status != 304
    && (headerValue? r.headers "content-type").any c.compressible
    && (headerValue? r.headers "content-encoding").isNone
    && !((headerValue? r.headers "cache-control").any fun v => (v.toLower.splitOn "no-transform").length > 1)
    && c.bytes_min ≤ r.body.size && r.body.size ≤ c.bytes_max

/-- A strong entity tag made weak; a weak one as it is. -/
def weaken (etag : String) : String :=
  if etag.startsWith "W/" then etag else "W/" ++ etag

/-- The response to a request whose `Accept-Encoding` was `acceptEncoding`. -/
def respond (c : Compression) (acceptEncoding : Option String) (r : Response) : Response :=
  if !c.eligible r then r
  else
    let varied := r.withHeader "vary" "Accept-Encoding"
    if !acceptEncoding.any accepts then varied
    else
      let body := Gzip.compress r.body
      if body.size ≥ r.body.size then varied
      else
        { varied with
          body
          headers := (varied.headers.map fun (n, v) =>
            if n.toLower == "etag" then (n, weaken v) else (n, v)) ++ [("content-encoding", "gzip")] }

end Compression

/-- A response with its content coding undone: gzip, or `deflate` as zlib's format or raw, at
most `max` bytes; any other coding is left as it is. `Content-Encoding` and `Content-Length` are
dropped from a response decoded. -/
def decode (max : Nat) (r : Response) : Except String Response :=
  match (headerValue? r.headers "content-encoding").map (·.trimAscii.toString.toLower) with
  | some "gzip" | some "x-gzip" => done (Gzip.decompress max r.body)
  | some "deflate" =>
    match Zlib.decompress max r.body with
    | .ok body => done (.ok body)
    | .error _ => done (Inflate.inflate max r.body)
  | _ => .ok r
where
  done (body : Except Inflate.Error ByteArray) : Except String Response :=
    match body with
    | .ok body => .ok { r with body, headers := r.headers.filter fun (n, _) =>
        n.toLower != "content-encoding" && n.toLower != "content-length" }
    | .error .tooLarge => .error s!"the response's body is larger than {max} bytes once decoded"
    | .error e => .error s!"the response's body does not decode: {repr e}"

end Lanes.Http
