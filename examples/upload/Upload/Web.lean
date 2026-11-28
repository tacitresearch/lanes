import Upload.Upload

/-!
# The front

`PUT` or `POST` a body to `/upload`, as large as it likes: the request streams
(`Http.ServerConfig.streams`), so the server hands its head to the system, then its body in
pieces of at most `piece_max` bytes, one at a time, each answered `204` once the system has
taken it. Neither the server nor the system ever holds the whole body.
-/

namespace Upload.Web

open Lanes Lanes.Http

def uploading (r : Http.Request) : Bool :=
  r.path == ["upload"] && (r.method == .put || r.method == .post)

/-- Whether a request has a body to follow; one that has none is an empty upload. -/
def hasBody (r : Http.Request) : Bool :=
  (r.header? "transfer-encoding").isSome || (r.header? "content-length").any (· != "0")

def home : Http.Response :=
  .text "PUT a file to /upload, as with: curl -T file http://127.0.0.1:8080/upload\n"

def done (size sum : Nat) : Http.Response :=
  .text s!"{size} bytes, Adler-32 {sum}\n"

def decode (id : ReqId) (r : Http.Request) : Except Http.Response Request :=
  match Stream.msg? r with
  | some (.piece head index data last) => .ok (.piece id head index data last)
  | some (.pull ..) => .error (.text "nothing to pull\n" 400)
  | none =>
    if uploading r then
      if hasBody r then .ok (.start id) else .error (done 0 (checksum .empty))
    else if r.path.isEmpty then .error home
    else .error (.text "not found\n" 404)

def encode (out : Response) : Http.Response :=
  match out.answer with
  | .taken => Http.Response.taken
  | .busy => .text "too many uploads at once\n" 503
  | .unknown => .text "no such upload\n" 400
  | .outOfOrder => .text "a piece out of order\n" 400
  | .done size sum => done size sum

def bridge : Bridge sig where
  decode := decode
  encode out := some (out.req, encode out)

/-- The server's configuration: uploads stream, in pieces of 64 KiB, up to 1 TiB. -/
def serverConfig (port : UInt16) (journal : Option System.FilePath) : ServerConfig :=
  { port, journal, system := "upload 1", streams := some uploading, piece_max := 65536 }

def saving : Saving (system {}) where
  actors := { id := Codec.unit, state := fun _ => Codec.of State, msg := fun _ => Request.codec }

end Upload.Web
