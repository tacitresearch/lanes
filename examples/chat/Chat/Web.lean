import Chat.Chat
import Lanes.Web.Http.WebSocket
import Lanes.Web.Http.WebSocketSession

/-!
# The front

`GET /` is a page that opens a WebSocket to `/chat` and shows what comes. The server checks the
handshake (`WebSocket.Server.bridge`) and hands the system the opening request, which it answers
`WebSocket.accept`; each line a browser sends is then a request through the gate, answered
`Response.taken`, and each line for a member is an output that answers the member's socket.
When a socket ends the server tells the system once, as `leave`.
-/

namespace Chat.Web

open Lanes Lanes.Http

def ws : WebSocket.Server := { wants := (·.path == ["chat"]) }

def page : String := "<!doctype html>
<meta charset=\"utf-8\"><title>Chat</title>
<ul id=\"lines\"></ul>
<form id=\"say\"><input id=\"line\" autocomplete=\"off\" autofocus> <button>Say</button></form>
<script>
const socket = new WebSocket(`ws://${location.host}/chat`);
const lines = document.getElementById('lines');
socket.onmessage = e => { const li = document.createElement('li'); li.textContent = e.data; lines.append(li); };
socket.onclose = e => { lines.append(Object.assign(document.createElement('li'), { textContent: `closed ${e.code}` })); };
document.getElementById('say').onsubmit = e => {
  e.preventDefault();
  const input = document.getElementById('line');
  if (input.value) socket.send(input.value);
  input.value = '';
};
</script>
"

def decode (id : ReqId) (r : Http.Request) : Except Http.Response Request :=
  match WebSocket.msg? r with
  | some (.message socket _ (.text line)) => .ok (.say id socket line)
  | some (.message _ _ (.binary _)) => .error (.text "lines are text\n" 400)
  | some (.closed socket _) => .ok (.leave id socket)
  | none =>
    if r.path == ["chat"] then .ok (.join id)
    else if r.path.isEmpty then .error (.html page)
    else .error (.text "not found\n" 404)

def encode (out : Out) : Http.Response :=
  match out.reply with
  | .accepted => WebSocket.accept
  | .full => .text "the room is full\n" 503
  | .taken => .taken
  | .line text => WebSocket.text text

def bridge : Bridge sig := ws.bridge { decode, encode := fun out => some (out.req, encode out) }

def serverConfig (port : UInt16) : ServerConfig := { port }

end Chat.Web
