// The Node side of oracles/go/requests/requests.py: node's http server (llhttp, not lenient) with the limits
// of Request.Limits, answering each request it reads with its method and the length of its body.
const http = require("http");

const server = http.createServer({ maxHeaderSize: 16384 }, (req, res) => {
  let size = 0;
  let tooLarge = false;
  req.on("data", (chunk) => {
    size += chunk.length;
    if (size > 1048576) tooLarge = true;
  });
  req.on("end", () => {
    req.socket.lanesRead = (req.socket.lanesRead || []).concat(
      tooLarge ? ["413"] : [`ok:${req.method}:${size}`]);
    if (tooLarge) {
      res.writeHead(413, { "Content-Length": "0" }).end();
    } else {
      res.writeHead(200, { "X-Verdict": `ok:${req.method}:${size}`, "Content-Length": "0" }).end();
    }
  });
  req.on("aborted", () => res.destroy());
});
server.on("clientError", (err, socket) => {
  if (socket.writable) {
    const code = err.code === "HPE_HEADER_OVERFLOW" ? 431 : 400;
    const read = (socket.lanesRead || []).join(" ");
    socket.end(`HTTP/1.1 ${code} Bad Request\r\nX-Error: ${err.code}\r\nX-Read: ${read}\r\n`
      + "Content-Length: 0\r\n\r\n");
  } else {
    socket.destroy();
  }
});
server.listen(0, "127.0.0.1", () => {
  console.log(server.address().port);
});
