#!/usr/bin/env python3
"""A relay in the middle of a PostgreSQL connection over TLS, for `Tests/PostgresTls.lean`.

    relay.py UPSTREAM_PORT CERT KEY

It prints the port it listens on, then for each client: answers its SSLRequest with S, runs TLS
with it under CERT, opens its own TLS connection to the server on 127.0.0.1:UPSTREAM_PORT, and
passes the bytes both ways. A client that checks only the certificate cannot tell it from the
server; one that binds SCRAM to the certificate's hash (`tls-server-end-point`) binds the relay's
certificate, and the server refuses it.
"""
import socket
import ssl
import sys
import threading

upstream, cert, key = int(sys.argv[1]), sys.argv[2], sys.argv[3]


def exactly(sock, n):
    data = b""
    while len(data) < n:
        more = sock.recv(n - len(data))
        if not more:
            raise OSError("closed")
        data += more
    return data


def pump(a, b):
    try:
        while True:
            data = a.recv(65536)
            if not data:
                break
            b.sendall(data)
    except OSError:
        pass
    for s in (a, b):
        try:
            s.close()
        except OSError:
            pass


def handle(client):
    try:
        request = exactly(client, 8)
        client.sendall(b"S")
        server_side = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        server_side.minimum_version = ssl.TLSVersion.TLSv1_2
        server_side.load_cert_chain(cert, key)
        near = server_side.wrap_socket(client, server_side=True)
        up = socket.create_connection(("127.0.0.1", upstream))
        up.sendall(request)
        if exactly(up, 1) != b"S":
            raise OSError("the server refused TLS")
        client_side = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        client_side.minimum_version = ssl.TLSVersion.TLSv1_2
        # The relay stands for an attacker between the client and the server: it does not check
        # the server, and the client's channel binding is what must catch it.
        client_side.check_hostname = False
        client_side.verify_mode = ssl.CERT_NONE
        far = client_side.wrap_socket(up)
        threading.Thread(target=pump, args=(near, far), daemon=True).start()
        pump(far, near)
    except (OSError, ssl.SSLError):
        client.close()


listener = socket.socket()
listener.bind(("127.0.0.1", 0))
listener.listen(8)
print(listener.getsockname()[1], flush=True)
while True:
    conn, _ = listener.accept()
    threading.Thread(target=handle, args=(conn,), daemon=True).start()
