"""A stub pack server for Pairs's URL tests (make urltest) and bench (make bench).

    python3 -I tools/stub/serve.py <root> [--port N]

Serves <root> over plain http on 127.0.0.1 (Pairs allows http only on this machine) and prints
the port on its first line. Paths under /slow/ answer images after SLOW_S seconds, so a test can
switch packs while one is still loading. Anything missing is a 404.
"""

import http.server
import os
import sys
import time

SLOW_S = 3.0


class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        if self.path.startswith("/slow/") and self.path.endswith(".png"):
            time.sleep(SLOW_S)
        super().do_GET()

    def log_message(self, fmt, *args):
        sys.stderr.write("stub: " + (fmt % args) + "\n")


def main():
    args = sys.argv[1:]
    if not args:
        sys.stderr.write("usage: serve.py <root> [--port N]\n")
        sys.exit(2)
    root = os.path.abspath(args[0])
    port = int(args[args.index("--port") + 1]) if "--port" in args else 0
    handler = lambda *a, **k: Handler(*a, directory=root, **k)
    server = http.server.ThreadingHTTPServer(("127.0.0.1", port), handler)
    print(server.server_address[1], flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
