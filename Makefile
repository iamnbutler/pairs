# Pairs on Cairn. Everything goes through Cairn's `cairn` CLI (cairn's docs/cli.md), built from
# the Cairn checkout Lake fetched from the registry (lean/.lake/packages/cairn).

export PATH := $(HOME)/.elan/bin:$(PATH)
export RESERVOIR_API_URL := https://cairn.registry.nexthub.sh/api/v1
CAIRN_PKG = lean/.lake/packages/cairn
CAIRN = $(CAIRN_PKG)/tools/cairn/.build/release/cairn

.PHONY: deps cairn-tool build selftest urltest shots lean lint audit ledger ledger-update kernel fuzz pairsfuzz size claims packs check clean

# Fetch Cairn and cairn_json as lean/lake-manifest.json pins them.
deps:
	cd lean && lake env true

# The `cairn` CLI from the fetched Cairn.
cairn-tool: deps
	swift build -c release --package-path $(CAIRN_PKG)/tools/cairn

# lake build, cairn-link into .cairn/lib/libpairs.a, swift build.
build: cairn-tool
	$(CAIRN) build

# The headless modes run with a home of their own (build/home), so they never touch the real
# scores or packs folder.
HOME_TEST = $(CURDIR)/build/home
RUN_HEADLESS = rm -rf $(HOME_TEST) && mkdir -p $(HOME_TEST) && CFFIXED_USER_HOME=$(HOME_TEST) swift run Pairs

selftest: build
	$(RUN_HEADLESS) --selftest

# Packs over http from a local stub server (tools/stub): a good pack, failures, switching packs
# and cancelling while one loads.
urltest: build
	tools/stub/packs.sh build/stub
	@set -e; python3 -I tools/stub/serve.py build/stub > build/stub.port 2> build/stub.log & pid=$$!; \
	  trap "kill $$pid" EXIT; \
	  for i in $$(seq 50); do [ -s build/stub.port ] && break; sleep 0.2; done; \
	  port=$$(head -1 build/stub.port); [ -n "$$port" ] || { echo "urltest: the stub server didn't start"; cat build/stub.log; exit 1; }; \
	  $(RUN_HEADLESS) --urltest http://127.0.0.1:$$port

# Offscreen renders of a few states into build/shots.
shots: build
	$(RUN_HEADLESS) --shots $(CURDIR)/build/shots

# The Lean side alone. `cairn build` turns Lake's artifact cache on, which keeps .olean files out
# of the build directory, and the ledger and audit import from there: turn it off.
lean:
	cd lean && LAKE_ARTIFACT_CACHE=false lake build -q

# Constructs that bypass the kernel or swap in unchecked code (AGENTS.md, Rules).
lint:
	@! grep -rnE 'implemented_by|skipKernelTC|native_decide|bv_decide|^\s*axiom |\bsorry\b' lean/Pairs lean/*.lean \
	  || (echo "lint: forbidden construct (see AGENTS.md, Rules)"; exit 1)

# Every theorem depends only on propext, Classical.choice and Quot.sound.
audit: lean
	cd lean && lake exe audit Checks Pairs

# Every pairs^N claim is in claims.lock with its statement hash; `ledger-update` writes new ones.
ledger: lean
	cd lean && lake exe ledger check --scope pairs --root Checks --lock ../claims.lock

ledger-update: lean
	cd lean && lake exe ledger update --scope pairs --root Checks --lock ../claims.lock

# Replay every declaration through the kernel (unsandboxed: macOS has no bubblewrap).
kernel: lean
	cd lean && lake check --inadvisably-no-sandbox

# Cairn's fuzzer on the app through the runtime (build/fuzz/Claims.json), then Pairs's own
# fuzzer with a random host: replies in any order, late, stale or failing (build/fuzz/pairs.json).
FUZZ_ITERATIONS ?= 200
fuzz: cairn-tool pairsfuzz
	$(CAIRN) fuzz --iterations $(FUZZ_ITERATIONS)

pairsfuzz: lean
	mkdir -p build/fuzz
	cd lean && lake build -q pairsfuzz && .lake/build/bin/pairsfuzz --iterations $(FUZZ_ITERATIONS) --steps 300 --out ../build/fuzz

# The release binary's size, attributed (build/size/), under Cairn's 5 MB limit.
size: cairn-tool
	$(CAIRN) size

# Every claim as the registry will show it (build/claims.json).
claims: cairn-tool
	mkdir -p build
	$(CAIRN) claims --ledger --out build/claims.json

# Redraw the bundled packs' images.
packs:
	rm -rf Sources/Pairs/packs
	swift tools/packs/draw.swift bundled Sources/Pairs/packs

check: build lint audit ledger kernel selftest urltest fuzz size claims

clean:
	rm -rf build .cairn .build lean/.lake
