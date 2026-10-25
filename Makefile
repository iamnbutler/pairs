# Pairs on Cairn. Everything goes through Cairn's `cairn` CLI (cairn's docs/cli.md), built from
# the Cairn checkout Lake fetched from the registry (lean/.lake/packages/cairn).

export PATH := $(HOME)/.elan/bin:$(PATH)
export RESERVOIR_API_URL := https://cairn.registry.nexthub.sh/api/v1
CAIRN_PKG = lean/.lake/packages/cairn
CAIRN = $(CAIRN_PKG)/tools/cairn/.build/release/cairn

.PHONY: deps cairn-tool build selftest urltest shots pairs bench lean lint audit ledger ledger-update kernel fuzz pairsfuzz size claims packs check clean

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

# A 100-face pack's load time and memory, from a folder and over http (bench/README.md), with
# `cairn bench` (a release build, then `Pairs --bench`), into build/bench/pairs.json.
bench: cairn-tool
	tools/stub/packs.sh build/stub
	mkdir -p build/bench
	@set -e; python3 -I tools/stub/serve.py build/stub > build/stub.port 2> build/stub.log & pid=$$!; \
	  trap "kill $$pid" EXIT; \
	  for i in $$(seq 50); do [ -s build/stub.port ] && break; sleep 0.2; done; \
	  port=$$(head -1 build/stub.port); [ -n "$$port" ] || { echo "bench: the stub server didn't start"; exit 1; }; \
	  rm -rf $(HOME_TEST) && mkdir -p $(HOME_TEST) && \
	  CFFIXED_USER_HOME=$(HOME_TEST) PAIRS_BENCH_PACKS=$(CURDIR)/build/stub PAIRS_BENCH_URL=http://127.0.0.1:$$port \
	  PAIRS_BENCH_OUT=$(CURDIR)/build/bench/pairs.json $(CAIRN) bench

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

# Pairs.app, built for release, signed and installed in ~/Applications. SIGN is a codesign
# identity: the first "Developer ID Application" one in the keychain, else `-` (ad hoc).
#
# The bundling below is cairn's tools/bundle/bundle.sh as fixed in cairn#183 (the released
# script only wraps Cairn's own examples and drops SwiftPM resources); once a Cairn release has
# `cairn bundle`, this becomes `$(CAIRN) bundle --sign "$(SIGN)"`.
SIGN ?= $(or $(shell security find-identity -v -p codesigning 2>/dev/null | grep -m1 '"Developer ID Application' | sed -E 's/.*"(.*)"/\1/'),-)
APP_OUT = build/apps/Pairs.app
pairs: build
	swift build -c release --product Pairs
	@set -e; bin=$$(swift build -c release --show-bin-path); \
	  rm -rf $(APP_OUT); mkdir -p $(APP_OUT)/Contents/MacOS $(APP_OUT)/Contents/Resources; \
	  cp $$bin/Pairs $(APP_OUT)/Contents/MacOS/Pairs; \
	  cp -R $$bin/pairs_Pairs.bundle $(APP_OUT)/Contents/Resources/; \
	  cp bundle/Info.plist $(APP_OUT)/Contents/Info.plist; plutil -lint -s $(APP_OUT)/Contents/Info.plist; \
	  if [ "$(SIGN)" = "-" ]; then codesign --force -s - $(APP_OUT); \
	  else codesign --force --options runtime -s "$(SIGN)" $(APP_OUT); fi; \
	  codesign --verify --strict $(APP_OUT)
	rm -rf $(HOME)/Applications/Pairs.app
	mkdir -p $(HOME)/Applications
	ditto $(APP_OUT) $(HOME)/Applications/Pairs.app
	@echo "pairs: installed ~/Applications/Pairs.app, signed $(if $(filter -,$(SIGN)),ad hoc (no Developer ID identity),by $(SIGN))"
	@CFFIXED_USER_HOME=$(CURDIR)/build/home $(HOME)/Applications/Pairs.app/Contents/MacOS/Pairs --selftest

check: build lint audit ledger kernel selftest urltest fuzz size claims

clean:
	rm -rf build .cairn .build lean/.lake
