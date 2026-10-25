# Pairs on Cairn. Everything goes through Cairn's `cairn` CLI (cairn's docs/cli.md), built from
# the Cairn checkout Lake fetched from the registry (lean/.lake/packages/cairn).

export PATH := $(HOME)/.elan/bin:$(PATH)
export RESERVOIR_API_URL := https://cairn.registry.nexthub.sh/api/v1
CAIRN_PKG = lean/.lake/packages/cairn
CAIRN = $(CAIRN_PKG)/tools/cairn/.build/release/cairn

.PHONY: deps cairn-tool build selftest clean

# Fetch Cairn and cairn_json as lean/lake-manifest.json pins them.
deps:
	cd lean && lake env true

# The `cairn` CLI from the fetched Cairn.
cairn-tool: deps
	swift build -c release --package-path $(CAIRN_PKG)/tools/cairn

# lake build, cairn-link into .cairn/lib/libpairs.a, swift build.
build: cairn-tool
	$(CAIRN) build

selftest: build
	swift run Pairs --selftest

clean:
	rm -rf build .cairn .build lean/.lake
