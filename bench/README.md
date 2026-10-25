# Pack load bench

`make bench` measures how long a 100-face pack takes to load and how much memory Pairs holds.
It draws the stub packs (`tools/stub/packs.sh`: `big` is 100 PNGs of 256 × 256 pixels), serves
them from `tools/stub/serve.py`, and runs `cairn bench`: a release build, then `Pairs --bench`
(`Sources/Pairs/Bench.swift`) through the real host world, headless. Results go to
`build/bench/pairs.json`.

- **Load time** is from Enter in the pack field to the new game dealt: the manifest read and
  parsed, all 100 images loaded and decoded by the host (six at a time, `maxInFlight`), then the
  deal. Each run opens the pack under a new name (`big-1` … `big-5`), so no image comes from the
  host's cache; between runs Shapes is chosen again. Five runs from a folder, five over http
  from the stub server on 127.0.0.1.
- **Memory** is the process's physical footprint (`task_vm_info.phys_footprint`) at start and
  after the ten loads (1,000 distinct images), and what the host's image store holds against
  the app's `Sub.imageCache` budget (192 MiB).

## Results

Apple M4 Max, macOS 27.0.1, Pairs at its first `make bench`:

| | |
|---|---|
| 100-face pack from a folder | median 30 ms (60, 30, 30, 30, 25) |
| 100-face pack over http (loopback) | median 74 ms (102, 84, 74, 73, 72) |
| Footprint at start | 9.2 MiB |
| Footprint after 1,000 images | 225.1 MiB |
| Image store after 1,000 images | 768 images, 192.0 MiB: the budget, the rest evicted |

A 256 × 256 image is 256 KiB of pixels, so the budget holds 768 of them; the footprint above
the budget is the app, the host and the frames.
