import CairnFrame
import CairnRender
import Darwin
import Foundation

/// `Pairs --bench` (`make bench`, through `cairn bench`): how long a 100-face pack takes to load,
/// from Enter in the pack field to the new game dealt, from a folder and over http from the stub
/// server, and how much memory the process holds before and after. Each run opens the pack under
/// a new name (`big-1` … `big-5`), so no image comes from the host's cache. Results go to stdout
/// and to `PAIRS_BENCH_OUT` (JSON) when set.
enum Bench {
    /// The process's physical footprint, in bytes (what Activity Monitor calls Memory).
    static func footprint() -> UInt64 {
        var info = task_vm_info_data_t()
        var count = mach_msg_type_number_t(MemoryLayout<task_vm_info_data_t>.size / MemoryLayout<integer_t>.size)
        let kr = withUnsafeMutablePointer(to: &info) {
            $0.withMemoryRebound(to: integer_t.self, capacity: Int(count)) { task_info(mach_task_self_, task_flavor_t(TASK_VM_INFO), $0, &count) }
        }
        return kr == KERN_SUCCESS ? info.phys_footprint : 0
    }

    static func mib(_ b: UInt64) -> Double { (Double(b) / 1_048_576 * 10).rounded() / 10 }

    static func run(_ d: Driver, packs: String, url: String?) -> Never {
        var results: [String: Any] = [:]
        d.until(3, "doesn't start on Shapes") { $0.ax.contains { $0.label == "Shapes" } }
        Thread.sleep(forTimeInterval: 0.5)
        let before = footprint()
        results["footprintStartMiB"] = mib(before)
        print("bench: footprint at start \(mib(before)) MiB")
        for (kind, base) in [("folder", packs), ("http", url)] {
            guard let base else { continue }
            var times: [Double] = []
            for i in 1...5 {
                // Back to Shapes between runs, so every run is a switch to a pack not on screen.
                d.menu(ControlRef(claim: 10, key: 0))
                d.until(10, "Shapes didn't come back") { f in f.ax.contains { $0.label == "Shapes" } && !d.has("Loading") }
                let t0 = Date()
                d.open("\(base)/big-\(i)")
                d.until(60, "the 100-face pack didn't load from \(kind)") { f in f.ax.contains { $0.label == "Hundred" } && d.cardCount(f) == 16 }
                times.append(Date().timeIntervalSince(t0) * 1000)
            }
            let sorted = times.sorted()
            let median = sorted[sorted.count / 2]
            results["\(kind)LoadMs"] = times.map { ($0 * 10).rounded() / 10 }
            results["\(kind)LoadMedianMs"] = (median * 10).rounded() / 10
            print("bench: 100-face pack from \(kind): median \(Int(median)) ms (runs \(times.map { Int($0) }) ms)")
        }
        Thread.sleep(forTimeInterval: 0.5)
        let after = footprint()
        results["footprintAfterMiB"] = mib(after)
        results["images"] = 100
        let store = ImageStore.shared
        results["imagesHeld"] = store.count
        results["imageBytesHeldMiB"] = mib(UInt64(store.bytes))
        print("bench: the host holds \(store.count) images, \(mib(UInt64(store.bytes))) MiB of pixels (budget 192 MiB)")
        print("bench: footprint after loading \(url == nil ? 5 : 10) × 100 images: \(mib(after)) MiB (+\(mib(after &- before)) MiB)")
        if let out = ProcessInfo.processInfo.environment["PAIRS_BENCH_OUT"],
           let data = try? JSONSerialization.data(withJSONObject: results, options: [.prettyPrinted, .sortedKeys]) {
            FileManager.default.createFile(atPath: out, contents: data)
            print("bench: wrote \(out)")
        }
        d.stop()
        exit(0)
    }
}
