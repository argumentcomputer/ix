import json
from pathlib import Path
import tempfile
import unittest

from analyze import intersect, memory_usage, read_spans, seconds, subtract, union


class Intervals(unittest.TestCase):
    def test_overlap_counts_once(self):
        self.assertEqual(union([(1, 5), (2, 4), (5, 9), (12, 15)]), [(1, 9), (12, 15)])
        self.assertEqual(intersect([(0, 10)], [(2, 5), (4, 7), (9, 12)]), [(2, 7), (9, 10)])
        self.assertEqual(subtract([(0, 10)], [(2, 5), (4, 7), (9, 12)]), [(0, 2), (7, 9)])

    def test_same_span_on_multiple_threads_and_reentry(self):
        events = [dict(event="new", id=1, tid="a", name="phase", fields={}, ts_ns=0)]
        for event, tid, stamp in [("enter", "a", 1), ("enter", "b", 2),
                                  ("enter", "a", 3), ("exit", "a", 4),
                                  ("exit", "b", 5), ("exit", "a", 6)]:
            events.append(dict(event=event, id=1, tid=tid, ts_ns=stamp))
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "spans.jsonl"
            path.write_text("\n".join(map(json.dumps, events)))
            result = read_spans(path)
        self.assertEqual(len(result), 3)
        self.assertAlmostEqual(seconds((s["start"], s["end"]) for s in result), 5e-9)

    def test_reused_device_address_and_unmatched_free(self):
        events = [dict(kind="memory", memory_kind=3, device=0, timestamp=i,
                       operation=op, address=address, bytes=size)
                  for i, (op, address, size) in enumerate([
                      (1, 100, 20), (1, 200, 30), (2, 100, 20),
                      (1, 100, 10), (2, 200, 30), (2, 100, 10), (2, 300, 5)])]
        result, _ = memory_usage(events)
        self.assertEqual(result, dict(peak_live_bytes=50, final_live_bytes=0, unmatched_frees=1))


if __name__ == "__main__":
    unittest.main()
