#!/usr/bin/env python3
"""check_consts.py ENV.ixe NAMES OUT_DIR [--jobs N] [--cap SECONDS] [--mem GIB]

Checks each constant named in NAMES (one per line) as its own IxVM claim, N processes at a time,
with `ix check --keep-going`. Writes OUT_DIR/results.tsv: name, status, seconds, queries,
instructions, message. Status is

  ok       the kernel accepted the constant
  failed   the kernel rejected it; the message holds what ix printed
  absent   the environment has no constant of that name
  timeout  its execution passed the per-claim cap
  memory   its process grew past the per-process limit while executing it
  killed   its process died while executing it

A worker whose process stops in the middle of a claim resumes with the names after that claim.
Raw output is kept in OUT_DIR/workerK.log. Execution only; must run outside the command sandbox.
"""
import argparse
import os
import pty
import re
import signal
import subprocess
import threading
import time

PROJECT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# The ix wrapper to run; IXW selects another build than the pinned one.
IXW = os.environ.get("IXW", os.path.join(PROJECT, "ix/ixw"))
EXECUTE = re.compile(r"\[aiur\] execute (.*)")
VERIFIED = re.compile(r"verified claim in ([\d.]+)s \((\d+) queries, (\d+) instructions\)")
ABSENT = re.compile(r"(.*) not found in ")


class Memory:
    """Resident memory of each watched process group, sampled by one thread.

    Some ix builds execute each claim in a child process, so a worker's memory is its whole
    group's. One scan of /proc per second serves every worker; a scan per worker would open every
    process's files once per worker per second."""

    def __init__(self):
        self.lock = threading.Lock()
        self.groups = {}
        threading.Thread(target=self.sample, daemon=True).start()

    def watch(self, pgid):
        with self.lock:
            self.groups[pgid] = 0.0

    def forget(self, pgid):
        with self.lock:
            self.groups.pop(pgid, None)

    def gib(self, pgid):
        with self.lock:
            return self.groups.get(pgid, 0.0)

    def sample(self):
        page = os.sysconf("SC_PAGE_SIZE")
        while True:
            with self.lock:
                watched = set(self.groups)
            pages = dict.fromkeys(watched, 0)
            if watched:
                for entry in os.listdir("/proc"):
                    if not entry.isdigit():
                        continue
                    try:
                        with open(f"/proc/{entry}/stat") as f:
                            pgid = int(f.read().rsplit(")", 1)[1].split()[2])
                        if pgid not in pages:
                            continue
                        with open(f"/proc/{entry}/statm") as f:
                            pages[pgid] += int(f.read().split()[1])
                    except (OSError, ValueError, IndexError):
                        continue
            with self.lock:
                for pgid, n in pages.items():
                    if pgid in self.groups:
                        self.groups[pgid] = n * page / 2**30
            time.sleep(1)


def stop(proc):
    """Kill the process and everything it started."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        proc.kill()


class Sweep:
    def __init__(self, args):
        self.args = args
        self.lock = threading.Lock()
        self.recorded = set()
        self.memory = Memory()
        self.results = open(os.path.join(args.out, "results.tsv"), "w")

    def record(self, name, status, seconds="", queries="", instructions="", message=""):
        with self.lock:
            if name in self.recorded:
                return
            self.recorded.add(name)
            message = " | ".join(message.split("\n"))[:600].replace("\t", " ")
            self.results.write(f"{name}\t{status}\t{seconds}\t{queries}\t{instructions}\t{message}\n")
            self.results.flush()

    def lines(self, fd):
        """Lines from a pty until it closes. A pty keeps the child's output line-buffered, so the
        claim being executed is known when the process is stopped."""
        pending = b""
        while True:
            try:
                data = os.read(fd, 65536)
            except OSError:
                break
            if not data:
                break
            pending += data
            *whole, pending = pending.split(b"\n")
            for line in whole:
                yield line.decode("utf-8", "replace").rstrip("\r")
        if pending:
            yield pending.decode("utf-8", "replace")

    def worker(self, k, names):
        remaining = list(names)
        env = {"IX_PROFILE": "ci-pinned", **os.environ}
        with open(os.path.join(self.args.out, f"worker{k}.log"), "w") as log:
            while remaining:
                master, slave = pty.openpty()
                proc = subprocess.Popen(
                    [IXW, "check", "--ixe", self.args.env, "--keep-going", *remaining],
                    stdout=slave, stderr=slave, stdin=subprocess.DEVNULL, env=env,
                    start_new_session=True)
                os.close(slave)
                self.memory.watch(proc.pid)
                state = {"current": None, "since": 0.0, "stop": None}

                def watch():
                    while proc.poll() is None:
                        time.sleep(1)
                        if state["current"] is None:
                            continue
                        if time.time() - state["since"] > self.args.cap:
                            state["stop"] = "timeout"
                        elif self.memory.gib(proc.pid) > self.args.mem:
                            state["stop"] = "memory"
                        if state["stop"]:
                            stop(proc)
                            return

                threading.Thread(target=watch, daemon=True).start()
                message = []
                for line in self.lines(master):
                    log.write(line + "\n")
                    log.flush()
                    m = EXECUTE.match(line)
                    if m:
                        if state["current"] is not None:
                            self.record(state["current"], "failed", message="\n".join(message))
                        state["since"] = time.time()
                        state["current"] = m.group(1).strip()
                        message = []
                        continue
                    m = VERIFIED.match(line)
                    if m and state["current"] is not None:
                        self.record(state["current"], "ok", *m.groups())
                        state["current"] = None
                        continue
                    m = ABSENT.match(line)
                    if m and state["current"] is None:
                        self.record(m.group(1).strip(), "absent")
                        continue
                    if state["current"] is not None:
                        message.append(line)
                os.close(master)
                code = proc.wait()
                self.memory.forget(proc.pid)
                current = state["current"]
                if current is not None:
                    if state["stop"] or code < 0:
                        elapsed = f"{time.time() - state['since']:.1f}"
                        self.record(current, state["stop"] or "killed", elapsed, message="\n".join(message))
                    else:
                        self.record(current, "failed", message="\n".join(message))
                    remaining = remaining[remaining.index(current) + 1:]
                with self.lock:
                    left = [name for name in remaining if name not in self.recorded]
                if current is None and len(left) == len(remaining):
                    for name in left:
                        self.record(name, "killed", message=f"ix exited with {code} before executing it")
                    break
                remaining = left

    def run(self, names):
        jobs = max(1, min(self.args.jobs, len(names)))
        threads = [threading.Thread(target=self.worker, args=(k, names[k::jobs])) for k in range(jobs)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        self.results.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("env")
    parser.add_argument("names")
    parser.add_argument("out")
    parser.add_argument("--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--cap", type=float, default=600.0)
    parser.add_argument("--mem", type=float, default=60.0)
    args = parser.parse_args()
    os.makedirs(args.out, exist_ok=True)
    with open(args.names) as f:
        names = [line.strip() for line in f if line.strip()]
    started = time.time()
    Sweep(args).run(names)
    with open(os.path.join(args.out, "done"), "w") as f:
        f.write(f"{time.time() - started:.0f}\n")


if __name__ == "__main__":
    main()
