#!/usr/bin/env python3
"""Manual compiler landing checks. See docs/compiler-gates.md.

Python 3.11+, Lake, Lean, Cargo and an already provisioned benchmark workspace
are required. Nothing is downloaded, recorded into source, pushed or retried.
The caller reserves the machine and checks that its checkout is idle.
"""
import argparse
import collections
import contextlib
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time
import traceback


SUITES = """pass3-cliques validate-lean pass3 pass3-plan-cache twins canon-pass1
clique-transport clique-ownership aux-oracle aux-cert validate-lean-nc
adversarial-matrix decompile-diff compile-claim-conflict compile-claim-order
compiler-selected-closure-e2e o11a-decline compile-closure-whole
compile-caller-independence changed-set pack-units validate-aux aux-gen-diff
rust-decompile kernel-ixon-roundtrip pass3-rust-parity compile
compile-schedule-identity rust-serialize decompile canon-closure-aux ixon-corpus
aux-gen-closure commit-io rust-canon-roundtrip""".split()
BUILD = """Ix IxTests ix kernel-check-ixe canon-census ixe-diff IxSharingVerify
aux-shape-sweep checker-support-regression kernel-pin-gen compile-cert-c1
compile-certify Ix.CompileCert.ValueReceipt""".split()
REFERENCES = {
    'initstd': 'a2e22ee7f8d0fcf0d607047dda7d83749f20886f2d03f1cbaf2ede3a7d1ba676',
    'mathlib': 'd0427adf7b995f7f48c6fe5fa069c5d3a3d5c10c6f061425729e87339f6bf6db',
    'certs': '6f15c4176891a706e5f236400fce2574d4c7de8a2fb2e275514914545c89fed7',
}
# Strip diagnostic selectors, output/rerecord switches and runtime overrides.
# The suite defaults (including the full schedule tier and pack coverage) remain.
SCOPE_PREFIXES = ('IX_', 'PARITY_', 'PASS3_', 'SCHED_', 'AUX_', 'VALIDATE_',
                  'CHANGED_SET_', 'PACK_UNITS_', 'CLOSURE_', 'DEV_CENSUS_',
                  'L2A_SYN_', 'CHECK_IXE_', 'M1G_', 'IMAGE_GEN_', 'LSPEC_')
ARTIFACT_SUFFIXES = ('.olean', '.ilean', '.ir', '.o', '.a', '.so', '.dylib', '.dll', '.trace')
HEX = r'[0-9a-f]{64}'


def stage_names(args):
    names = ['source-pre', 'references-pre', 'inputs-pre', 'space']
    if args.phase in ('core', 'all'):
        names += ['ixc-build', 'build', 'cargo-fmt', 'cargo-clippy', 'cargo-test', 'native-refresh', 'test']
        names += ['suite-' + s for s in SUITES + args.extra_suite]
        names += ['aux-shape-sweep', 'checker-support-regression', 'parity-initstd',
                  'prepare-initstd-imports', 'initstd-provenance-pre', 'initstd-rust', 'initstd-lean']
        names += [f'refuse-{backend}-{mode}' for backend in ('compile', 'compile-lean') for mode in ('off', 'bogus')]
        names += ['initstd-rust-images', 'initstd-lean-images', 'initstd-plans', 'initstd-provenance-post',
                  'pass3-lib', 'kernel-check', 'kernel-rows', 'pin-controls', 'pin-gen',
                  'pin-data-PinData', 'pin-data-NatOpPinData', 'lint', 'prepare-cert-output', 'check-cert',
                  'archive-cert', 'prepare-kernel-output', 'check-kernel', 'archive-kernel']
        names += ['toolchain-' + p for p in ('Benchmarks-Compile', 'IxC', 'Models-SetTheory')]
    if args.phase == 'all':
        names += ['core-complete']
    if args.phase in ('mathlib', 'all'):
        names += ['mathlib-native-build', 'prepare-mathlib-imports', 'mathlib-provenance-pre',
                  'mathlib-rust', 'mathlib-lean', 'mathlib-provenance-post']
    return names + ['artifacts-post', 'source-post', 'references-post', 'inputs-post']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    before = path.stat()
    with path.open('rb') as stream:
        value = hashlib.file_digest(stream, 'sha256').hexdigest()
    after = path.stat()
    require((before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_size, after.st_mtime_ns, after.st_ctime_ns), f'changed while hashing: {path}')
    return value


def identity(path):
    path = Path(path)
    return {'path': str(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None,
            'bytes': path.stat().st_size, 'mode': path.stat().st_mode & 0o7777,
            'sha256': sha(path)}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def manifest(path):
    rows = {}
    for line in path.read_text().splitlines():
        digest, name = line.split('  ', 1)
        rel = Path(name)
        require(re.fullmatch(HEX, digest) and not rel.is_absolute() and
                '..' not in rel.parts and str(rel) == name and name not in rows,
                f'invalid source manifest row: {name!r}')
        rows[name] = digest
    require(rows, 'empty source manifest')
    return rows


def tree(path, *, artifacts=False, ancestors=(), source_only=False):
    """Available files, with symlink targets; never silently skip a missing root."""
    real = path.resolve(strict=True)
    require(real not in ancestors, f'directory link cycle: {path}')
    result = []
    for entry in sorted(path.iterdir()):
        if entry.name == '.git' or source_only and entry.name in ('.lake', 'target'):
            continue
        if entry.is_dir():
            result.extend(tree(entry, artifacts=artifacts, ancestors=(*ancestors, real), source_only=source_only))
        else:
            require(entry.is_file(), f'nonregular/dangling input: {entry}')
            if not artifacts or any(s in entry.suffixes for s in ARTIFACT_SUFFIXES):
                result.append(identity(entry))
    return result


def normalize_pins(kind, text):
    """Exactly the two Init-source fields; the certificate digest is immutable."""
    if kind == 'PinData':
        patterns = [rf'^(\(coverage, never soundness\)\. Source: sha256 )({HEX})(\.)$',
                    rf'^(def source : String := "sha256:)({HEX})(")$']
    else:
        patterns = [rf'^(  )({HEX})(\), as the Ixon reader reads them;)$',
                    rf'^(def source : String := "sha256:)({HEX})( sha256:{HEX}")$']
    counts = []
    for pattern in patterns:
        text, count = re.subn(pattern, lambda m: m[1] + '0' * 64 + m[3], text, flags=re.M)
        counts.append(count)
    require(counts == [1, 1], f'{kind}: missing/duplicate provenance field: {counts}')
    return text


class Gate:
    def __init__(self, args):
        self.args = args
        self.root = Path(__file__).resolve().parent.parent
        self.out = args.out.absolute()
        self.env = dict(os.environ)
        test_settings = set()
        for path in (self.root / 'Tests').rglob('*.lean'):
            test_settings.update(re.findall(r'\b(?:IO\.)?getEnv\s+"([A-Z][A-Z0-9_]*)"', path.read_text()))
        test_settings -= {'PATH', 'HOME', 'USER', 'TMPDIR'}
        removed = sorted(k for k in self.env if k in test_settings or k.startswith(SCOPE_PREFIXES) or k in
                         ('LEAN_PATH', 'LEAN_SRC_PATH', 'PYTHONOPTIMIZE', 'RUSTC_WRAPPER',
                          'RUSTC_WORKSPACE_WRAPPER', 'LAKE_OVERRIDE_LEAN', 'LEAN_GITHASH',
                          'CARGO_TARGET_DIR', 'CARGO_BUILD_TARGET_DIR'))
        for key in removed:
            self.env.pop(key)
        self.env.update(IX_COMPILE_WORKERS=str(args.workers), RAYON_NUM_THREADS=str(args.workers),
                        CARGO_BUILD_JOBS=str(args.cargo_jobs), IX_RUST_CHECK_SERIAL='1',
                        LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false',
                        CARGO_NET_OFFLINE='true', GIT_OPTIONAL_LOCKS='0')
        self.version = subprocess.check_output(['lean', '--version'], env=self.env, text=True).strip()
        print(self.version, flush=True)
        print(f'== commit: {args.commit}', flush=True)
        require('version 4.34.1,' in self.version and 'commit 5045d0056413266e57c625dcd7c365b10e377c52' in self.version,
                'use the pinned Lean 4.34.1 toolchain')
        self.results = []
        self.blocked = None
        self.evidence_error = False
        self.source_before = None
        self.library_before = {}
        self.snapshot_inputs = {}
        self.artifacts = {}
        self.lane_prepared = set()
        write_json(self.out / 'planned-stages.json', stage_names(args))
        write_json(self.out / 'invocation.json', {
            'commit': args.commit, 'phase': args.phase, 'argv': sys.argv,
            'root': str(self.root), 'workers': args.workers, 'cargo_jobs': args.cargo_jobs,
            'kernel_jobs': 1, 'rust_check': 'serial', 'removed_environment_keys': removed,
            'scope_environment': {k: self.env[k] for k in
                ('IX_COMPILE_WORKERS', 'RAYON_NUM_THREADS', 'CARGO_BUILD_JOBS', 'IX_RUST_CHECK_SERIAL')},
            'runner': identity(Path(__file__)), 'source_manifest': identity(args.source_manifest),
            'pid': os.getpid(), 'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        })

    def run(self, name, action, *, critical=False, force=False, cwd=None, env=None, check=None):
        row = {'stage': name, 'status': 'not-run', 'rc': None, 'command_rc': None,
               'reason': self.blocked, 'seconds': 0,
               'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
        path = self.out / (name + '.log')
        if not self.blocked or force:
            started = time.monotonic()
            try:
                with path.open('x') as log:
                    log.write(f'{self.version}\n== commit: {self.args.commit}\n== stage: {name}\n')
                    if callable(action):
                        row['command'] = 'internal:' + name
                    else:
                        row['command'] = [str(x) for x in action]
                        log.write('COMMAND ' + shlex.join(row['command']) + '\n')
                    log.flush()
                    try:
                        with contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
                            if callable(action):
                                action()
                                rc = 0
                            else:
                                rc = subprocess.run(row['command'], cwd=cwd or self.root,
                                    env={**self.env, **(env or {})}, stdout=log,
                                    stderr=subprocess.STDOUT).returncode
                                if rc < 0:
                                    rc = 128 - rc
                            row['command_rc'] = rc
                            log.flush()
                            if check is not None:
                                check(rc, path)
                                rc = 0
                            row['rc'] = rc
                    except OSError:
                        self.evidence_error = True
                        row['rc'] = 97
                        traceback.print_exc(file=log)
                    except Exception:
                        row['rc'] = 1
                        traceback.print_exc(file=log)
                    log.flush()
                row['status'] = 'pass' if row['rc'] == 0 else 'fail'
                row['seconds'] = round(time.monotonic() - started, 3)
                row['log'] = identity(path)
                # Retain the full log; this is only an index of its summary lines.
                row['summaries'] = [line for line in path.read_text(errors='replace').splitlines()
                    if re.search(r'^\[|^(Build completed|test result:|check-ixe: done|EXACT_|PIN_|BYTE_)', line)]
            except OSError as error:
                self.evidence_error = True
                row.update(status='evidence-error', rc=97, reason=str(error))
            if row['status'] != 'pass' and critical:
                self.blocked = f'prerequisite {name} failed'
            if self.evidence_error:
                self.blocked = 'required evidence or command I/O failed'
        self.results.append(row)
        try:
            write_json(self.out / 'stages.json', self.results)
            with (self.out / 'stages.tsv').open('a') as stream:
                stream.write(f"{name}\t{row['status']}\t{row['rc']}\t{row['seconds']}\n")
            print(f"{name}: {row['status']} rc={row['rc']} ({row['seconds']} s)", flush=True)
        except OSError:
            self.evidence_error = True
            self.blocked = 'required evidence write failed'

    def source(self, label):
        require(sha(self.args.source_manifest) == self.args.source_sha, 'source manifest changed')
        rows = manifest(self.args.source_manifest)
        require('scripts/compiler-gate.py' in rows and 'Tests/Main.lean' in rows,
                'manifest must include the runner and complete tracked source')
        found = []
        for name, digest in rows.items():
            path = self.root / name
            require(path.resolve().is_relative_to(self.root), f'escaping source: {name}')
            item = identity(path)
            found.append(item)
            require(item['sha256'] == digest, f'source differs: {name}')
        write_json(self.out / f'source-{label}.json', found)
        if label == 'pre':
            self.source_before = found
        else:
            require(found == self.source_before, 'source identity changed during the gate')

    def references(self, label):
        paths = {key: getattr(self.args, key + '_ref') for key in REFERENCES}
        expected = {**REFERENCES, 'legacy': self.args.legacy_sha, 'kernel': self.args.kernel_baseline_sha}
        paths.update(legacy=self.args.legacy_ref, kernel=self.args.kernel_baseline)
        result = {name: identity(path) for name, path in paths.items()}
        write_json(self.out / f'references-{label}.json', result)
        require(all(row['sha256'] == expected[name] for name, row in result.items()), 'reference hash mismatch')
        if label == 'pre':
            self.refs_before = result
        else:
            require(result == self.refs_before, 'reference identity changed')

    def inputs(self, label):
        """Source/dependency/tool identities; compiled artifacts get a separate interval."""
        result = {'tools': [], 'dependencies': [], 'benchmark': []}
        for tool in ('lean', 'lake', 'cargo', 'rustc'):
            path = shutil.which(tool, path=self.env.get('PATH'))
            require(path is not None, f'missing tool: {tool}')
            row = {'name': tool, **identity(Path(path)), 'version':
                   subprocess.check_output([tool, '--version'], env=self.env, text=True).strip()}
            if Path(path).resolve().name == 'rustup':
                actual = subprocess.check_output(['rustup', 'which', tool], env=self.env, text=True).strip()
                row['actual'] = identity(Path(actual))
            wrapped = Path(path).resolve().parent / ('.' + tool + '-wrapped')
            if wrapped.is_file():
                row['wrapped'] = identity(wrapped)
            result['tools'].append(row)
        for workspace in (self.root, self.args.benchmark_dir, self.root / 'IxC', self.root / 'Models/SetTheory'):
            lock = json.loads((workspace / 'lake-manifest.json').read_text())
            for entry in lock['packages']:
                if entry['type'] != 'git':
                    continue
                package = workspace / lock.get('packagesDir', '.lake/packages') / entry['name']
                # Lean names may be quoted in JSON but use the unquoted directory spelling.
                if not package.exists() and entry['name'].startswith('«') and entry['name'].endswith('»'):
                    package = package.with_name(entry['name'][1:-1])
                files = tree(package, source_only=True)
                require(files, f'dependency not provisioned: {package}')
                git = ['git', '-C', str(package)]
                head = subprocess.check_output(git + ['rev-parse', 'HEAD'], env=self.env, text=True).strip()
                require(head == entry['rev'], f'dependency revision differs from lock: {package}')
                subprocess.run(git + ['diff', '--quiet', 'HEAD', '--'], env=self.env, check=True)
                result['dependencies'].append({'workspace': str(workspace), 'package': entry,
                                               'directory': str(package), 'head': head, 'files': files})
        for name in ('CompileInitStd.lean', 'CompileMathlib.lean', 'lakefile.toml',
                     'lake-manifest.json', 'lean-toolchain'):
            result['benchmark'].append(identity(self.args.benchmark_dir / name))
        write_json(self.out / f'inputs-{label}.json', result)
        if label == 'pre':
            self.snapshot_inputs = result
        else:
            require(result == self.snapshot_inputs, 'tool/dependency/benchmark identity changed')

    def imports(self, label, group):
        result = {'views': [], 'files': {}}
        for cwd in (self.root, self.args.benchmark_dir):
            query = ('import os,json,subprocess; print(json.dumps({'
                     '"prefix":subprocess.check_output(["lean","--print-prefix"],text=True).strip(),'
                     '"paths":{k:os.environ.get(k,"") for k in '
                     '["LEAN_PATH","LEAN_SRC_PATH","LD_LIBRARY_PATH"]}}))')
            view = json.loads(subprocess.check_output(['lake', '--offline', '--no-cache', 'env', sys.executable, '-I', '-B', '-c', query],
                cwd=cwd, env=self.env, text=True))
            require(view['paths']['LEAN_PATH'], 'empty effective Lean import path')
            view['cwd'] = str(cwd)
            result['views'].append(view)
            roots = [Path(view['prefix']) / 'lib']
            for key, value in view['paths'].items():
                for raw in filter(None, value.split(os.pathsep)):
                    path = Path(raw) if Path(raw).is_absolute() else cwd / raw
                    if path.exists():
                        roots.append(path)
                    else:
                        result['files'][str(path)] = {'absent': True}
            for path in roots:
                if str(path) not in result['files']:
                    result['files'][str(path)] = tree(path)
        # Pin all generated native inputs/executables, not just the ix command.
        for path in (self.root / '.lake/build/lib', self.root / '.lake/build/bin'):
            result['files'][str(path)] = tree(path)
        write_json(self.out / f'{group}-imports-{label}.json', result)
        if label == 'pre':
            self.library_before[group] = result
        else:
            require(result == self.library_before[group], f'{group}: import/native identity changed')

    def byte_check(self, name, reference, aligned=False, note=False, plans=False):
        def check(rc, log):
            require(rc == 0, f'{name}: compiler failed ({rc})')
            output = self.out / (name + '.ixe')
            row = identity(output)
            self.artifacts[name] = row
            write_json(self.out / 'artifacts.json', self.artifacts)
            require(row['sha256'] == REFERENCES[reference], f'{name}: default bytes moved; output retained')
            with output.open('rb') as a, getattr(self.args, reference + '_ref').open('rb') as b:
                while True:
                    x, y = a.read(8 * 1024**2), b.read(8 * 1024**2)
                    require(x == y, f'{name}: byte comparison failed')
                    if not x:
                        break
            text = log.read_text()
            if aligned:
                require(text.count(f'[compile-lean] ALIGNED: {row["bytes"]} bytes byte-identical with Rust') == 1,
                        'missing/duplicate Rust alignment result')
            if note:
                require('note: IX_PASS3=images has no effect' in text, 'missing deprecation note')
            if plans:
                matches = re.findall(r'\[pass3\] clique plan table: (\d+) plans, (\d+) taken from the table '
                                     r'\(each recomputed and equal: IX_PASS3_CHECK_PLANS\)', text)
                require(len(matches) == 1 and all(int(n) > 0 for n in matches[0]), 'no checked plan reuse')
            print(f'BYTE_IDENTICAL {name} {row["bytes"]} {row["sha256"]}')
        return check

    def pin_compare(self, kind, expected, actual, label):
        e, a = expected.read_bytes().decode('utf-8'), actual.read_bytes().decode('utf-8')
        diff = ''.join(difflib.unified_diff(e.splitlines(True), a.splitlines(True), str(expected), str(actual)))
        (self.out / (label + '.diff')).write_text(diff)
        require(normalize_pins(kind, e) == normalize_pins(kind, a), f'{kind}: generated pin data differs')
        print(f'PIN_DATA_EXACT {kind}; only two Init-source fields normalized')

    def pin_controls(self):
        controls = []
        for kind, marker in (('PinData', '  ([.inl "And"], "'), ('NatOpPinData', '  ("Nat.div", ')):
            source = self.root / f'IxC/Kernel/Ixon/{kind}.lean'
            original = source.read_bytes().decode('utf-8')
            require('\n' in original and '\r' not in original, f'{kind}: expected an LF control baseline')
            start = original.index(marker) + len(marker)
            changed = original[:start] + ('1' if original[start] == '0' else '0') + original[start + 1:]
            cases = [('unchanged', original, True), ('provenance-only', normalize_pins(kind, original), True),
                     ('changed-data', changed, False)]
            if kind == 'NatOpPinData':
                altered, count = re.subn(rf'(def source : String := "sha256:{HEX} sha256:)([0-9a-f])',
                    lambda m: m[1] + ('1' if m[2] == '0' else '0'), original)
                require(count == 1, 'certificate control did not select its exact field')
                cases.append(('changed-certificate-digest', altered, False))
            cases += [('crlf', original.replace('\n', '\r\n'), False),
                      ('lone-cr', original.replace('\n', '\r'), False)]
            for label, text, expected in cases:
                actual = self.out / f'control-{kind}-{label}.lean'
                actual.write_bytes(text.encode('utf-8'))
                if label not in ('crlf', 'lone-cr'):
                    equal = normalize_pins(kind, original) == normalize_pins(kind, text)
                    require(equal == expected, f'pin control failed: {kind}/{label}')
                accepted = True
                try:
                    self.pin_compare(kind, source, actual, f'control-{kind}-{label}')
                except RuntimeError as failure:
                    accepted = False
                    print(f'PIN_CONTROL_REJECT {kind}/{label}: {failure}')
                require(accepted == expected, f'pin file comparison control failed: {kind}/{label}')
                controls.append({'kind': kind, 'control': label, 'accepted': accepted})
        require(len(controls) == 11, 'pin control inventory changed')
        write_json(self.out / 'pin-controls.json', controls)
        print('PIN_CONTROLS_OK 11')

    def kernel_rows(self):
        def load(path):
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            require(rows and len({r['address'] for r in rows}) == len(rows), 'empty/duplicate checker rows')
            for row in rows:
                require(set(row) == {'address', 'names', 'kind', 'outcome', 'reason', 'micros', 'readMicros'},
                        'checker row schema changed')
                require(row['outcome'] in ('accept', 'decline', 'reject', 'blocked'), 'unknown checker outcome')
                require(all(isinstance(row[k], int) and row[k] >= 0 for k in ('micros', 'readMicros')),
                        'invalid row timing')
            return [{k: v for k, v in row.items() if k not in ('micros', 'readMicros')} for row in rows]
        expected, observed = load(self.args.kernel_baseline), load(self.out / 'kernel.jsonl')
        write_json(self.out / 'kernel-accounting.json', {'rows': len(observed),
            'outcomes': dict(collections.Counter(row['outcome'] for row in observed)),
            'ordered_semantics_equal': observed == expected})
        require(observed == expected, 'checker coverage/outcome/reason/name/order differs from reviewed baseline')
        require('check-ixe: done in ' in (self.out / 'kernel-check.log').read_text(), 'missing checker completion')
        print(f'EXACT_KERNEL_ROWS_OK {len(observed)}')

    def lane_files(self, kind, prepare=False):
        require(prepare or kind in self.lane_prepared, f'{kind} output preparation did not complete')
        if kind == 'cert':
            paths = [self.root / '.lake/build/compile-cert']
        else:
            paths = [self.root / '.lake/build' / name for name in (
                'kernel-codec.log', 'kernel-order.jsonl', 'kernel-entry-cases.jsonl', 'kernel-reader-fidelity.log')]
        dest = self.out / (('prior-' if prepare else '') + kind + '-details')
        dest.mkdir()
        producer = 'check-cert' if kind == 'cert' else 'check-kernel'
        succeeded = any(row['stage'] == producer and row['status'] == 'pass' for row in self.results)
        for path in paths:
            require(not path.is_symlink(), f'unexpected lane-output symlink: {path}')
            if path.exists():
                if prepare:
                    # Preserve stale build-cache evidence separately; never accept it as this run's result.
                    shutil.move(str(path), dest / path.name)
                elif path.is_dir():
                    shutil.copytree(path, dest / path.name, symlinks=True)
                else:
                    shutil.copy2(path, dest / path.name)
            elif not prepare:
                print(f'NOT_PRODUCED {path}')
                require(not succeeded, f'{producer} returned success without expected evidence: {path}')
        write_json(self.out / (dest.name + '.json'), tree(dest))
        if prepare:
            self.lane_prepared.add(kind)

    def artifacts_post(self):
        result = []
        for path in sorted(self.out.iterdir()):
            if path.suffix in ('.ixe', '.tmp', '.jsonl', '.lean') or path.name.endswith('.changed.json'):
                require(path.is_file() and not path.is_symlink(), f'nonregular output: {path}')
                result.append(identity(path))
        write_json(self.out / 'outputs-post.json', result)
        by_path = {row['path']: row for row in result}
        require(all(by_path.get(row['path']) == row for row in self.artifacts.values()),
                'previously hashed compiler output changed or disappeared')

    def compile(self, name, backend, library, **checks):
        args = [self.root / '.lake/build/bin/ix', backend, self.args.benchmark_dir /
                ('CompileInitStd.lean' if library == 'initstd' else 'CompileMathlib.lean'),
                '--out', self.out / (name + '.ixe')]
        if backend == 'compile':
            args += ['--no-build']
        else:
            args += ['--workers', str(self.args.workers)]
        if checks.get('aligned'):
            args += ['--rust-check']
        env = {'IX_PASS3': 'images'} if checks.get('note') else {}
        if checks.get('plans'):
            env['IX_PASS3_CHECK_PLANS'] = '1'
        self.run(name, args, env=env, critical=True, check=self.byte_check(name, library, **checks))

    def schedule(self):
        a, root = self.args, self.root
        lake = ['lake', '--offline', '--no-cache']
        self.run('source-pre', lambda: self.source('pre'), critical=True)
        self.run('references-pre', lambda: self.references('pre'), critical=True)
        self.run('inputs-pre', lambda: self.inputs('pre'), critical=True)
        self.run('space', lambda: require(shutil.disk_usage(root).free >= a.min_free_gb * 10**9,
                                         'insufficient declared startup disk floor'), critical=True)
        if a.phase in ('core', 'all'):
            self.run('ixc-build', lake + ['-d', 'IxC', 'build', '--wfail'], critical=True)
            self.run('build', lake + ['build', '--wfail'] + BUILD, critical=True)
            self.run('cargo-fmt', ['cargo', 'fmt', '--all', '--', '--check'], critical=True)
            self.run('cargo-clippy', ['cargo', 'clippy', '--release', '--workspace', '--all-targets',
                '--features', 'ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi,ixon/sharing-profile', '--', '-D', 'warnings'], critical=True)
            self.run('cargo-test', ['cargo', 'test', '--release', '--workspace'], critical=True)
            self.run('native-refresh', lake + ['build', '--wfail', 'IxTests', 'ix', 'kernel-check-ixe', 'compile-certify'], critical=True)
            self.run('test', lake + ['test', '--wfail'])
            for suite in SUITES + a.extra_suite:
                self.run('suite-' + suite, lake + ['test', '--wfail', '--', '--ignored', suite])
            self.run('aux-shape-sweep', lake + ['exe', 'aux-shape-sweep', 'self-check'])
            self.run('checker-support-regression', lake + ['exe', 'checker-support-regression'])
            self.run('parity-initstd', lake + ['test', '--wfail', '--', '--ignored', 'pass3-rust-parity'],
                     env={'PARITY_FILE': str(a.benchmark_dir / 'CompileInitStd.lean')})
            self.run('prepare-initstd-imports', lake + ['build', '--wfail', 'CompileInitStd'],
                     cwd=a.benchmark_dir, critical=True)
            self.run('initstd-provenance-pre', lambda: self.imports('pre', 'initstd'), critical=True)
            self.compile('initstd-rust', 'compile', 'initstd')
            self.compile('initstd-lean', 'compile-lean', 'initstd', aligned=True)
            for backend in ('compile', 'compile-lean'):
                for mode in ('off', 'bogus'):
                    name = f'refuse-{backend}-{mode}'
                    output = self.out / (name + '.ixe')
                    def refusal(rc, log, backend=backend, mode=mode, output=output):
                        expected = 'the legacy call-site surgery was deleted' if mode == 'off' else 'IX_PASS3=bogus is not a mode'
                        require(rc != 0 and (backend != 'compile-lean' or rc == 2) and
                                expected in log.read_text() and not output.exists() and not output.is_symlink(),
                                'invalid-mode control failed: exit, diagnostic or output')
                    self.run(name, [root / '.lake/build/bin/ix', backend, a.benchmark_dir / 'CompileInitStd.lean',
                        '--out', output], env={'IX_PASS3': mode}, check=refusal)
            self.compile('initstd-rust-images', 'compile', 'initstd', note=True)
            self.compile('initstd-lean-images', 'compile-lean', 'initstd', note=True)
            self.compile('initstd-plans', 'compile-lean', 'initstd', plans=True)
            self.run('initstd-provenance-post', lambda: self.imports('post', 'initstd'), critical=True, force=True)
            self.run('pass3-lib', lake + ['test', '--wfail', '--', '--ignored', 'pass3'],
                     env={'PASS3_LIB': f'{a.legacy_ref},{self.out / "initstd-lean.ixe"}', 'PASS3_LIB_ALL': '1'})
            self.run('kernel-check', [root / '.lake/build/bin/kernel-check-ixe', self.out / 'initstd-lean.ixe',
                                     self.out / 'kernel.jsonl'])
            self.run('kernel-rows', self.kernel_rows)
            self.run('pin-controls', self.pin_controls)
            self.run('pin-gen', [root / '.lake/build/bin/kernel-pin-gen', self.out / 'initstd-lean.ixe',
                     a.certs_ref, self.out / 'PinData.lean', self.out / 'NatOpPinData.lean'], critical=True)
            for kind in ('PinData', 'NatOpPinData'):
                self.run('pin-data-' + kind, lambda kind=kind: self.pin_compare(kind,
                    root / f'IxC/Kernel/Ixon/{kind}.lean', self.out / (kind + '.lean'), 'pin-data-' + kind))
            self.run('lint', lake + ['lint', '--', '--wfail'])
            self.run('prepare-cert-output', lambda: self.lane_files('cert', prepare=True), critical=True)
            self.run('check-cert', lake + ['run', 'check-cert'])
            self.run('archive-cert', lambda: self.lane_files('cert'), force=True)
            self.run('prepare-kernel-output', lambda: self.lane_files('kernel', prepare=True), critical=True)
            self.run('check-kernel', lake + ['run', 'check-kernel', '--with-model'])
            self.run('archive-kernel', lambda: self.lane_files('kernel'), force=True)
            for package in ('Benchmarks/Compile', 'IxC', 'Models/SetTheory'):
                self.run('toolchain-' + package.replace('/', '-'), lambda package=package:
                    require((root / 'lean-toolchain').read_bytes() == (root / package / 'lean-toolchain').read_bytes(),
                            'toolchain mismatch: ' + package))
        if a.phase in ('mathlib', 'all'):
            if a.phase == 'all':
                self.run('core-complete', lambda: require(all(row['status'] == 'pass' for row in self.results),
                                                         'core stage failed; Mathlib not started'), critical=True)
            self.run('mathlib-native-build', lake + ['build', '--wfail', 'ix'], critical=True)
            self.run('prepare-mathlib-imports', lake + ['build', '--wfail', 'CompileMathlib'],
                     cwd=a.benchmark_dir, critical=True)
            self.run('mathlib-provenance-pre', lambda: self.imports('pre', 'mathlib'), critical=True)
            self.compile('mathlib-rust', 'compile', 'mathlib')
            self.compile('mathlib-lean', 'compile-lean', 'mathlib', aligned=True)
            self.run('mathlib-provenance-post', lambda: self.imports('post', 'mathlib'), force=True, critical=True)
        self.run('artifacts-post', self.artifacts_post, force=True)
        self.run('source-post', lambda: self.source('post'), force=True)
        self.run('references-post', lambda: self.references('post'), force=True)
        self.run('inputs-post', lambda: self.inputs('post'), force=True)

    def finish(self):
        expected = stage_names(self.args)
        observed = [row['stage'] for row in self.results]
        if observed != expected:
            self.evidence_error = True
            for name in expected:
                if name not in observed:
                    self.results.append({'stage': name, 'status': 'not-run', 'rc': None,
                                         'reason': 'unexpected termination before stage'})
            write_json(self.out / 'stages.json', self.results)
        rc = 97 if self.evidence_error else int(any(r['status'] != 'pass' for r in self.results))
        result = {'commit': self.args.commit, 'source_sha256': self.args.source_sha,
                  'phase': self.args.phase, 'rc': rc, 'stages': self.results,
                  'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                  'workers': self.args.workers, 'artifacts': self.artifacts,
                  'planned_stages': expected,
                  'pending_sections': [] if self.args.phase == 'all' else
                      ['mathlib' if self.args.phase == 'core' else 'core'],
                  'full_common_gate': self.args.phase == 'all' and rc == 0,
                  'package_specific_acceptance': 'separate; review named package obligations and all summaries'}
        write_json(self.out / 'result.json', result)
        (self.out / 'driver.rc').write_text(str(rc) + '\n')
        print(f'COMPILER_GATE phase={self.args.phase} stages={len(self.results)} RC={rc}', flush=True)
        return rc


def main():
    require(not sys.flags.optimize, 'optimized Python is forbidden')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--phase', choices=('core', 'mathlib', 'all'), required=True)
    p.add_argument('--commit', required=True, help='full reviewed source commit (not inferred from remote checkout)')
    p.add_argument('--source-manifest', type=Path, required=True, help='complete SHA256SUMS for that committed source')
    p.add_argument('--source-sha', required=True, help='externally reviewed hash of the source manifest')
    p.add_argument('--benchmark-dir', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True, help='fresh evidence directory; all output artifacts are retained')
    for ref in ('initstd', 'mathlib', 'certs', 'legacy'):
        p.add_argument('--' + ref + '-ref', type=Path, required=True)
    p.add_argument('--legacy-sha', required=True, help='reviewed historical Init+Std comparison input hash')
    p.add_argument('--kernel-baseline', type=Path, required=True, help='reviewed full ordered Init+Std checker JSONL')
    p.add_argument('--kernel-baseline-sha', required=True)
    p.add_argument('--workers', type=int, required=True, help='Lean workers and Rust scheduler/Rayon ceiling; typically 32')
    p.add_argument('--cargo-jobs', type=int, default=4)
    p.add_argument('--min-free-gb', type=int, default=100, help='startup floor in decimal GB; not a live quota')
    p.add_argument('--extra-suite', action='append', default=[], help='additional ignored package suite; never replaces defaults')
    a = p.parse_args()
    require(re.fullmatch('[0-9a-f]{40}', a.commit), 'expected full commit hash')
    require(all(re.fullmatch(HEX, v) for v in (a.source_sha, a.legacy_sha, a.kernel_baseline_sha)), 'expected full hashes')
    require(a.workers > 0 and a.cargo_jobs > 0 and a.min_free_gb >= 100, 'invalid resource setting')
    require(len(a.extra_suite) == len(set(a.extra_suite)) and not set(a.extra_suite) & set(SUITES) and
            all(re.fullmatch('[a-z][a-z0-9-]+', name) for name in a.extra_suite), 'duplicate/invalid extra suite')
    for key, value in vars(a).items():
        if isinstance(value, Path):
            setattr(a, key, value.absolute())
    root = Path(__file__).resolve().parent.parent
    require(Path.cwd().resolve() == root, 'run from the checkout root')
    require(a.benchmark_dir.resolve() == root / 'Benchmarks/Compile', 'use this checkout\'s benchmark workspace')
    require(a.out == a.out.resolve() and a.out != root / 'out' and a.out.is_relative_to(root / 'out'),
            '--out must be a fresh nonsymlink path below checkout/out')
    require(not a.out.exists() and not a.out.is_symlink(), 'output path already exists')
    require(',' not in str(a.legacy_ref) + str(a.out), 'PASS3_LIB paths cannot contain commas')
    root.joinpath('.lake').mkdir(exist_ok=True)
    lock = root / '.lake/compiler-gate.lock'
    with lock.open('x') as stream:
        stream.write(json.dumps({'pid': os.getpid(), 'out': str(a.out), 'commit': a.commit}) + '\n')
    gate = None
    owns_output = False
    try:
        a.out.mkdir(parents=True)
        owns_output = True
        gate = Gate(a)
        gate.schedule()
        return gate.finish()
    except BaseException:
        traceback.print_exc()
        if gate is not None:
            try:
                gate.evidence_error = True
                gate.finish()
            except Exception:
                traceback.print_exc()
        elif owns_output:
            try:
                write_json(a.out / 'result.json', {'commit': a.commit, 'phase': a.phase, 'rc': 97,
                    'planned_stages': stage_names(a), 'stages': [], 'full_common_gate': False,
                    'error': traceback.format_exc()})
                (a.out / 'driver.rc').write_text('97\n')
            except OSError:
                traceback.print_exc()
        return 97
    finally:
        lock.unlink()


if __name__ == '__main__':
    raise SystemExit(main())
