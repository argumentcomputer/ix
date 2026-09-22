import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tomllib

root = Path(__file__).resolve().parents[2]
backend = root.parent / 'multi-stark'
output = root / 'target/shared-execution-build'
output.mkdir(parents=True, exist_ok=True)
config = root / '.cargo/config.toml'
lock = root / 'Cargo.lock'
original_config = config.read_bytes()
original_lock = lock.read_bytes()
patched_config = original_config + (
    '\n\n[patch."https://github.com/argumentcomputer/multi-stark.git"]\n'
    f'multi-stark = {{ path = {json.dumps(str(backend))} }}\n'
).encode()

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def git(directory, *args):
    return subprocess.check_output(['git', '-C', str(directory), *args])

def source_state():
    extra = ['Ix/Aiur/Stages/Codegen.lean', *git(root, 'ls-files', '--others', '--exclude-standard', '--', 'crates').decode().splitlines()]
    return {
        'ix': git(root, 'diff', '--binary', 'HEAD', '--', 'crates').decode(),
        'multi-stark': git(backend, 'diff', '--binary', 'HEAD').decode(),
        'extra_sources': {path: digest(root / path) for path in extra},
    }

before = source_state()
for name in ('ix', 'multi-stark'):
    (output / f'{name}.patch').write_text(before[name])
for path in before['extra_sources']:
    destination = output / 'source' / path
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(root / path, destination)
(output / 'Cargo.lock.original').write_bytes(original_lock)
(output / 'cargo-config.toml').write_bytes(patched_config)
lean = Path('/home/sam/.elan/toolchains/leanprover--lean4---v4.33.1')
settings = {
    'CARGO_BUILD_JOBS': str(len(os.sched_getaffinity(0))),
    'CARGO_NET_OFFLINE': 'true',
    'LEAN_NUM_THREADS': str(len(os.sched_getaffinity(0))),
    'RAYON_NUM_THREADS': str(len(os.sched_getaffinity(0))),
    'MULTI_STARK_CUDA_ARCHS': '120',
    'IX_CUDA': '1',
    'RUSTUP_TOOLCHAIN': '1.98.1',
    'LEAN_SYSROOT': str(lean),
    'LIBCLANG_PATH': '/usr/lib/x86_64-linux-gnu',
    'CFLAGS': '-std=gnu17',
}
env = dict(os.environ, **settings)
env['PATH'] = str(lean / 'bin') + ':' + env['PATH']
metadata = {
    'started': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_heads': {name: git(directory, 'rev-parse', 'HEAD').decode().strip()
                     for name, directory in [('ix', root), ('multi-stark', backend)]},
    'environment': settings,
    'extra_sources': before['extra_sources'],
    'commands': [],
}

def run(command):
    metadata['commands'].append(command)
    print('Running:', command, flush=True)
    with (output / 'build.log').open('a') as log:
        result = subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print((output / 'build.log').read_text()[-12000:], flush=True)
        result.check_returncode()

try:
    config.write_bytes(patched_config)
    run(['cargo', 'build', '--release', '-p', 'ix-ffi', '--features', 'parallel,cuda'])
    resolved_lock = lock.read_bytes()
    (output / 'Cargo.lock').write_bytes(resolved_lock)
    old_packages = [p for p in tomllib.loads(original_lock.decode())['package'] if p['name'] != 'multi-stark']
    new_packages = [p for p in tomllib.loads(resolved_lock.decode())['package'] if p['name'] != 'multi-stark']
    assert old_packages == new_packages, 'Unexpected dependency resolution change'
    run([str(lean / 'bin/lake'), 'build', 'ix'])
    assert source_state() == before, 'Sources changed during the build'
    fixed = output / 'ix-shared-execution'
    shutil.copy2(root / '.lake/build/bin/ix', fixed)
    shutil.copy2(root / '.lake/build/bin/ix.rsp', output / 'ix.rsp')
    metadata['fixed_sha256'] = digest(fixed)
    metadata['completed'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (output / 'build-source.py').write_text(Path(__file__).read_text())
    print('Built:', fixed, metadata['fixed_sha256'], flush=True)
finally:
    if config.read_bytes() == patched_config:
        config.write_bytes(original_config)
    else:
        print('Cargo config changed concurrently; original saved in build metadata', flush=True)
        (output / 'cargo-config.original.toml').write_bytes(original_config)
    lock.write_bytes(original_lock)
    (output / 'build.json').write_text(json.dumps(metadata, indent=2) + '\n')
