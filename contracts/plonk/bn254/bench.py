#!/usr/bin/env python3
"""Verify the pinned Init proof with stock and adapted SP1 contracts on local Anvil."""

import argparse
import hashlib
import json
import re
import socket
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617
P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
CALL_GAS = 2_000_000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def word(value):
    return value.to_bytes(32, 'big')


def blob(value):
    return word(len(value)) + value + bytes((-len(value)) % 32)


class RpcError(Exception):
    def __init__(self, error):
        super().__init__(json.dumps(error))
        self.error = error


class Rpc:
    def __init__(self, url):
        self.url = url
        self.sequence = 0

    def __call__(self, method, params=None):
        self.sequence += 1
        body = json.dumps({'jsonrpc': '2.0', 'id': self.sequence,
                           'method': method, 'params': params or []}).encode()
        request = urllib.request.Request(self.url, body, {'Content-Type': 'application/json'})
        with urllib.request.urlopen(request, timeout=30) as response:
            result = json.load(response)
        if 'error' in result:
            raise RpcError(result['error'])
        return result['result']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tools', type=Path, required=True, help='directory containing solc, anvil and cast')
    parser.add_argument('--out', type=Path, required=True, help='new directory for compiler output and receipts')
    args = parser.parse_args()
    args.tools = args.tools.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    versions = {name: subprocess.check_output([str(args.tools / name), '--version'], text=True).strip()
                for name in ['solc', 'anvil', 'cast']}
    assert '0.8.37+' in versions['solc'] and '1.8.5' in versions['anvil'], versions
    fixture_path = ROOT / 'testdata/init.json'
    fixture, provenance = read(fixture_path), read(ROOT / 'provenance.json')
    assert sha(fixture_path.read_bytes()) == provenance['adaptation']['fixture_sha256']
    proof = bytes.fromhex(fixture['proof'][2:])
    digest = bytes.fromhex(fixture['claimDigest'][2:])
    claim = bytes.fromhex(fixture['claim'][2:])
    assert len(proof) == 864 and len(digest) == 32
    assert sha(proof) == provenance['adaptation']['proof_solidity_sha256']
    assert fixture['verifyingKeySHA256'] == provenance['adaptation']['verifying_key_sha256']
    for name, record in provenance['files'].items():
        directory = 'upstream' if name == 'ISP1Verifier.sol' else 'upstream/v6.1.0'
        assert sha((ROOT / directory / name).read_bytes()) == record['sha256'], name
    source = (ROOT / 'src/PlonkVerifier.sol').read_text()
    assert sha(source.encode()) == provenance['adaptation']['adapted_source_sha256']
    stock_source = (ROOT / 'upstream/v6.1.0/PlonkVerifier.sol').read_text()
    substitutions = provenance['adaptation']['changed_constants']
    pattern = r'(uint256 private constant )(VK_\w+)( = )([^;]+)(;)'
    adapted = re.sub(pattern, lambda m: m[1] + m[2] + m[3] + substitutions.get(m[2], {'ix': m[4]})['ix'] + m[5], stock_source)
    assert adapted == source, 'adaptation changed more than the pinned key constants'
    assert sha(source.replace('pragma solidity ^0.8.20;', 'pragma solidity ^0.8.0;').encode()) == provenance['adaptation']['generated_gnark_source_sha256']
    sources = {str(p.relative_to(ROOT)): {'content': p.read_text()}
               for p in [ROOT / 'src/PlonkVerifier.sol', ROOT / 'upstream/ISP1Verifier.sol',
                         ROOT / 'upstream/v6.1.0/PlonkVerifier.sol', ROOT / 'upstream/v6.1.0/SP1VerifierPlonk.sol']}
    sources['IxPlonkVerifier.sol'] = {'content': (ROOT.parent / 'src/IxPlonkVerifier.sol').read_text()}
    compiler = {'language': 'Solidity', 'sources': sources, 'settings': {
        'optimizer': {'enabled': True, 'runs': 200}, 'viaIR': True, 'evmVersion': 'prague',
        'outputSelection': {'*': {'*': ['abi', 'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    write(out / 'compiler-input.json', compiler)
    print('Compiling stock SP1, adapted SP1 and ix adapter contracts.', flush=True)
    compiled = subprocess.run([str(args.tools / 'solc'), '--standard-json'],
                              input=json.dumps(compiler), capture_output=True, text=True, check=True)
    (out / 'compiler-output.json').write_text(compiled.stdout)
    output = json.loads(compiled.stdout)
    errors = [e for e in output.get('errors', []) if e['severity'] == 'error']
    assert not errors, errors

    def selector(signature):
        return bytes.fromhex(subprocess.check_output([str(args.tools / 'cast'), 'sig', signature], text=True).strip()[2:])

    verify_selector = selector('Verify(bytes,uint256[])')
    adapter_selector = selector('verify(bytes,bytes32)')
    facade_selector = selector('verifyProof(bytes32,bytes,bytes)')
    inputs = [int.from_bytes(digest[:16], 'little'), int.from_bytes(digest[16:], 'little')]

    def raw_call(payload=proof, public=inputs):
        encoded = blob(payload)
        return verify_selector + word(64) + word(64 + len(encoded)) + encoded + word(len(public)) + b''.join(word(x) for x in public)

    def adapter_call(payload=proof, expected=digest):
        return adapter_selector + word(64) + expected + blob(payload)

    report = {'format': 'ix-bn254-plonk-anvil-v1', 'toolchain': versions,
              'compiler_settings': compiler['settings'], 'execution_hardfork': 'osaka',
              'fixture_sha256': sha(fixture_path.read_bytes()), 'verifying_key_sha256': fixture['verifyingKeySHA256'],
              'claim_digest': fixture['claimDigest'], 'sp1_commit': provenance['commit'],
              'changed_vk_constants': list(substitutions), 'verifier_algorithm_unchanged': True,
              'proof_solidity_bytes': len(proof), 'native_proof_bytes': len(bytes.fromhex(fixture['nativeProof'][2:])),
              'envelope_bytes': len(bytes.fromhex(fixture['envelope'][2:])),
              'deployments': {}, 'checks': {}, 'transactions': {}, 'call_gas_limit': CALL_GAS}
    with socket.socket() as listener:
        listener.bind(('127.0.0.1', 0))
        port = listener.getsockname()[1]
    rpc = Rpc(f'http://127.0.0.1:{port}')
    anvil_log = (out / 'anvil.log').open('w')
    process = subprocess.Popen([str(args.tools / 'anvil'), '--host', '127.0.0.1', '--port', str(port),
                                '--hardfork', 'osaka', '--chain-id', '31337', '--gas-limit', '30000000',
                                '--steps-tracing'], stdout=anvil_log, stderr=subprocess.STDOUT)
    try:
        for _ in range(100):
            if process.poll() is not None:
                raise RuntimeError('Anvil exited before becoming ready')
            try:
                if rpc('eth_chainId') == hex(31337):
                    break
            except (OSError, urllib.error.URLError):
                time.sleep(0.1)
        else:
            raise RuntimeError('Anvil did not become ready')
        report['client_version'] = rpc('web3_clientVersion')
        account = rpc('eth_accounts')[0]

        def transaction(name, data, address=None, gas=CALL_GAS):
            tx = {'from': account, 'data': '0x' + data.hex(), 'gas': hex(gas)}
            if address is not None:
                tx['to'] = address
            txid = rpc('eth_sendTransaction', [tx])
            for _ in range(100):
                receipt = rpc('eth_getTransactionReceipt', [txid])
                if receipt is not None:
                    break
                time.sleep(0.05)
            else:
                raise RuntimeError('missing transaction receipt')
            assert int(receipt['status'], 16) == 1, (name, receipt)
            write(out / f'{name}-receipt.json', receipt)
            result = {'transaction_hash': txid, 'gas_used': int(receipt['gasUsed'], 16), 'calldata_bytes': len(data)}
            if address is not None:
                zeros = data.count(0)
                intrinsic = 21000 + 4 * zeros + 16 * (len(data) - zeros)
                floor = 21000 + 10 * (zeros + 4 * (len(data) - zeros))
                assert result['gas_used'] > floor
                result.update(intrinsic_calldata_gas=intrinsic, eip7623_floor_gas=floor,
                              execution_gas=result['gas_used'] - intrinsic)
                trace = rpc('debug_traceTransaction', [txid, {'tracer': 'callTracer'}])
                assert trace.get('output') == '0x' + word(1).hex(), (name, trace)
                write(out / f'{name}-trace.json', trace)
                precompiles = []
                def collect(call):
                    address_value = int(call.get('to', '0x0'), 16)
                    if 1 <= address_value <= 17:
                        precompiles.append({'address': address_value, 'gas_used': int(call['gasUsed'], 16),
                                            'input_bytes': len(bytes.fromhex(call.get('input', '0x')[2:]))})
                    for child in call.get('calls', []):
                        collect(child)
                collect(trace)
                result['precompile_calls'] = precompiles
                report['transactions'][name] = result
            return receipt, result

        def deploy(name, file, contract, arguments=b''):
            artifact = output['contracts'][file][contract]['evm']
            init = bytes.fromhex(artifact['bytecode']['object']) + arguments
            runtime = bytes.fromhex(artifact['deployedBytecode']['object'])
            assert len(init) <= 49152 and len(runtime) <= 24576, (name, len(init), len(runtime))
            receipt, result = transaction('deploy-' + name, init, gas=10_000_000)
            address = receipt['contractAddress']
            deployed = bytes.fromhex(rpc('eth_getCode', [address, 'latest'])[2:])
            assert len(deployed) == len(runtime)
            result.update(address=address, initcode_bytes=len(init), runtime_bytes=len(deployed), runtime_sha256=sha(deployed))
            report['deployments'][name] = result
            return address

        stock = deploy('stock-sp1', 'upstream/v6.1.0/PlonkVerifier.sol', 'PlonkVerifier')
        facade = deploy('stock-sp1-facade', 'upstream/v6.1.0/SP1VerifierPlonk.sol', 'SP1Verifier')
        adapted_address = deploy('adapted-sp1', 'src/PlonkVerifier.sol', 'PlonkVerifier')
        adapter = deploy('ix-adapter', 'IxPlonkVerifier.sol', 'IxPlonkVerifier', word(int(adapted_address, 16)))

        def evaluate(name, address, data, expected, returns_bool=True):
            try:
                result = rpc('eth_call', [{'to': address, 'from': account, 'data': '0x' + data.hex(), 'gas': hex(CALL_GAS)}, 'latest'])
                if returns_bool:
                    assert result in ['0x' + word(0).hex(), '0x' + word(1).hex()], (name, result)
                    accepted = result == '0x' + word(1).hex()
                else:
                    assert result == '0x', (name, result)
                    accepted = True
                record = {'accepted': accepted, 'result': result}
            except RpcError as error:
                message = json.dumps(error.error).lower()
                assert 'revert' in message, (name, error.error)
                accepted = False
                record = {'accepted': False, 'reverted': True, 'error': error.error}
            assert accepted == expected, (name, record)
            report['checks'][name] = record

        evaluate('stock-rejects-two-ix-inputs', stock, raw_call(), False)
        evaluate('stock-rejects-proof-with-five-inputs', stock, raw_call(public=inputs + [0, 0, 0]), False)
        verifier_hash = bytes.fromhex(rpc('eth_call', [{'to': facade, 'data': '0x' + selector('VERIFIER_HASH()').hex()}, 'latest'])[2:])
        vk_root = bytes.fromhex(rpc('eth_call', [{'to': facade, 'data': '0x' + selector('VK_ROOT()').hex()}, 'latest'])[2:])
        framed = verifier_hash[:4] + word(0) + vk_root + word(0) + proof
        public_values = blob(claim)
        framed_call = facade_selector + word(1) + word(96) + word(96 + len(public_values)) + public_values + blob(framed)
        evaluate('stock-facade-rejects-correctly-framed-ix-proof', facade, framed_call, False, returns_bool=False)
        assert report['checks']['stock-facade-rejects-correctly-framed-ix-proof']['error']['data'] == '0x' + selector('InvalidProof()').hex()
        evaluate('adapted-sp1-accepts-init', adapted_address, raw_call(), True)
        evaluate('ix-adapter-accepts-init', adapter, adapter_call(), True)
        transaction('adapted-sp1-verify', raw_call(), adapted_address)
        transaction('ix-adapter-verify', adapter_call(), adapter)
        print('Actual Init proof accepted by adapted SP1 verifier and ix adapter.', flush=True)

        for index in [0, 15, 16, 31]:
            wrong = bytearray(digest)
            wrong[index] ^= 1
            evaluate(f'changed-claim-byte-{index}', adapter, adapter_call(expected=bytes(wrong)), False)
        for name, public in [('swapped-inputs', inputs[::-1]), ('missing-input', inputs[:1]),
                              ('extra-input', inputs + [0]), ('noncanonical-input', [R, inputs[1]])]:
            evaluate(name, adapted_address, raw_call(public=public), False)
        for name, payload in [('empty-proof', b''), ('truncated-proof', proof[:-1]), ('trailing-proof', proof + b'\x00'),
                              ('native-format', bytes.fromhex(fixture['nativeProof'][2:])),
                              ('ix-envelope-format', bytes.fromhex(fixture['envelope'][2:]))]:
            evaluate(name, adapter, adapter_call(payload=payload), False)
        for index in range(len(proof) // 32):
            wrong = bytearray(proof)
            wrong[32 * index + 31] ^= 1
            evaluate(f'changed-proof-word-{index}', adapter, adapter_call(payload=bytes(wrong)), False)
        for name, offset, modulus in [('noncanonical-point', 0, P), ('noncanonical-scalar', 0x180, R)]:
            wrong = bytearray(proof)
            wrong[offset:offset+32] = word(modulus)
            evaluate(name, adapter, adapter_call(payload=bytes(wrong)), False)
        report['all_checks_passed'] = True
        report['acceptance_scope'] = 'Actual Init proof, independently fixed expected claim digest and pinned circuit verification key; isolated local Anvil only.'
        write(out / 'report.json', report)
        print(json.dumps({'transactions': {k: {field: value for field, value in v.items() if field != 'precompile_calls'} for k, v in report['transactions'].items()},
                          'deployments': report['deployments'], 'checks_passed': len(report['checks'])}, indent=2), flush=True)
    finally:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=5)
        assert process.poll() is not None
        anvil_log.close()


if __name__ == '__main__':
    main()
