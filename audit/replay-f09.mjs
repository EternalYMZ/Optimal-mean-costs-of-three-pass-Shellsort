import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createReadStream, closeSync, mkdtempSync, openSync, readFileSync, rmSync, rmdirSync, writeFileSync } from 'node:fs';
import { createInterface } from 'node:readline';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const audit = dirname(fileURLToPath(import.meta.url));
const repository = dirname(audit);
const manifest = JSON.parse(readFileSync(join(audit, 'f09-replays.json'), 'utf8'));
const lake = process.env.LAKE || 'lake';
const suffix = process.platform === 'win32' ? '.exe' : '';
const requested = process.argv.slice(2);
const groups = manifest.exports.filter(group => !requested.length || requested.includes(group.module));
if (!groups.length || requested.some(name => !groups.some(group => group.module === name))) {
  throw new Error('Choose module names from audit/f09-replays.json.');
}

function run(args, stdout = 'inherit') {
  const result = spawnSync(lake, args, { cwd: repository, windowsHide: true, stdio: ['ignore', stdout, 'inherit'] });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`lake ${args[0]} exited with status ${result.status}`);
}

// The final export includes the large integer proofs from all thirteen quadratures.
async function checkExportInterface(proof, roots) {
  const names = [''];
  const missing = new Set(roots);
  const lines = createInterface({ input: createReadStream(proof), crlfDelay: Infinity });
  for await (const line of lines) {
    if (line.startsWith('{"in":')) {
      const record = JSON.parse(line);
      const part = record.str ?? record.num;
      if (!part) throw new Error('Unsupported exported name');
      const prefix = names[part.pre];
      if (prefix === undefined) throw new Error('Missing exported name prefix');
      names[record.in] = (prefix ? prefix + '.' : '') + (part.str ?? part.i);
    } else if (line.startsWith('{"axiom":')) {
      const name = names[JSON.parse(line).axiom.name];
      if (!manifest.allowed_axioms.includes(name)) throw new Error('Unapproved axiom ' + name);
    } else if (line.startsWith('{"thm":')) {
      missing.delete(names[JSON.parse(line).thm.name]);
    }
  }
  if (missing.size) throw new Error('Missing exported theorems: ' + [...missing].join(', '));
}

for (const group of groups) {
  run(['build', group.module]);
  const dir = mkdtempSync(join(tmpdir(), 'shellsort-f09-'));
  try {
    const proof = join(dir, 'proof.ndjson');
    const statements = join(dir, 'theorems.txt');
    const config = join(dir, 'nanoda.json');
    const fd = openSync(proof, 'w');
    try {
      run(['env', 'leanexport' + suffix, group.module, '--', ...group.declarations], fd);
    } finally {
      closeSync(fd);
    }
    const sha = createHash('sha256');
    for await (const chunk of createReadStream(proof)) sha.update(chunk);
    const digest = sha.digest('hex');
    if (digest !== group.export_sha256) throw new Error('Export differs from the recorded SHA-256.');
    if (group.checker === 'leanchecker') {
      await checkExportInterface(proof, group.declarations);
      run(['env', process.env.LEANCHECKER || 'leanchecker' + suffix, '--from-export', proof]);
      console.log(group.module, digest);
      continue;
    }
    writeFileSync(statements, '');
    writeFileSync(config, JSON.stringify({
      export_file_path: proof, permitted_axioms: manifest.allowed_axioms,
      unpermitted_axiom_hard_error: true, unsafe_permit_all_axioms: false,
      nat_extension: true, string_extension: true, pp_declars: group.declarations,
      pp_output_path: statements, pp_options: { proofs: false }, print_success_message: true
    }));
    run(['env', 'nanoda_bin' + suffix, config]);
    const types = readFileSync(statements, 'utf8');
    for (const name of group.declarations) {
      if (!types.includes('theorem ' + name)) throw new Error('Missing checked theorem ' + name);
    }
    console.log(group.module, digest);
  } finally {
    for (const file of ['proof.ndjson', 'theorems.txt', 'nanoda.json']) {
      rmSync(join(dir, file), { force: true });
    }
    rmdirSync(dir);
  }
}
