// Tiny stack VM, make.fun ISA v1 (kit ISA.md; kit vm.mjs is authoritative).
// One run answers every instance under MAKEFUN_INPUT_DIR, writing
// <id>/stdout.bin + <id>/exit.txt under MAKEFUN_OUTPUT_DIR. Deterministic:
// no clock, no network, no randomness, nothing outside the input dir.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const STEP = 1e6, OUT = 65536, SCAP = 256, CCAP = 64, MEM = 256, MIN = -2147483648;
// One dispatch table, built once: [immediate length, pops, pushes] per opcode,
// null for bytes no opcode names. The old isOp()/imm()/eff() trio ran three
// function calls per step and eff() allocated a fresh array on every instruction;
// one table lookup replaces all of it, with identical semantics.
const META: ReadonlyArray<readonly [number, number, number] | null> = (() => {
  const t: Array<readonly [number, number, number] | null> = new Array(256).fill(null);
  const set = (ops: number[], im: number, po: number, pu: number) => { for (const o of ops) t[o] = [im, po, pu]; };
  set([0, 52], 0, 0, 0);
  set([48, 51], 2, 0, 0);
  set([49, 50], 2, 1, 0);
  set([1], 1, 0, 1);
  set([2], 4, 0, 1);
  set([3, 80, 81, 83], 0, 1, 0);
  set([4], 0, 1, 2);
  set([5], 0, 2, 2);
  set([6], 0, 2, 3);
  set([7], 0, 3, 3);
  set([23, 27, 64], 0, 1, 1);
  set([65], 0, 2, 0);
  set([82], 0, 0, 1);
  set([16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34], 0, 2, 1);
  return t;
})();
function run(code, input) {
  const n = code.length, s = new Int32Array(SCAP), r = new Int32Array(CCAP), m = new Int32Array(MEM), b = new Uint8Array(OUT);
  let t = 0, rp = 0, w = 0, cur = 0, pc = 0, st = 0;
  const fin = (e) => ({ e, b: b.subarray(0, w) });
  for (;;) {
    if (st === STEP) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = code[pc];
    const meta = META[op];
    if (!meta) return fin(5);
    const im = meta[0];
    if (pc + im >= n) return fin(9);
    st++;
    const po = meta[1], pu = meta[2];
    if (t < po) return fin(2);
    if (t - po + pu > SCAP) return fin(3);
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0: return fin(0);
      case 1: s[t++] = (code[nx - 1] << 24) >> 24; break; // PUSH8 sign-extended
      case 2: s[t++] = code[nx - 4] | (code[nx - 3] << 8) | (code[nx - 2] << 16) | (code[nx - 1] << 24); break; // PUSH32
      case 3: t--; break;
      case 4: s[t] = s[t - 1]; t++; break; // DUP
      case 5: { const x = s[t - 1]; s[t - 1] = s[t - 2]; s[t - 2] = x; break; } // SWAP
      case 6: s[t] = s[t - 2]; t++; break; // OVER
      case 7: { const x = s[t - 3]; s[t - 3] = s[t - 2]; s[t - 2] = s[t - 1]; s[t - 1] = x; break; } // ROT
      case 23: s[t - 1] = (-s[t - 1]) | 0; break; // NEG wraps
      case 27: s[t - 1] = ~s[t - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const y = s[t - 1], x = s[t - 2];
        let v;
        switch (op) {
          case 16: v = (x + y) | 0; break; // ADD
          case 17: v = (x - y) | 0; break; // SUB
          case 18: v = Math.imul(x, y); break; // MUL low 32 bits
          case 19: if (!y) return fin(4); v = x === MIN && y === -1 ? x : (x / y) | 0; break; // DIV
          case 20: if (!y) return fin(4); v = y === -1 ? 0 : (x % y) | 0; break; // MOD
          case 21: if (!y) return fin(4); v = Math.floor((x >>> 0) / (y >>> 0)) | 0; break; // DIVU
          case 22: if (!y) return fin(4); v = ((x >>> 0) % (y >>> 0)) | 0; break; // MODU
          case 24: v = x & y; break;
          case 25: v = x | y; break;
          case 26: v = x ^ y; break;
          case 28: v = x << (y & 31); break; // SHL
          case 29: v = x >> (y & 31); break; // SHR
          case 30: v = (x >>> (y & 31)) | 0; break; // SHRU
          case 32: v = x === y ? 1 : 0; break; // EQ
          case 33: v = x < y ? 1 : 0; break; // LT signed
          default: v = (x >>> 0) < (y >>> 0) ? 1 : 0; // LTU unsigned
        }
        t -= 2; s[t++] = v; break;
      }
      case 48: case 49: case 50: {
        const rel = ((code[nx - 2] | (code[nx - 1] << 8)) << 16) >> 16;
        if (op === 48) pc = nx + rel;
        else { const v = s[--t]; if ((op === 49) === (v === 0)) pc = nx + rel; }
        break;
      }
      case 51: // CALL
        if (rp === CCAP) return fin(7);
        r[rp++] = nx; pc = code[nx - 2] | (code[nx - 1] << 8); break;
      case 52: // RET
        if (!rp) return fin(8);
        pc = r[--rp]; break;
      case 64: { // LOAD
        const a = s[t - 1];
        if (a < 0 || a >= MEM) return fin(6);
        s[t - 1] = m[a]; break;
      }
      case 65: { // STORE ( v addr -- )
        const a = s[t - 1], v = s[t - 2];
        if (a < 0 || a >= MEM) return fin(6);
        t -= 2; m[a] = v; break;
      }
      case 80: { // PRINT decimal ASCII
        const d = String(s[t - 1]);
        if (w + d.length > OUT) return fin(11);
        t--;
        for (let i = 0; i < d.length; i++) b[w++] = d.charCodeAt(i);
        break;
      }
      case 81: // PUTC one byte
        if (w + 1 > OUT) return fin(11);
        b[w++] = s[--t] & 255; break;
      case 82: // IN: next byte, -1 at EOF
        s[t++] = cur < input.length ? input[cur++] : -1; break;
      case 83: // EXIT low byte
        return fin(s[--t] & 255);
      default: return fin(5);
    }
  }
}
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const e of readdirSync(IN, { withFileTypes: true }).sort((a, z) => (a.name < z.name ? -1 : 1))) {
  if (!e.isDirectory()) continue;
  let code = 1, bytes = new Uint8Array(0);
  try {
    const o = run(readFileSync(join(IN, e.name, 'program.bin')), readFileSync(join(IN, e.name, 'input.bin')));
    code = o.e; bytes = o.b;
  } catch { code = 1; bytes = new Uint8Array(0); }
  mkdirSync(join(OUTD, e.name), { recursive: true });
  writeFileSync(join(OUTD, e.name, 'stdout.bin'), bytes);
  writeFileSync(join(OUTD, e.name, 'exit.txt'), code + '\n');
}
