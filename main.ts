// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// Every rule follows the kit's reference VM (generator/subject/vm.mjs), which
// is the rule where ISA.md is ambiguous: 32-bit wrapping ints, a 256-value
// stack, a 64-deep call stack, 256 words of memory, ten traps with their own
// exit codes, and the 1,000,000-step and 65,536-byte output limits.
import { mkdirSync as mkdir, readdirSync as ls, readFileSync as read, writeFileSync as write } from 'node:fs';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function run(p, inp) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (c) => ({ out: out.slice(0, ol), code: c });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = p[pc];
    // Known opcodes: 0x00-0x07, 0x10-0x22, 0x30-0x34, 0x40-0x41, 0x50-0x53.
    if (op > 7 && (op < 16 || op > 34) && (op < 48 || op > 52) && op !== 64 && op !== 65 && (op < 80 || op > 83)) return done(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    const pops = op === 7 ? 3 : op === 5 || op === 6 || op === 65 || (op >= 16 && op <= 34 && op !== 23 && op !== 27) ? 2
      : op === 3 || op === 4 || op === 23 || op === 27 || op === 49 || op === 50 || op === 64 || op === 80 || op === 81 || op === 83 ? 1 : 0;
    const push = op === 4 || op === 5 ? 2 : op === 6 || op === 7 ? 3
      : op === 1 || op === 2 || op === 82 || (op >= 16 && op <= 34) || op === 64 ? 1 : 0;
    if (pc + imm >= p.length) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + push > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00:
        return done(0);
      case 0x01:
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const v = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = v;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = (-D[sp - 1]) | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        C[cp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return done(D[--sp] & 255);
      default: {
        // Binary operators 0x10-0x16, 0x18-0x1a, 0x1c-0x22 (NEG/NOT handled above).
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // 0x22 LTU
        sp -= 2;
        D[sp++] = r;
        break;
      }
    }
  }
}

for (const id of ls(I).sort()) {
  const r = run(read(I + '/' + id + '/program.bin'), read(I + '/' + id + '/input.bin'));
  mkdir(O + '/' + id, { recursive: true });
  write(O + '/' + id + '/stdout.bin', r.out);
  write(O + '/' + id + '/exit.txt', r.code + '\n');
}
