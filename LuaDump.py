#!/usr/bin/env python3
"""
LuauDump — Luau Bytecode Decompiler
Supports Luau bytecode versions 3-9 (Roblox Luau)
Usage:
  python luaudump.py <file>            # decompile
  python luaudump.py <file> --dis      # disassemble only
  python luaudump.py <file> --both     # both modes
"""

import base64, struct, sys, math, re, os
from dataclasses import dataclass, field
from typing import List, Optional, Any, Dict, Set, Tuple

# ─── Opcode table ─────────────────────────────────────────────────────────────

OP_NAMES = [
    'NOP','BREAK','LOADNIL','LOADB','LOADN','LOADK','MOVE','GETUPVAL','SETUPVAL',
    'CLOSEUPVALS','GETIMPORT','GETTABLE','SETTABLE','GETTABLEKS','SETTABLEKS',
    'GETTABLEN','SETTABLEN','NEWCLOSURE','NAMECALL','CALL','RETURN','JUMP',
    'JUMPBACK','JUMPIF','JUMPIFNOT','JUMPIFEQ','JUMPIFLE','JUMPIFLT',
    'JUMPIFNOTEQ','JUMPIFNOTLE','JUMPIFNOTLT','ADD','SUB','MUL','DIV','MOD',
    'POW','ADDK','SUBK','MULK','DIVK','MODK','POWK','AND','OR','ANDK','ORK',
    'CONCAT','NOT','MINUS','LENGTH','NEWTABLE','DUPTABLE','SETLIST','FORNPREP',
    'FORNLOOP','FORGLOOP','FORGPREP_INEXT','FORGLOOP_INEXT','FORGPREP_NEXT',
    'FORGLOOP_NEXT','GETVARARGS','DUPCLOSURE','PREPVARARGS','LOADKX','JUMPX',
    'FASTCALL','COVERAGE','CAPTURE','SUBRK','DIVRK','FASTCALL1','FASTCALL2',
    'FASTCALL2K','FORGPREP','JUMPXEQKNIL','JUMPXEQKB','JUMPXEQKN','JUMPXEQKS',
    'IDIV','IDIVK',
]
OP = {n: i for i, n in enumerate(OP_NAMES)}

AUX_OPS: Set[int] = {
    OP['GETIMPORT'], OP['GETTABLEKS'], OP['SETTABLEKS'], OP['NAMECALL'],
    OP['SETLIST'],   OP['LOADKX'],    OP['FASTCALL2'],  OP['FASTCALL2K'],
    OP['JUMPXEQKNIL'], OP['JUMPXEQKB'], OP['JUMPXEQKN'], OP['JUMPXEQKS'],
    OP['JUMPIFEQ'], OP['JUMPIFLE'], OP['JUMPIFLT'],
    OP['JUMPIFNOTEQ'], OP['JUMPIFNOTLE'], OP['JUMPIFNOTLT'],
}

BINOP_SYM = {
    OP['ADD']:'+', OP['SUB']:'-', OP['MUL']:'*', OP['DIV']:'/',
    OP['MOD']:'%', OP['POW']:'^', OP['IDIV']:'//', OP['CONCAT']:'..',
    OP['AND']:'and', OP['OR']:'or',
    OP['ADDK']:'+', OP['SUBK']:'-', OP['MULK']:'*', OP['DIVK']:'/',
    OP['MODK']:'%', OP['POWK']:'^', OP['IDIVK']:'//',
    OP['ANDK']:'and', OP['ORK']:'or',
    OP['SUBRK']:'-', OP['DIVRK']:'/',
}
CMP_SYM = {
    OP['JUMPIFEQ']:'==', OP['JUMPIFLE']:'<=', OP['JUMPIFLT']:'<',
    OP['JUMPIFNOTEQ']:'~=', OP['JUMPIFNOTLE']:'>', OP['JUMPIFNOTLT']:'>=',
}
JUMP_OPS = {OP['JUMP'], OP['JUMPBACK'], OP['JUMPX']}
FORN_LOOP = {OP['FORNLOOP']}
FORG_LOOP = {OP['FORGLOOP'], OP['FORGLOOP_INEXT'], OP['FORGLOOP_NEXT']}
FORG_PREP = {OP['FORGPREP'], OP['FORGPREP_INEXT'], OP['FORGPREP_NEXT']}

# ─── Data classes ─────────────────────────────────────────────────────────────

@dataclass
class Instr:
    op: int; a: int; b: int; c: int; aux: int = 0; raw_pc: int = 0
    @property
    def d(self): return (self.b << 8) | self.c
    @property
    def sd(self):
        d = self.d
        return d - 0x10000 if d >= 0x8000 else d
    @property
    def name(self): return OP_NAMES[self.op] if 0 <= self.op < len(OP_NAMES) else f'OP_{self.op}'

@dataclass
class LocalVar:
    name: str; reg: int; start_pc: int; end_pc: int

@dataclass
class Const:
    ctype: int; value: Any = None

@dataclass
class Proto:
    max_stack: int = 0; num_params: int = 0; num_upvalues: int = 0
    is_vararg: bool = False; flags: int = 0
    code: List[Instr] = field(default_factory=list)
    consts: List[Const] = field(default_factory=list)
    upval_descs: List[Tuple] = field(default_factory=list)
    child_protos: List[int] = field(default_factory=list)
    line_defined: int = 0; debug_name: str = ''
    locals: List[LocalVar] = field(default_factory=list)
    upval_names: List[str] = field(default_factory=list)
    line_info: List[int] = field(default_factory=list)
    # raw-pc → code-list index mapping (built after parse)
    raw_pc_map: Dict[int,int] = field(default_factory=dict)

# ─── Binary reader ────────────────────────────────────────────────────────────

class Reader:
    def __init__(self, data: bytes): self.data = data; self.pos = 0
    def byte(self):
        b = self.data[self.pos]; self.pos += 1; return b
    def u32(self):
        v = struct.unpack_from('<I', self.data, self.pos)[0]; self.pos += 4; return v
    def f64(self):
        v = struct.unpack_from('<d', self.data, self.pos)[0]; self.pos += 8; return v
    def varint(self):
        r = s = 0
        while True:
            b = self.byte(); r |= (b & 0x7f) << s; s += 7
            if not (b & 0x80): break
        return r
    def read(self, n): b = self.data[self.pos:self.pos+n]; self.pos += n; return b

# ─── Parser ───────────────────────────────────────────────────────────────────

class Parser:
    def __init__(self, data: bytes):
        self.r = Reader(data); self.strtab: List[str] = ['']
        self.all_protos: List[Proto] = []; self.version = 0; self.types_version = 0

    def parse(self) -> Proto:
        r = self.r; v = r.byte(); self.version = v
        if v == 0: raise ValueError("Bytecode error (version=0)")
        if not (3 <= v <= 9): raise ValueError(f"Unsupported version {v}")
        if v >= 4: self.types_version = r.byte()

        # String table
        for _ in range(r.varint()):
            n = r.varint(); self.strtab.append(r.read(n).decode('utf-8','replace'))

        # Proto table
        for _ in range(r.varint()): self.all_protos.append(self._proto())

        main = r.varint()
        return self.all_protos[main]

    def _proto(self) -> Proto:
        r = self.r; p = Proto()
        p.max_stack = r.byte(); p.num_params = r.byte()
        p.num_upvalues = r.byte(); p.is_vararg = bool(r.byte())
        if self.version >= 4:
            p.flags = r.byte()
            if self.types_version > 0:
                r.read(r.varint())  # skip type annotations

        # Instructions
        n_code = r.varint()
        raw = [r.u32() for _ in range(n_code)]
        ri = 0
        while ri < n_code:
            w = raw[ri]; op = w&0xFF; a=(w>>8)&0xFF; b=(w>>16)&0xFF; c=(w>>24)&0xFF
            ins = Instr(op=op, a=a, b=b, c=c, raw_pc=ri); ri += 1
            if op in AUX_OPS and ri < n_code: ins.aux = raw[ri]; ri += 1
            p.code.append(ins)
        # Build raw-pc → code-idx map
        for ci, ins in enumerate(p.code): p.raw_pc_map[ins.raw_pc] = ci

        # Constants
        for _ in range(r.varint()):
            ct = r.byte()
            if ct == 0: p.consts.append(Const(0))
            elif ct == 1: p.consts.append(Const(1, bool(r.byte())))
            elif ct == 2: p.consts.append(Const(2, r.f64()))
            elif ct == 3:
                i = r.varint(); p.consts.append(Const(3, self.strtab[i] if i < len(self.strtab) else ''))
            elif ct == 4: p.consts.append(Const(4, r.u32()))
            elif ct == 5: cnt=r.varint(); p.consts.append(Const(5,[r.varint() for _ in range(cnt)]))
            elif ct == 6: p.consts.append(Const(6, r.varint()))
            else: raise ValueError(f"Unknown constant type {ct}")

        # Upvalue descriptors
        for _ in range(r.varint()):
            ins_ = r.byte(); idx = r.byte()
            kind = r.byte() if self.version >= 4 else 0
            p.upval_descs.append((ins_, idx, kind))

        # Child protos
        for _ in range(r.varint()): p.child_protos.append(r.varint())

        # Debug name
        p.line_defined = r.varint()
        di = r.varint(); p.debug_name = self.strtab[di] if di < len(self.strtab) else ''

        # Line info
        if r.byte():
            gap_log2 = r.byte()
            n_abs = ((n_code - 1) >> gap_log2) + 1 if n_code else 0
            spans = [r.byte() for _ in range(n_code)]
            abs_l = [r.u32() for _ in range(n_abs)]
            p.line_info = [abs_l[ii >> gap_log2] + spans[ii] for ii in range(n_code)]

        # Debug info (locals & upvalue names)
        if r.byte():
            for _ in range(r.varint()):
                ni = r.varint(); nm = self.strtab[ni] if ni < len(self.strtab) else '?'
                sp = r.varint(); ep = r.varint(); reg = r.byte()
                p.locals.append(LocalVar(nm, reg, sp, ep))
            for _ in range(p.num_upvalues):
                ni = r.varint(); p.upval_names.append(self.strtab[ni] if ni < len(self.strtab) else '?')

        return p

# ─── Helpers ──────────────────────────────────────────────────────────────────

def _is_ident(s: str) -> bool:
    LUA_KEYWORDS = {'and','break','do','else','elseif','end','false','for',
                    'function','goto','if','in','local','nil','not','or',
                    'repeat','return','then','true','until','while'}
    if not s or not (s[0].isalpha() or s[0]=='_'): return False
    if not all(c.isalnum() or c=='_' for c in s): return False
    return s not in LUA_KEYWORDS

def _fmt_num(v: float) -> str:
    if math.isnan(v): return '0/0'
    if v == math.inf: return 'math.huge'
    if v == -math.inf: return '-math.huge'
    if v == int(v) and abs(v) < 1e15: return str(int(v))
    return repr(v)

def _decode_import(val: int, consts: List[Const], strtab: List[str]) -> str:
    count = (val >> 30) + 1
    shifts = [20, 10, 0]
    parts = []
    for i in range(count):
        idx = (val >> shifts[i]) & 0x3FF
        # idx is 1-based into the string table
        if 0 < idx < len(strtab): parts.append(strtab[idx])
        else: parts.append(f'?{idx}')
    return '.'.join(parts)

def _const_repr(k: Const, consts: List[Const], strtab: List[str]) -> str:
    if k.ctype == 0: return 'nil'
    if k.ctype == 1: return 'true' if k.value else 'false'
    if k.ctype == 2: return _fmt_num(k.value)
    if k.ctype == 3: return repr(k.value)
    if k.ctype == 4: return _decode_import(k.value, consts, strtab)
    if k.ctype == 5: return '{}'
    if k.ctype == 6: return '<closure>'
    return '?'

def _get_k(proto: Proto, idx: int, strtab: List[str]) -> str:
    if 0 <= idx < len(proto.consts):
        return _const_repr(proto.consts[idx], proto.consts, strtab)
    return f'?k{idx}'

def _get_str_k(proto: Proto, idx: int) -> str:
    if 0 <= idx < len(proto.consts) and proto.consts[idx].ctype == 3:
        return proto.consts[idx].value
    return f'?k{idx}'

def _local_at(proto: Proto, reg: int, raw_pc: int) -> Optional[str]:
    for lv in proto.locals:
        if lv.reg == reg and lv.start_pc <= raw_pc < lv.end_pc:
            return lv.name
    return None

# ─── Disassembler ─────────────────────────────────────────────────────────────

def disassemble(proto: Proto, all_protos: List[Proto], strtab: List[str],
                out: List[str], depth: int = 0):
    pad = '  ' * depth
    name = proto.debug_name or '(main)'
    out.append(f'{pad}; ── function {name!r} @ line {proto.line_defined} ──────────')
    out.append(f'{pad}; params={proto.num_params} upvals={proto.num_upvalues} '
               f'maxstack={proto.max_stack} vararg={int(proto.is_vararg)}')
    if proto.upval_names:
        out.append(f'{pad}; upvalues: {", ".join(proto.upval_names)}')
    if proto.locals:
        locs = ', '.join(f'{lv.name}@R{lv.reg}[{lv.start_pc}..{lv.end_pc})' for lv in proto.locals)
        out.append(f'{pad}; locals:   {locs}')

    for ins in proto.code:
        op = ins.op
        line = proto.line_info[ins.raw_pc] if ins.raw_pc < len(proto.line_info) else '?'
        prefix = f'{pad}  [{ins.raw_pc:4d}] L{line:<5} {ins.name:<18}'

        def uvn(i): return proto.upval_names[i] if i < len(proto.upval_names) else f'UV{i}'
        def kv(i): return _get_k(proto, i, strtab)
        def ks(i): return _get_str_k(proto, i)

        if op == OP['LOADNIL']:   s = f'R{ins.a}..R{ins.a+ins.b}'
        elif op == OP['LOADB']:   s = f'R{ins.a} = {bool(ins.b)}  skip={ins.c}'
        elif op == OP['LOADN']:   s = f'R{ins.a} = {ins.sd}'
        elif op == OP['LOADK']:   s = f'R{ins.a} = K{ins.d} ({kv(ins.d)})'
        elif op == OP['LOADKX']:  s = f'R{ins.a} = K{ins.aux} ({kv(ins.aux)})'
        elif op == OP['MOVE']:    s = f'R{ins.a} = R{ins.b}'
        elif op == OP['GETUPVAL']:s = f'R{ins.a} = {uvn(ins.b)}'
        elif op == OP['SETUPVAL']:s = f'{uvn(ins.b)} = R{ins.a}'
        elif op == OP['GETIMPORT']:
            kc = proto.consts[ins.aux] if ins.aux < len(proto.consts) else None
            nm = _decode_import(kc.value, proto.consts, strtab) if kc and kc.ctype==4 else f'K{ins.aux}'
            s = f'R{ins.a} = {nm}'
        elif op == OP['GETTABLE']:   s = f'R{ins.a} = R{ins.b}[R{ins.c}]'
        elif op == OP['SETTABLE']:   s = f'R{ins.b}[R{ins.c}] = R{ins.a}'
        elif op == OP['GETTABLEKS']: s = f'R{ins.a} = R{ins.b}[{repr(ks(ins.aux))}]'
        elif op == OP['SETTABLEKS']: s = f'R{ins.b}[{repr(ks(ins.aux))}] = R{ins.a}'
        elif op == OP['GETTABLEN']:  s = f'R{ins.a} = R{ins.b}[{ins.c+1}]'
        elif op == OP['SETTABLEN']:  s = f'R{ins.b}[{ins.c+1}] = R{ins.a}'
        elif op in (OP['NEWCLOSURE'],OP['DUPCLOSURE']):
            ci = proto.child_protos[ins.d] if ins.d < len(proto.child_protos) else '?'
            s = f'R{ins.a} = Proto[{ins.d}] → all_protos[{ci}]'
        elif op == OP['NAMECALL']:   s = f'R{ins.a},R{ins.a+1} = R{ins.b}:{repr(ks(ins.aux))}'
        elif op == OP['CALL']:       s = f'R{ins.a}({ins.b-1} args) → {ins.c-1} results'
        elif op == OP['RETURN']:     s = f'R{ins.a}..{ins.b-1} values'
        elif op in JUMP_OPS:
            t = ins.raw_pc + 1 + ins.sd; s = f'→ @{t}'
        elif op in (OP['JUMPIF'],OP['JUMPIFNOT']):
            t = ins.raw_pc + 1 + ins.sd; neg = 'not ' if op==OP['JUMPIFNOT'] else ''
            s = f'if {neg}R{ins.a} → @{t}'
        elif op in CMP_SYM:
            t = ins.raw_pc + 1 + ins.sd
            s = f'if R{ins.a} {CMP_SYM[op]} R{ins.aux} → @{t}'
        elif op in (OP['JUMPXEQKNIL'],OP['JUMPXEQKB'],OP['JUMPXEQKN'],OP['JUMPXEQKS']):
            flip = bool(ins.aux >> 31); kid = ins.aux & 0x7FFFFFFF
            rhs = {OP['JUMPXEQKNIL']:'nil', OP['JUMPXEQKB']:str(bool(kid)),
                   OP['JUMPXEQKN']:kv(kid), OP['JUMPXEQKS']:repr(ks(kid))}[op]
            cmp = '~=' if flip else '=='
            t = ins.raw_pc + 1 + ins.sd; s = f'if R{ins.a} {cmp} {rhs} → @{t}'
        elif op in BINOP_SYM:
            sym = BINOP_SYM[op]
            if op in {OP['ADDK'],OP['SUBK'],OP['MULK'],OP['DIVK'],OP['MODK'],OP['POWK'],OP['IDIVK'],OP['ANDK'],OP['ORK']}:
                s = f'R{ins.a} = R{ins.b} {sym} K{ins.c} ({kv(ins.c)})'
            elif op == OP['SUBRK']: s = f'R{ins.a} = K{ins.b} ({kv(ins.b)}) - R{ins.c}'
            elif op == OP['DIVRK']: s = f'R{ins.a} = K{ins.b} ({kv(ins.b)}) / R{ins.c}'
            elif op == OP['CONCAT']:s = f'R{ins.a} = R{ins.b}..R{ins.c}'
            else: s = f'R{ins.a} = R{ins.b} {sym} R{ins.c}'
        elif op == OP['NOT']:    s = f'R{ins.a} = not R{ins.b}'
        elif op == OP['MINUS']:  s = f'R{ins.a} = -R{ins.b}'
        elif op == OP['LENGTH']: s = f'R{ins.a} = #R{ins.b}'
        elif op == OP['NEWTABLE']:s = f'R{ins.a} = {{}} (arr={ins.b} hash={ins.c})'
        elif op == OP['DUPTABLE']:s = f'R{ins.a} = dup K{ins.d}'
        elif op == OP['SETLIST']: s = f'R{ins.a}[{ins.aux}..] = R{ins.b}..R{ins.b+ins.c-2}'
        elif op == OP['FORNPREP']:t=ins.raw_pc+1+ins.sd; s=f'R{ins.a} → loop @{t}'
        elif op == OP['FORNLOOP']:t=ins.raw_pc+1+ins.sd; s=f'R{ins.a} step → @{t}'
        elif op in FORG_PREP:    t=ins.raw_pc+1+ins.sd; s=f'R{ins.a} → @{t} ({ins.b} vars)'
        elif op in FORG_LOOP:    t=ins.raw_pc+1+ins.sd; s=f'R{ins.a} iter → @{t} ({ins.b} vars)'
        elif op == OP['GETVARARGS']:s = f'R{ins.a}..{ins.b-1} = ...'
        elif op == OP['CAPTURE']:
            kinds = ['val','ref','upval']
            s = f'{kinds[ins.a] if ins.a<3 else ins.a}(R{ins.b})'
        elif op == OP['FASTCALL']:  s = f'builtin={ins.a} skip={ins.c}'
        elif op == OP['FASTCALL1']: s = f'builtin={ins.a} R{ins.b} skip={ins.c}'
        elif op in {OP['FASTCALL2'],OP['FASTCALL2K']}: s = f'builtin={ins.a} R{ins.b},R{ins.aux}'
        elif op == OP['PREPVARARGS']: s = f'{ins.a} fixed params'
        elif op == OP['COVERAGE']: s = ''
        else: s = f'A={ins.a} B={ins.b} C={ins.c} AUX={ins.aux}'

        out.append(prefix + s)

    out.append(f'{pad}; ── end {name!r} ──')
    out.append('')

    for ci in proto.child_protos:
        if ci < len(all_protos):
            disassemble(all_protos[ci], all_protos, strtab, out, depth+1)

# ─── Decompiler ───────────────────────────────────────────────────────────────

class Decompiler:
    def __init__(self, all_protos: List[Proto], strtab: List[str]):
        self.all_protos = all_protos
        self.strtab = strtab

    def run(self, main: Proto) -> str:
        lines = self._emit_proto_body(main, is_main=True, depth=0)
        return '\n'.join(lines)

    # ── Expression & name helpers ──────────────────────────────────────────────

    def _kv(self, proto: Proto, idx: int) -> str:
        return _get_k(proto, idx, self.strtab)

    def _ks(self, proto: Proto, idx: int) -> str:
        return _get_str_k(proto, idx)

    def _uv(self, proto: Proto, idx: int) -> str:
        return proto.upval_names[idx] if idx < len(proto.upval_names) else f'upv{idx}'

    def _params(self, proto: Proto) -> str:
        ps = []
        for i in range(proto.num_params):
            nm = _local_at(proto, i, 0) or f'p{i}'
            ps.append(nm)
        if proto.is_vararg: ps.append('...')
        return ', '.join(ps)

    # ── Core emission ──────────────────────────────────────────────────────────

    def _emit_proto_body(self, proto: Proto, is_main: bool, depth: int) -> List[str]:
        """
        Emit Lua source for one function prototype.
        Returns list of lines (already indented by `depth`).
        """
        lines: List[str] = []
        tab = '\t' * depth

        if not is_main:
            lines.append(f'function({self._params(proto)})')

        body = self._emit_body(proto, depth + (0 if is_main else 1))
        lines.extend(body)

        if not is_main:
            lines.append(f'{tab}end')

        return lines

    def _emit_inline_func(self, proto: Proto, depth: int) -> str:
        """Return a single-line function expression if short, else multiline."""
        ps = self._params(proto)
        body = self._emit_body(proto, depth + 1)
        # Filter blank/comment lines for length check
        real = [l for l in body if l.strip() and not l.strip().startswith('--')]
        if len(real) <= 2:
            inner = ' '.join(l.strip() for l in real)
            return f'function({ps}) {inner} end'
        # Multi-line: return sentinel to caller
        return None  # caller will handle multi-line

    def _emit_body(self, proto: Proto, depth: int) -> List[str]:
        """
        Emit the body of a proto (instructions → Lua statements).
        Handles for-loops, while-loops, if/elseif/else, and linear code.
        """
        lines: List[str] = []
        tab = '\t' * depth
        code = proto.code

        if not code:
            return lines

        # Build set of raw-pcs that are AUX words (skip in iteration)
        is_aux: Set[int] = set()
        for ins in code:
            if ins.op in AUX_OPS:
                is_aux.add(ins.raw_pc + 1)

        # Collect all jump targets (raw_pc values) for block boundary detection
        jump_targets: Set[int] = set()
        for ins in code:
            op = ins.op
            if op in JUMP_OPS | CMP_SYM.keys() | {OP['JUMPIF'],OP['JUMPIFNOT'],
               OP['FORNPREP'],OP['FORNLOOP']} | FORG_PREP | FORG_LOOP | \
               {OP['JUMPXEQKNIL'],OP['JUMPXEQKB'],OP['JUMPXEQKN'],OP['JUMPXEQKS']}:
                t = ins.raw_pc + 1 + ins.sd
                jump_targets.add(t)

        # ── Register tracking ────────────────────────────────────────────────
        # reg_val[r] = current expression string for register r
        reg_val: Dict[int, str] = {}
        # declared[r] = local var name (once emitted as 'local X =')
        declared: Dict[int, str] = {}

        def rv(r: int, pc: int) -> str:
            lv = _local_at(proto, r, pc)
            if lv: return lv
            if r in reg_val: return reg_val[r]
            return f'r{r}'

        def assign(r: int, expr: str, pc: int, force_local: bool = False):
            lv = _local_at(proto, r, pc)
            if lv:
                if r not in declared or declared[r] != lv:
                    declared[r] = lv
                    lines.append(f'{tab}local {lv} = {expr}')
                else:
                    lines.append(f'{tab}{lv} = {expr}')
                reg_val[r] = lv
            elif force_local:
                name = f'v{r}'
                lines.append(f'{tab}local {name} = {expr}')
                reg_val[r] = name
            else:
                reg_val[r] = expr

        # ── Method-call tracking ─────────────────────────────────────────────
        namecall_reg = -1
        namecall_self = ''
        namecall_method = ''

        # ── Main instruction loop ────────────────────────────────────────────
        loop_stack: List[Dict] = []   # stack of {type, old_depth}
        ci = 0  # index into proto.code

        def current_tab(): return '\t' * depth_now[0]

        depth_now = [depth]

        while ci < len(code):
            ins = code[ci]
            op = ins.op
            pc = ins.raw_pc
            tab = '\t' * depth_now[0]

            # ─ Skip NOP / internal ops ────────────────────────────────────────
            if op in (OP['NOP'], OP['BREAK'], OP['COVERAGE'], OP['PREPVARARGS'],
                      OP['CLOSEUPVALS']):
                ci += 1; continue
            if op == OP['CAPTURE']:
                ci += 1; continue
            if op in (OP['FASTCALL'], OP['FASTCALL1'], OP['FASTCALL2'], OP['FASTCALL2K']):
                ci += 1; continue

            # ─ LOADNIL ────────────────────────────────────────────────────────
            if op == OP['LOADNIL']:
                for reg in range(ins.a, ins.a + ins.b + 1):
                    assign(reg, 'nil', pc)

            # ─ LOADB ──────────────────────────────────────────────────────────
            elif op == OP['LOADB']:
                assign(ins.a, 'true' if ins.b else 'false', pc)
                if ins.c: ci += 2; continue

            # ─ LOADN ──────────────────────────────────────────────────────────
            elif op == OP['LOADN']:
                assign(ins.a, str(ins.sd), pc)

            # ─ LOADK / LOADKX ─────────────────────────────────────────────────
            elif op == OP['LOADK']:
                assign(ins.a, self._kv(proto, ins.d), pc)
            elif op == OP['LOADKX']:
                assign(ins.a, self._kv(proto, ins.aux), pc)

            # ─ MOVE ───────────────────────────────────────────────────────────
            elif op == OP['MOVE']:
                assign(ins.a, rv(ins.b, pc), pc)

            # ─ GETUPVAL / SETUPVAL ─────────────────────────────────────────────
            elif op == OP['GETUPVAL']:
                assign(ins.a, self._uv(proto, ins.b), pc)
            elif op == OP['SETUPVAL']:
                lines.append(f'{tab}{self._uv(proto, ins.b)} = {rv(ins.a, pc)}')

            # ─ GETIMPORT ──────────────────────────────────────────────────────
            elif op == OP['GETIMPORT']:
                kc = proto.consts[ins.aux] if ins.aux < len(proto.consts) else None
                if kc and kc.ctype == 4:
                    expr = _decode_import(kc.value, proto.consts, self.strtab)
                else:
                    expr = self._kv(proto, ins.aux)
                assign(ins.a, expr, pc)

            # ─ GETTABLE / SETTABLE ────────────────────────────────────────────
            elif op == OP['GETTABLE']:
                assign(ins.a, f'{rv(ins.b,pc)}[{rv(ins.c,pc)}]', pc)
            elif op == OP['SETTABLE']:
                lines.append(f'{tab}{rv(ins.b,pc)}[{rv(ins.c,pc)}] = {rv(ins.a,pc)}')

            # ─ GETTABLEKS / SETTABLEKS ────────────────────────────────────────
            elif op == OP['GETTABLEKS']:
                fn = self._ks(proto, ins.aux)
                obj = rv(ins.b, pc)
                expr = f'{obj}.{fn}' if _is_ident(fn) else f'{obj}[{repr(fn)}]'
                assign(ins.a, expr, pc)
            elif op == OP['SETTABLEKS']:
                fn = self._ks(proto, ins.aux)
                obj = rv(ins.b, pc)
                lhs = f'{obj}.{fn}' if _is_ident(fn) else f'{obj}[{repr(fn)}]'
                lines.append(f'{tab}{lhs} = {rv(ins.a,pc)}')

            # ─ GETTABLEN / SETTABLEN ──────────────────────────────────────────
            elif op == OP['GETTABLEN']:
                assign(ins.a, f'{rv(ins.b,pc)}[{ins.c+1}]', pc)
            elif op == OP['SETTABLEN']:
                lines.append(f'{tab}{rv(ins.b,pc)}[{ins.c+1}] = {rv(ins.a,pc)}')

            # ─ NEWCLOSURE / DUPCLOSURE ────────────────────────────────────────
            elif op in (OP['NEWCLOSURE'], OP['DUPCLOSURE']):
                child_proto_idx = proto.child_protos[ins.d] if ins.d < len(proto.child_protos) else -1
                child = self.all_protos[child_proto_idx] if 0 <= child_proto_idx < len(self.all_protos) else None

                if child:
                    ps = self._params(child)
                    lv = _local_at(proto, ins.a, pc)
                    fname = lv or f'f{ins.a}'

                    body_lines = self._emit_body(child, depth_now[0] + 1)
                    real = [l for l in body_lines if l.strip() and not l.strip().startswith('--')]

                    if len(real) <= 1:
                        inner = real[0].strip() if real else ''
                        expr = f'function({ps}) {inner} end'
                        assign(ins.a, expr, pc)
                    else:
                        if lv and (ins.a not in declared or declared[ins.a] != lv):
                            declared[ins.a] = lv
                            lines.append(f'{tab}local {lv}')
                        lines.append(f'{tab}{fname} = function({ps})')
                        lines.extend(body_lines)
                        lines.append(f'{tab}end')
                        reg_val[ins.a] = fname
                else:
                    assign(ins.a, 'function(...) end', pc)

            # ─ NAMECALL ───────────────────────────────────────────────────────
            elif op == OP['NAMECALL']:
                namecall_reg = ins.a
                namecall_self = rv(ins.b, pc)
                namecall_method = self._ks(proto, ins.aux)
                reg_val[ins.a + 1] = namecall_self  # self slot

            # ─ CALL ───────────────────────────────────────────────────────────
            elif op == OP['CALL']:
                is_nc = (ins.a == namecall_reg and namecall_reg >= 0)
                n_args = ins.b - 1
                n_ret  = ins.c - 1

                if is_nc:
                    # method call: self is at A+1, user args start at A+2
                    if ins.b == 0:  # vararg
                        extra = ['...']
                    elif n_args <= 1:
                        extra = []
                    else:
                        extra = [rv(ins.a + 2 + j, pc) for j in range(n_args - 1)]
                    call_expr = f'{namecall_self}:{namecall_method}({", ".join(extra)})'
                    namecall_reg = -1
                else:
                    func = rv(ins.a, pc)
                    if ins.b == 0:
                        args = ['...']
                    else:
                        args = [rv(ins.a + 1 + j, pc) for j in range(n_args)]
                    call_expr = f'{func}({", ".join(args)})'

                if n_ret == 0:
                    lines.append(f'{tab}{call_expr}')
                elif n_ret == 1:
                    assign(ins.a, call_expr, pc, force_local=False)
                elif n_ret == -1:
                    assign(ins.a, call_expr, pc, force_local=False)
                else:
                    # multi-return
                    rets = []
                    for j in range(n_ret):
                        lv = _local_at(proto, ins.a + j, pc)
                        nm = lv or f'r{ins.a+j}'
                        if lv and (ins.a+j not in declared or declared[ins.a+j] != lv):
                            declared[ins.a+j] = lv
                        rets.append(nm); reg_val[ins.a + j] = nm
                    # Emit as 'local a, b, c = call()'
                    all_local = all(_local_at(proto, ins.a+j, pc) for j in range(n_ret))
                    prefix = 'local ' if all_local else ''
                    lines.append(f'{tab}{prefix}{", ".join(rets)} = {call_expr}')

            # ─ RETURN ─────────────────────────────────────────────────────────
            elif op == OP['RETURN']:
                n = ins.b - 1
                if n == 0:
                    if not loop_stack:  # skip tail return at end of main
                        pass
                    lines.append(f'{tab}return')
                elif n == -1:
                    lines.append(f'{tab}return {rv(ins.a,pc)}, ...')
                else:
                    vals = [rv(ins.a + j, pc) for j in range(n)]
                    lines.append(f'{tab}return {", ".join(vals)}')

            # ─ JUMP / JUMPBACK / JUMPX ────────────────────────────────────────
            elif op in JUMP_OPS:
                # Unconditional jump — skip (control flow handled structurally)
                pass

            # ─ JUMPIF / JUMPIFNOT ─────────────────────────────────────────────
            elif op in (OP['JUMPIF'], OP['JUMPIFNOT']):
                neg = '' if op == OP['JUMPIF'] else 'not '
                cond = rv(ins.a, pc)
                t = ins.raw_pc + 1 + ins.sd
                # Check if it's a while-loop: if jump target comes before current pos
                if t <= pc:
                    lines.append(f'{tab}-- while {neg}{cond} do')
                else:
                    lines.append(f'{tab}if {neg}{cond} then')
                    lines.append(f'{tab}end -- @{t}')

            # ─ Comparison jumps ───────────────────────────────────────────────
            elif op in CMP_SYM:
                sym = CMP_SYM[op]; b_reg = ins.aux
                t = ins.raw_pc + 1 + ins.sd
                lines.append(f'{tab}if {rv(ins.a,pc)} {sym} {rv(b_reg,pc)} then -- @{t}')
                lines.append(f'{tab}end')

            # ─ JUMPXEQK* ──────────────────────────────────────────────────────
            elif op in (OP['JUMPXEQKNIL'],OP['JUMPXEQKB'],OP['JUMPXEQKN'],OP['JUMPXEQKS']):
                flip = bool(ins.aux >> 31); kid = ins.aux & 0x7FFFFFFF
                t = ins.raw_pc + 1 + ins.sd
                rhs = {
                    OP['JUMPXEQKNIL']: 'nil',
                    OP['JUMPXEQKB']: ('true' if kid else 'false'),
                    OP['JUMPXEQKN']: self._kv(proto, kid),
                    OP['JUMPXEQKS']: repr(self._ks(proto, kid)),
                }[op]
                cmp = '~=' if flip else '=='
                lines.append(f'{tab}if {rv(ins.a,pc)} {cmp} {rhs} then -- @{t}')
                lines.append(f'{tab}end')

            # ─ Arithmetic / binary ops ────────────────────────────────────────
            elif op in BINOP_SYM:
                sym = BINOP_SYM[op]
                if op in {OP['ADDK'],OP['SUBK'],OP['MULK'],OP['DIVK'],
                          OP['MODK'],OP['POWK'],OP['IDIVK']}:
                    expr = f'{rv(ins.b,pc)} {sym} {self._kv(proto, ins.c)}'
                elif op in {OP['ANDK'],OP['ORK']}:
                    expr = f'{rv(ins.b,pc)} {sym} {self._kv(proto, ins.c)}'
                elif op == OP['SUBRK']:
                    expr = f'{self._kv(proto, ins.b)} - {rv(ins.c,pc)}'
                elif op == OP['DIVRK']:
                    expr = f'{self._kv(proto, ins.b)} / {rv(ins.c,pc)}'
                elif op == OP['CONCAT']:
                    parts = [rv(ins.b + j, pc) for j in range(ins.c - ins.b + 1)]
                    expr = ' .. '.join(parts)
                else:
                    expr = f'{rv(ins.b,pc)} {sym} {rv(ins.c,pc)}'
                assign(ins.a, expr, pc)

            # ─ Unary ops ──────────────────────────────────────────────────────
            elif op == OP['NOT']:    assign(ins.a, f'not {rv(ins.b,pc)}', pc)
            elif op == OP['MINUS']:  assign(ins.a, f'-{rv(ins.b,pc)}', pc)
            elif op == OP['LENGTH']: assign(ins.a, f'#{rv(ins.b,pc)}', pc)

            # ─ Table construction ─────────────────────────────────────────────
            elif op == OP['NEWTABLE']:
                assign(ins.a, '{}', pc)
            elif op == OP['DUPTABLE']:
                assign(ins.a, '{}', pc)  # best effort
            elif op == OP['SETLIST']:
                tbl = rv(ins.a, pc); n_elem = ins.c - 1; base = ins.aux
                for j in range(n_elem):
                    lines.append(f'{tab}{tbl}[{base + j}] = {rv(ins.b + j, pc)}')

            # ─ Numeric for loop ───────────────────────────────────────────────
            elif op == OP['FORNPREP']:
                # R(A) = limit, R(A+1) = step, R(A+2) = initial
                limit = rv(ins.a, pc); step = rv(ins.a + 1, pc); init = rv(ins.a + 2, pc)
                idx_nm = _local_at(proto, ins.a + 3, pc) or _local_at(proto, ins.a + 2, pc) or f'_i{ins.a}'
                if not _local_at(proto, ins.a+2, pc):
                    # init already in the limit slot from compiler
                    pass
                lines.append(f'{tab}for {idx_nm} = {init}, {limit}, {step} do')
                loop_stack.append({'type':'forn', 'depth': depth_now[0]})
                depth_now[0] += 1

            elif op == OP['FORNLOOP']:
                if loop_stack and loop_stack[-1]['type'] == 'forn':
                    depth_now[0] = loop_stack.pop()['depth']
                    tab = '\t' * depth_now[0]
                lines.append(f'{tab}end')

            # ─ Generic for loop ───────────────────────────────────────────────
            elif op in FORG_PREP:
                n_vars = ins.b
                var_names = []
                for j in range(n_vars):
                    nm = _local_at(proto, ins.a + 3 + j, pc) or f'_v{j}'
                    var_names.append(nm)
                in_expr = rv(ins.a, pc)
                lines.append(f'{tab}for {", ".join(var_names)} in {in_expr} do')
                loop_stack.append({'type':'forg', 'depth': depth_now[0]})
                depth_now[0] += 1

            elif op in FORG_LOOP:
                if loop_stack and loop_stack[-1]['type'] == 'forg':
                    depth_now[0] = loop_stack.pop()['depth']
                    tab = '\t' * depth_now[0]
                lines.append(f'{tab}end')

            # ─ Varargs ────────────────────────────────────────────────────────
            elif op == OP['GETVARARGS']:
                n = ins.b - 1
                if n == 1:
                    assign(ins.a, '...', pc)
                elif n == -1:
                    assign(ins.a, '...', pc)
                else:
                    for j in range(n):
                        assign(ins.a + j, f'select({j+1}, ...)', pc)

            # ─ Unknown ────────────────────────────────────────────────────────
            else:
                lines.append(f'{tab}-- [{ins.name}] A={ins.a} B={ins.b} C={ins.c} AUX={ins.aux}')

            ci += 1

        return lines

# ─── Entry point ──────────────────────────────────────────────────────────────

def load_bytecode(path: str) -> bytes:
    with open(path, 'rb') as f:
        data = f.read()

    # If it looks like a text file with base64 in a Lua comment
    if data[:2] == b'--':
        for raw_line in data.split(b'\n'):
            line = raw_line.strip()
            if line.startswith(b'--'):
                candidate = line[2:].strip()
                try:
                    decoded = base64.b64decode(candidate)
                    if 3 <= decoded[0] <= 9:
                        return decoded
                except Exception:
                    pass
        raise ValueError("Could not find valid base64 bytecode in Lua comment")

    # Maybe raw binary
    if 3 <= data[0] <= 9:
        return data

    # Maybe raw base64
    try:
        decoded = base64.b64decode(data.strip())
        if 3 <= decoded[0] <= 9:
            return decoded
    except Exception:
        pass

    raise ValueError(f"Cannot determine bytecode format for {path}")


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__); sys.exit(1)

    path = args[0]
    do_dis  = '--dis'  in args or '--both' in args
    do_dec  = '--dis'  not in args  # decompile unless --dis only

    raw = load_bytecode(path)
    parser = Parser(raw)
    try:
        main_proto = parser.parse()
    except Exception as e:
        print(f"Parse error: {e}", file=sys.stderr)
        import traceback; traceback.print_exc()
        sys.exit(1)

    if do_dis:
        dis_out: List[str] = [
            '; LuauDump Disassembly',
            f'; Bytecode version: {parser.version}  Types version: {parser.types_version}',
            f'; String table: {len(parser.strtab)-1} entries',
            f'; Proto table:  {len(parser.all_protos)} protos',
            '',
        ]
        disassemble(main_proto, parser.all_protos, parser.strtab, dis_out)
        if '--both' in args:
            print('\n'.join(dis_out))
            print('\n' + '-'*60 + ' DECOMPILATION\n')
        else:
            print('\n'.join(dis_out))
            return

    if do_dec:
        dec = Decompiler(parser.all_protos, parser.strtab)
        print(dec.run(main_proto))


if __name__ == '__main__':
    main()
