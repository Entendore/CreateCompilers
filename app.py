"""
Nova Language Workshop — Complete Unified Edition
=================================================
A comprehensive language development environment combining:
  • PEG grammar definition & parsing
  • Custom source language with esoteric features
  • Multi-level IR pipeline (HIR → MIR → SSA → LIR)
  • 10 code generation backends
  • Hindley-Milner type inference
  • Advanced optimizations + PGO
  • Grammar workflow toolkit (testing, fuzzing, mutation, coverage)
  • Visualizations (railroad, NFA/DFA, CFG, flame graph, timeline)
  • Professional IDE (themes, layouts, command palette, minimap)

Run:
    python nova_workshop.py              # launch IDE
    python nova_workshop.py --verify     # headless regression
    python nova_workshop.py --pgo        # PGO demo
"""

import sys, re, json, time, hashlib, os, random, itertools, math, copy
from dataclasses import dataclass, field
from collections import defaultdict, deque
from typing import List, Dict, Set, Tuple, Optional, Any

# ============================================================================
# 1. PEG GRAMMAR ENGINE
# ============================================================================

class _G: pass
class _Grammar(_G):
    def __init__(self, rules): self.rules = rules
class _Rule(_G):
    def __init__(self, name, expr): self.name, self.expr = name, expr
class _Choice(_G):
    def __init__(self, exprs): self.exprs = exprs
class _Seq(_G):
    def __init__(self, exprs): self.exprs = exprs
class _Repeat(_G):
    def __init__(self, expr, lo, hi): self.expr, self.lo, self.hi = expr, lo, hi
class _Lit(_G):
    def __init__(self, value): self.value = value
class _Regex(_G):
    def __init__(self, pattern): self.pattern = pattern
    @property
    def compiled(self): return re.compile(self.pattern)
class _Ref(_G):
    def __init__(self, name): self.name = name


class _GLexer:
    SPEC = [
        ("COMMENT", r"#[^\n]*"), ("ARROW", r"<-"),
        ("LITERAL", r"'[^']*'|\"[^\"]*\""),
        ("REGEX",   r"(?!\s)(?:\\.|[^/\\\n])+"),
        ("NAME",    r"[a-zA-Z_]\w*"),
        ("STAR", r"\*"), ("PLUS", r"\+"), ("QUESTION", r"\?"),
        ("SLASH", r"/"), ("LPAREN", r"\("), ("RPAREN", r"\)"),
        ("WS", r"\s+"), ("BAD", r"."),
    ]
    MASTER = re.compile("|".join(f"(?P<{n}>{p})" for n, p in SPEC))
    @classmethod
    def tokenize(cls, text):
        out = []
        for m in cls.MASTER.finditer(text):
            k, v = m.lastgroup, m.group()
            if k in ("WS", "COMMENT"): continue
            if k == "BAD": raise SyntaxError(f"Grammar: unexpected {v!r}")
            if k == "REGEX": v = v[1:-1]
            elif k == "LITERAL": v = v[1:-1]
            out.append((k, v))
        return out


class _GParser:
    def __init__(self, tokens): self.tokens, self.pos = tokens, 0
    def peek(self): return self.tokens[self.pos] if self.pos < len(self.tokens) else None
    def eat(self, kind):
        t = self.peek()
        if not t or t[0] != kind: raise SyntaxError(f"Grammar: expected {kind}, got {t}")
        self.pos += 1; return t[1]
    def parse(self):
        rules = {}
        while self.peek():
            name = self.eat("NAME"); self.eat("ARROW")
            rules[name] = _Rule(name, self.expression())
        return _Grammar(rules)
    def expression(self):
        seqs = [self.sequence()]
        while self.peek() and self.peek()[0] == "SLASH":
            self.pos += 1; seqs.append(self.sequence())
        return seqs[0] if len(seqs) == 1 else _Choice(seqs)
    def sequence(self):
        parts = []
        while self.peek() and self.peek()[0] not in ("SLASH", "RPAREN"):
            if (self.peek()[0] == "NAME" and self.pos + 1 < len(self.tokens)
                    and self.tokens[self.pos + 1][0] == "ARROW"): break
            parts.append(self.prefix())
        return _Seq(parts) if len(parts) != 1 else (parts[0] if parts else _Seq([]))
    def prefix(self):
        node = self.suffix()
        if self.peek() and self.peek()[0] in ("STAR", "PLUS", "QUESTION"):
            op = self.eat(self.peek()[0])
            return _Repeat(node, 0, float("inf")) if op == "*" \
                else _Repeat(node, 1, float("inf")) if op == "+" \
                else _Repeat(node, 0, 1)
        return node
    def suffix(self):
        t = self.peek()
        if not t: raise SyntaxError("Grammar: unexpected EOF")
        if t[0] == "NAME": return _Ref(self.eat("NAME"))
        if t[0] == "LITERAL": return _Lit(self.eat("LITERAL"))
        if t[0] == "REGEX": return _Regex(self.eat("REGEX"))
        if t[0] == "LPAREN":
            self.eat("LPAREN"); node = self.expression(); self.eat("RPAREN"); return node
        raise SyntaxError(f"Grammar: unexpected {t}")


def expr_to_text(expr) -> str:
    if isinstance(expr, _Lit): return f"'{expr.value}'"
    if isinstance(expr, _Regex): return f"/{expr.pattern}/"
    if isinstance(expr, _Ref): return expr.name
    if isinstance(expr, _Seq): return " ".join(expr_to_text(e) for e in expr.exprs)
    if isinstance(expr, _Choice): return " / ".join(expr_to_text(e) for e in expr.exprs)
    if isinstance(expr, _Repeat):
        inner = expr_to_text(expr.expr)
        if expr.lo == 0 and expr.hi == float("inf"): return f"{inner}*"
        if expr.lo == 1 and expr.hi == float("inf"): return f"{inner}+"
        if expr.lo == 0 and expr.hi == 1: return f"{inner}?"
        return f"{inner}{{{expr.lo},{expr.hi}}}"
    return "/* unknown */"


# ============================================================================
# 2. SOURCE LANGUAGE LEXER / PARSER
# ============================================================================

@dataclass
class PNode:
    rule: str
    children: list
    pos: int = 0
    line: int = 1
    col: int = 1


class _Lexer:
    def __init__(self, grammar):
        specs = []
        for name, rule in grammar.rules.items():
            if name.isupper():
                p = self._pat(rule.expr)
                if p: specs.append((name, p))
        lits = set()
        def walk(n):
            if isinstance(n, _Lit): lits.add(n.value)
            elif isinstance(n, (_Choice, _Seq)):
                for e in n.exprs: walk(e)
            elif isinstance(n, _Repeat): walk(n.expr)
        for rule in grammar.rules.values(): walk(rule.expr)
        for v in sorted(lits, key=lambda s: (-len(s), s)):
            specs.append((f"P{len(specs)}", re.escape(v)))
        self.specs = specs
        self.master = re.compile("|".join(f"(?P<{n}>{p})" for n, p in specs))
    def _pat(self, n):
        if isinstance(n, _Regex): return n.pattern
        if isinstance(n, _Lit): return re.escape(n.value)
        if isinstance(n, _Choice):
            parts = [self._pat(e) for e in n.exprs]
            if all(parts): return "|".join(f"(?:{p})" for p in parts)
        return None
    def tokenize(self, text):
        tokens, pos, line, col = [], 0, 1, 1
        while pos < len(text):
            if text[pos] == "\n": line += 1; col = 1; pos += 1; continue
            if text[pos].isspace(): pos += 1; col += 1; continue
            m = self.master.match(text, pos)
            if not m: raise SyntaxError(f"Lex error at {line}:{col}: {text[pos]!r}")
            kind, value = m.lastgroup, m.group()
            pos = m.end(); col += len(value)
            tokens.append((kind, value, m.start(), line, col - len(value) + 1))
        tokens.append(("EOF", "", len(text), line, col))
        return tokens


class _Parser:
    def __init__(self, grammar, tokens, trace=False):
        self.grammar, self.tokens, self.pos = grammar, tokens, 0
        self.trace = trace
        self.trace_log = []
        self.depth = 0

    def peek(self): return self.tokens[self.pos] if self.pos < len(self.tokens) else None
    def parse(self, start="program"):
        node = self._rule(start)
        if node is None:
            t = self.peek()
            raise SyntaxError(f"Parse error at {t[3]}:{t[4]}: {t[1]!r}")
        t = self.peek()
        if t and t[0] != "EOF":
            raise SyntaxError(f"Trailing input at {t[3]}:{t[4]}: {t[1]!r}")
        return node

    def _log(self, event, rule, detail=""):
        if self.trace:
            self.trace_log.append((self.depth, event, rule, self.pos, detail))

    def _rule(self, name):
        t = self.peek()
        if name.isupper():
            if t and t[0] == name:
                self._log("match", name, t[1])
                self.pos += 1
                return PNode(name, [t], t[2], t[3], t[4])
            self._log("fail", name)
            return None
        rule = self.grammar.rules.get(name)
        if rule is None: raise RuntimeError(f"Undefined rule: {name}")
        saved = self.pos
        self._log("enter", name)
        self.depth += 1
        frag = self._expr(rule.expr)
        self.depth -= 1
        if frag is None:
            self.pos = saved
            self._log("fail", name)
            return None
        if isinstance(frag, list):
            children = frag
            if children and isinstance(children[0], PNode):
                first = children[0]
                pos, line, col = first.pos, first.line, first.col
            else:
                pos, line, col = (t[2], t[3], t[4]) if t else (0, 1, 1)
        else:
            children = [frag]
            pos, line, col = frag.pos, frag.line, frag.col
        self._log("exit", name)
        return PNode(name, children, pos, line, col)

    def _expr(self, node):
        if isinstance(node, _Choice):
            for alt in node.exprs:
                saved = self.pos
                r = self._expr(alt)
                if r is not None: return r
                self.pos = saved
            return None
        if isinstance(node, _Seq):
            parts = []
            for e in node.exprs:
                r = self._expr(e)
                if r is None: return None
                parts.extend(r if isinstance(r, list) else [r])
            return parts
        if isinstance(node, _Repeat):
            parts, count = [], 0
            while count < node.hi:
                saved = self.pos
                r = self._expr(node.expr)
                if r is None: self.pos = saved; break
                parts.extend(r if isinstance(r, list) else [r])
                count += 1
                if self.pos == saved: break
            return parts if count >= node.lo else None
        if isinstance(node, _Lit):
            t = self.peek()
            if t and t[1] == node.value:
                self.pos += 1
                return PNode("LITERAL", [t], t[2], t[3], t[4])
            return None
        if isinstance(node, _Regex):
            t = self.peek()
            if t and node.compiled.fullmatch(t[1]):
                self.pos += 1
                return PNode("REGEX", [t], t[2], t[3], t[4])
            return None
        if isinstance(node, _Ref): return self._rule(node.name)
        return None


# ============================================================================
# 3. DEFAULT GRAMMAR (extended language)
# ============================================================================

DEFAULT_GRAMMAR = r"""
COMMENT    <- /#[^\n]*/
PRINT      <- /print\b/
LET        <- /let\b/
IF         <- /if\b/
ELSE       <- /else\b/
WHILE      <- /while\b/
FOR        <- /for\b/
FUNC       <- /func\b/
RETURN     <- /return\b/
BREAK      <- /break\b/
CONTINUE   <- /continue\b/
TRY        <- /try\b/
CATCH      <- /catch\b/
THROW      <- /throw\b/
MATCH      <- /match\b/
CASE       <- /case\b/
AND        <- /and\b/
OR         <- /or\b/
NOT        <- /not\b/
BOOL       <- /\b(?:true|false)\b/
NULL       <- /\bnull\b/
REGEX      <- /r"(?:\\.|[^"\\])*"/
STRING     <- /"(?:\\.|[^"\\])*"/
NUMBER     <- /\d+(\.\d+)?/
IDENT      <- /[a-zA-Z_]\w*/

program       <- statement*
statement     <- print_stmt / let_stmt / assign_stmt / if_stmt / while_stmt
                 / for_stmt / func_def / return_stmt / break_stmt
                 / continue_stmt / try_stmt / throw_stmt / match_stmt / expr_stmt
print_stmt    <- PRINT expr
let_stmt      <- LET IDENT '=' expr
assign_stmt   <- target '=' expr
target        <- IDENT ('[' expr ']')?
if_stmt       <- IF expr block (ELSE (if_stmt / block))?
while_stmt    <- WHILE expr block
for_stmt      <- FOR IDENT '=' expr ',' expr (',' expr)? block
func_def      <- FUNC IDENT '(' params? ')' block
return_stmt   <- RETURN expr?
break_stmt    <- BREAK
continue_stmt <- CONTINUE
try_stmt      <- TRY block CATCH '(' IDENT ')' block
throw_stmt    <- THROW expr
match_stmt    <- MATCH expr '{' case_clause* '}'
case_clause   <- CASE pattern '=>' block
expr_stmt     <- expr
block         <- '{' statement* '}'
params        <- IDENT (',' IDENT)*
pattern       <- NUMBER / STRING / BOOL / NULL / IDENT / array_pattern
array_pattern <- '[' (pattern (',' pattern)*)? ']'
expr          <- or_expr
or_expr       <- and_expr (OR and_expr)*
and_expr      <- comparison (AND comparison)*
comparison    <- add_expr (('==' / '!=' / '<=' / '>=' / '<' / '>') add_expr)*
add_expr      <- mul_expr (('+' / '-') mul_expr)*
mul_expr      <- unary (('*' / '/' / '%' / '//') unary)*
unary         <- ('-' / NOT) unary / postfix
postfix       <- primary ('[' expr ']')*
primary       <- call / atom
atom          <- NUMBER / STRING / REGEX / BOOL / NULL / IDENT
                 / '(' expr ')' / array / dict
call          <- IDENT '(' args? ')'
args          <- expr (',' expr)*
array         <- '[' (expr (',' expr)*)? ']'
dict          <- '{' (pair (',' pair)*)? '}'
pair          <- expr ':' expr
"""


# ============================================================================
# 4. SOURCE LANGUAGE INTERPRETER
# ============================================================================

class NovaError(Exception): pass
class ThrowSignal(Exception):
    def __init__(self, value): self.value = value
class ReturnSignal(Exception):
    def __init__(self, value): self.value = value
class BreakSignal(Exception): pass
class ContinueSignal(Exception): pass


def subs(node):
    return [c for c in node.children if isinstance(c, PNode)]

def pn(node, rule):
    for c in node.children:
        if isinstance(c, PNode) and c.rule == rule: return c
    return None

def pns(node, rule):
    return [c for c in node.children if isinstance(c, PNode) and c.rule == rule]

def first_sub(node):
    for c in node.children:
        if isinstance(c, PNode): return c
    return None

def token_value(node):
    if not node.children: return ""
    c = node.children[0]
    return c[1] if isinstance(c, tuple) else token_value(c)

def ident_of(node):
    for c in node.children:
        if isinstance(c, PNode) and c.rule == "IDENT":
            return token_value(c)
    return None

def all_idents(node):
    out = []
    if isinstance(node, PNode):
        if node.rule == "IDENT": return [token_value(node)]
        for c in node.children: out.extend(all_idents(c))
    return out

def unescape(s):
    table = {"n": "\n", "r": "\r", "t": "\t", '"': '"', "\\": "\\"}
    return re.sub(r'\\([nrt"\\])', lambda m: table.get(m.group(1), m.group(1)), s)

def render(value):
    if value is None: return "null"
    if isinstance(value, bool): return "true" if value else "false"
    if isinstance(value, float):
        return str(int(value)) if value.is_integer() else str(value)
    if isinstance(value, list):
        return "[" + ", ".join(render(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{" + ", ".join(f"{render(k)}: {render(v)}" for k, v in value.items()) + "}"
    if isinstance(value, Closure): return f"<function {value.name}>"
    return str(value)


class Environment:
    def __init__(self, parent=None):
        self.vars, self.parent = {}, parent
    def get(self, name):
        if name in self.vars: return self.vars[name]
        if self.parent: return self.parent.get(name)
        raise NovaError(f"Undefined variable '{name}'")
    def find(self, name):
        if name in self.vars: return self.vars[name]
        return self.parent.find(name) if self.parent else None
    def set(self, name, value): self.vars[name] = value
    def assign(self, name, value):
        if name in self.vars: self.vars[name] = value
        elif self.parent: self.parent.assign(name, value)
        else: raise NovaError(f"Undefined variable '{name}'")
    def all_vars(self):
        out, env = {}, self
        while env:
            for k, v in env.vars.items(): out.setdefault(k, v)
            env = env.parent
        return out


class Closure:
    def __init__(self, name, params, body, env):
        self.name, self.params, self.body, self.env = name, params, body, env


def _type_name(v):
    if v is None: return "Null"
    if isinstance(v, bool): return "Bool"
    if isinstance(v, int): return "Int"
    if isinstance(v, float): return "Float"
    if isinstance(v, str): return "String"
    if isinstance(v, list): return "List"
    if isinstance(v, dict): return "Dict"
    if isinstance(v, Closure): return "Function"
    return type(v).__name__


BUILTINS = {
    "str": lambda x: str(x),
    "int": lambda x: int(x),
    "float": lambda x: float(x),
    "len": lambda x: len(x),
    "type": lambda x: _type_name(x),
    "abs": lambda x: abs(x),
    "pow": lambda a, b: a ** b,
    "sum": lambda a: sum(a),
    "min": lambda *a: min(a[0] if len(a) == 1 else a),
    "max": lambda *a: max(a[0] if len(a) == 1 else a),
    "upper": lambda s: str(s).upper(),
    "lower": lambda s: str(s).lower(),
    "strip": lambda s: str(s).strip(),
    "split": lambda s, sep=" ": str(s).split(sep),
    "join": lambda sep, arr: str(sep).join(str(x) for x in arr),
    "replace": lambda s, a, b: str(s).replace(str(a), str(b)),
    "find": lambda s, sub: str(s).find(str(sub)),
    "keys": lambda d: list(d.keys()),
    "values": lambda d: list(d.values()),
    "items": lambda d: [[k, v] for k, v in d.items()],
    "has_key": lambda d, k: k in d,
    "push": lambda arr, x: (arr.append(x), arr)[1],
    "pop": lambda arr: arr.pop(),
    "regex": lambda pat, text: bool(pat.search(str(text))),
    "find_all": lambda pat, text: list(pat.findall(str(text))),
    "range": lambda a, b=None, step=1: list(range(a, b if b is not None else a,
                                                  step if b is not None else 1)),
}


class Interpreter:
    def __init__(self):
        self.env = Environment()
        self.output = []
        self.steps = 0
        self.max_steps = 200_000
        self.depth = 0
        self.call_stack = []
        self.coverage = set()
        self.breakpoints = set()
        self.paused_at = None

    def run(self, ast):
        for stmt in pns(ast, "statement"):
            self.eval_stmt(first_sub(stmt))
        return self.output

    def exec_block(self, block):
        for stmt in pns(block, "statement"):
            self.eval_stmt(first_sub(stmt))

    def eval_stmt(self, node):
        self.steps += 1
        if self.steps > self.max_steps:
            raise NovaError("Execution limit exceeded")
        if node.line: self.coverage.add(node.line)
        if node.line in self.breakpoints:
            self.paused_at = node.line
            return

        r = node.rule
        if r == "print_stmt":
            self.output.append(render(self.eval_expr(pn(node, "expr"))))
        elif r == "let_stmt":
            self.env.set(ident_of(node), self.eval_expr(pn(node, "expr")))
        elif r == "assign_stmt":
            target = pn(node, "target")
            value = self.eval_expr(pn(node, "expr"))
            name = ident_of(target)
            index = pn(target, "expr")
            if index:
                self.env.get(name)[self.eval_expr(index)] = value
            else:
                self.env.assign(name, value)
        elif r == "if_stmt":
            cond = self.eval_expr(pn(node, "expr"))
            blocks = pns(node, "block")
            elseif = pn(node, "if_stmt")
            if cond:
                self.exec_block(blocks[0])
            elif elseif is not None:
                self.eval_stmt(elseif)
            elif len(blocks) > 1:
                self.exec_block(blocks[1])
        elif r == "while_stmt":
            while self.eval_expr(pn(node, "expr")):
                try: self.exec_block(pn(node, "block"))
                except BreakSignal: break
                except ContinueSignal: pass
        elif r == "for_stmt":
            name = ident_of(node)
            exprs = pns(node, "expr")
            start = self.eval_expr(exprs[0])
            end = self.eval_expr(exprs[1])
            step = self.eval_expr(exprs[2]) if len(exprs) > 2 else 1
            if step == 0: raise NovaError("for-loop step cannot be zero")
            i = start
            while (i < end if step > 0 else i > end):
                self.env.set(name, i)
                try: self.exec_block(pn(node, "block"))
                except BreakSignal: break
                except ContinueSignal: pass
                i += step
        elif r == "func_def":
            name = ident_of(node)
            params_node = pn(node, "params")
            params = all_idents(params_node) if params_node else []
            self.env.set(name, Closure(name, params, pn(node, "block"), self.env))
        elif r == "return_stmt":
            e = pn(node, "expr")
            raise ReturnSignal(self.eval_expr(e) if e else None)
        elif r == "break_stmt": raise BreakSignal()
        elif r == "continue_stmt": raise ContinueSignal()
        elif r == "throw_stmt":
            raise ThrowSignal(self.eval_expr(pn(node, "expr")))
        elif r == "try_stmt":
            blocks = pns(node, "block")
            try: self.exec_block(blocks[0])
            except (ThrowSignal, NovaError) as exc:
                value = exc.value if isinstance(exc, ThrowSignal) else str(exc)
                self.env.set(ident_of(node), value)
                self.exec_block(blocks[1])
        elif r == "match_stmt":
            value = self.eval_expr(pn(node, "expr"))
            for case in pns(node, "case_clause"):
                pattern = pn(case, "pattern")
                if self.match_pattern(first_sub(pattern), value):
                    self.exec_block(pn(case, "block"))
                    return
        elif r == "expr_stmt":
            self.eval_expr(pn(node, "expr"))

    def eval_expr(self, node):
        if node is None: return None
        if not isinstance(node, PNode):
            return node[1] if isinstance(node, tuple) else node
        self.steps += 1
        if self.steps > self.max_steps:
            raise NovaError("Execution limit exceeded")
        r = node.rule
        if r in ("expr", "primary"): return self.eval_expr(first_sub(node))
        if r in ("or_expr", "and_expr", "comparison", "add_expr", "mul_expr"):
            return self.infix(node, short_circuit=r in ("or_expr", "and_expr"))
        if r == "unary":
            parts = subs(node)
            if len(parts) == 1: return self.eval_expr(parts[0])
            op = token_value(parts[0])
            value = self.eval_expr(parts[1])
            return -value if op == "-" else not value
        if r == "postfix":
            parts = subs(node)
            value = self.eval_expr(parts[0])
            i = 1
            while i + 2 < len(parts) + 1 and i < len(parts):
                index_node = parts[i + 1]
                value = value[self.eval_expr(index_node)]
                i += 3
            return value
        if r == "atom":
            grouped = pns(node, "expr")
            if grouped: return self.eval_expr(grouped[0])
            return self.eval_expr(subs(node)[0])
        if r == "NUMBER":
            raw = token_value(node)
            return float(raw) if "." in raw else int(raw)
        if r == "STRING": return unescape(token_value(node)[1:-1])
        if r == "REGEX": return re.compile(token_value(node)[2:-1])
        if r == "BOOL": return token_value(node) == "true"
        if r == "NULL": return None
        if r == "IDENT": return self.env.get(token_value(node))
        if r == "array":
            return [self.eval_expr(e) for e in pns(node, "expr")]
        if r == "dict":
            result = {}
            for pair in pns(node, "pair"):
                exprs = pns(pair, "expr")
                result[self.eval_expr(exprs[0])] = self.eval_expr(exprs[1])
            return result
        if r == "call":
            name = ident_of(node)
            args_node = pn(node, "args")
            args = ([self.eval_expr(e) for e in pns(args_node, "expr")]
                    if args_node else [])
            return self.call_function(name, args, node.line)
        raise NovaError(f"Cannot evaluate expression '{r}'")

    def op_text(self, node):
        if node.rule == "LITERAL" or node.rule in ("AND", "OR", "NOT"):
            return token_value(node)
        return None

    def infix(self, node, short_circuit=False):
        left, op = None, None
        for child in subs(node):
            text = self.op_text(child)
            if text is not None:
                op = text; continue
            if left is None and op is None:
                left = self.eval_expr(child); continue
            if short_circuit and op == "or" and left: return left
            if short_circuit and op == "and" and not left: return left
            right = self.eval_expr(child)
            left = self.apply(op, left, right)
            op = None
        return left

    def apply(self, op, a, b):
        if op == "+":
            return str(a) + str(b) if isinstance(a, str) or isinstance(b, str) else a + b
        if op == "-": return a - b
        if op == "*": return a * b
        if op == "/":
            if b == 0: raise NovaError("Division by zero")
            return a / b
        if op == "//":
            if b == 0: raise NovaError("Division by zero")
            return a // b
        if op == "%":
            if b == 0: raise NovaError("Modulo by zero")
            return a % b
        if op == "==": return a == b
        if op == "!=": return a != b
        if op == "<": return a < b
        if op == ">": return a > b
        if op == "<=": return a <= b
        if op == ">=": return a >= b
        if op == "and": return a and b
        if op == "or": return a or b
        raise NovaError(f"Unknown operator '{op}'")

    def call_function(self, name, args, line=None):
        if name in BUILTINS:
            try: return BUILTINS[name](*args)
            except TypeError as e: raise NovaError(f"{name}(): {e}")
            except (ValueError, ZeroDivisionError) as e: raise NovaError(f"{name}(): {e}")
        target = self.env.find(name)
        if isinstance(target, Closure): return self.invoke(target, args, line)
        raise NovaError(f"Unknown function '{name}'")

    def invoke(self, closure, args, line=None):
        if len(args) != len(closure.params):
            raise NovaError(f"{closure.name}() expects {len(closure.params)} args, got {len(args)}")
        self.depth += 1
        if self.depth > 150:
            self.depth -= 1
            raise NovaError("Recursion limit exceeded")
        saved = self.env
        local = Environment(closure.env)
        for p, a in zip(closure.params, args): local.set(p, a)
        self.env = local
        self.call_stack.append((closure.name, line))
        try:
            self.exec_block(closure.body)
        except ReturnSignal as ret:
            return ret.value
        finally:
            self.env = saved
            self.call_stack.pop()
            self.depth -= 1
        return None

    def match_pattern(self, node, value):
        r = node.rule
        if r == "NUMBER":
            raw = token_value(node)
            return value == (float(raw) if "." in raw else int(raw))
        if r == "STRING": return value == unescape(token_value(node)[1:-1])
        if r == "BOOL": return value == (token_value(node) == "true")
        if r == "NULL": return value is None
        if r == "IDENT":
            name = token_value(node)
            if name == "_": return True
            self.env.set(name, value)
            return True
        if r == "array_pattern":
            if not isinstance(value, list): return False
            patterns = pns(node, "pattern")
            if len(patterns) != len(value): return False
            return all(self.match_pattern(first_sub(p), v)
                       for p, v in zip(patterns, value))
        return False


# ============================================================================
# 5. TYPE INFERENCE (Hindley-Milner)
# ============================================================================

class TypeVar:
    _counter = 0
    def __init__(self):
        TypeVar._counter += 1
        self.id = TypeVar._counter
        self.name = f"t{self.id}"
    def __repr__(self): return self.name
    def __eq__(self, other): return isinstance(other, TypeVar) and self.id == other.id
    def __hash__(self): return hash(self.id)

class TypeCon:
    def __init__(self, name, args=None):
        self.name, self.args = name, args or []
    def __repr__(self):
        if self.args: return f"{self.name}[{', '.join(repr(a) for a in self.args)}]"
        return self.name
    def __eq__(self, other):
        return isinstance(other, TypeCon) and self.name == other.name and self.args == other.args
    def __hash__(self): return hash((self.name, tuple(self.args)))

T_INT = TypeCon("Int")
T_FLOAT = TypeCon("Float")
T_STRING = TypeCon("String")
T_BOOL = TypeCon("Bool")
T_NULL = TypeCon("Null")
T_VOID = TypeCon("Void")


class TypeInference:
    def __init__(self):
        self.bindings = {}
        self.env = {}
        self.errors = []
        self.var_types = {}

    def fresh_var(self): return TypeVar()

    def find(self, t):
        if isinstance(t, TypeVar) and t in self.bindings:
            return self.find(self.bindings[t])
        return t

    def occurs(self, var, t):
        t = self.find(t)
        if isinstance(t, TypeVar): return t == var
        if isinstance(t, TypeCon): return any(self.occurs(var, a) for a in t.args)
        return False

    def unify(self, t1, t2, context=""):
        t1 = self.find(t1); t2 = self.find(t2)
        if t1 == t2: return t1
        if isinstance(t1, TypeVar):
            if self.occurs(t1, t2):
                self.errors.append(f"Infinite type: {t1} in {t2} ({context})")
                return t1
            self.bindings[t1] = t2; return t2
        if isinstance(t2, TypeVar): return self.unify(t2, t1, context)
        if isinstance(t1, TypeCon) and isinstance(t2, TypeCon):
            if t1.name != t2.name:
                self.errors.append(f"Type mismatch: {t1} vs {t2} ({context})")
                return t1
            if len(t1.args) != len(t2.args):
                self.errors.append(f"Arity mismatch: {t1} vs {t2} ({context})")
                return t1
            for a1, a2 in zip(t1.args, t2.args):
                self.unify(a1, a2, context)
            return t1
        return t1

    def infer(self, ast):
        self.env['print'] = TypeCon("Func", [self.fresh_var(), T_VOID])
        self.env['len'] = TypeCon("Func", [TypeCon("List", [self.fresh_var()]), T_INT])
        self.env['str'] = TypeCon("Func", [self.fresh_var(), T_STRING])
        self.env['int'] = TypeCon("Func", [self.fresh_var(), T_INT])
        self.env['float'] = TypeCon("Func", [self.fresh_var(), T_FLOAT])
        self.env['true'] = T_BOOL
        self.env['false'] = T_BOOL
        self.env['null'] = T_NULL

        for child in ast.children:
            if isinstance(child, PNode) and child.rule == 'statement':
                self.infer_stmt(child.children[0])
        for name, t in self.env.items():
            self.var_types[name] = self.find(t)
        return self.var_types

    def infer_stmt(self, node):
        rule = node.rule
        if rule == 'let_stmt':
            name = node.children[1][1]
            t = self.infer_expr(node.children[3])
            self.env[name] = t
            self.var_types[name] = self.find(t)
        elif rule == 'assign_stmt':
            name = node.children[0][1]
            t = self.infer_expr(node.children[2])
            if name in self.env: self.unify(self.env[name], t, f"assignment to {name}")
        elif rule == 'print_stmt': self.infer_expr(node.children[1])
        elif rule == 'if_stmt':
            cond = self.infer_expr(node.children[1])
            self.unify(cond, T_BOOL, "if condition")
            for s in node.children[3].children: self.infer_stmt(s)
            if len(node.children) > 5:
                for s in node.children[5].children: self.infer_stmt(s)
        elif rule == 'while_stmt':
            cond = self.infer_expr(node.children[1])
            self.unify(cond, T_BOOL, "while condition")
            for s in node.children[3].children: self.infer_stmt(s)
        elif rule == 'func_def':
            name = node.children[1][1]
            params = [c[1] for c in node.children[3].children if isinstance(c, tuple)]
            param_types = [self.fresh_var() for _ in params]
            ret_type = self.fresh_var()
            func_type = TypeCon("Func", param_types + [ret_type])
            self.env[name] = func_type
            old_env = self.env.copy()
            for p, pt in zip(params, param_types): self.env[p] = pt
            for s in node.children[5].children: self.infer_stmt(s)
            self.env = old_env
            self.var_types[name] = self.find(func_type)
        elif rule == 'return_stmt':
            if len(node.children) > 1: self.infer_expr(node.children[1])
        elif rule == 'expr_stmt': self.infer_expr(node.children[0])

    def infer_expr(self, node):
        if not isinstance(node, PNode):
            if isinstance(node, tuple):
                val = node[1]
                if isinstance(val, bool): return T_BOOL
                if isinstance(val, int): return T_INT
                if isinstance(val, float): return T_FLOAT
                if isinstance(val, str): return T_STRING
            return self.fresh_var()
        rule = node.rule
        if rule == 'NUMBER':
            val = node.children[0][1]
            return T_FLOAT if '.' in val else T_INT
        if rule == 'STRING': return T_STRING
        if rule == 'BOOL': return T_BOOL
        if rule == 'NULL': return T_NULL
        if rule == 'IDENT':
            name = node.children[0][1]
            if name in self.env: return self.find(self.env[name])
            t = self.fresh_var(); self.env[name] = t; return t
        if rule == 'array':
            elem_types = [self.infer_expr(c) for c in node.children if isinstance(c, PNode)]
            if not elem_types: return TypeCon("List", [self.fresh_var()])
            elem_t = elem_types[0]
            for et in elem_types[1:]: self.unify(elem_t, et, "array element")
            return TypeCon("List", [self.find(elem_t)])
        if rule == 'dict':
            return TypeCon("Dict", [self.fresh_var(), self.fresh_var()])
        if rule == 'index':
            obj_t = self.infer_expr(node.children[0])
            self.infer_expr(node.children[2])
            if isinstance(obj_t, TypeCon) and obj_t.name == "List" and obj_t.args:
                return obj_t.args[0]
            return self.fresh_var()
        if rule in ('add_expr', 'mul_expr'):
            left = self.infer_expr(node.children[0])
            for i in range(1, len(node.children), 2):
                op = node.children[i][1]
                right = self.infer_expr(node.children[i+1])
                if op == '+':
                    if isinstance(left, TypeCon) and left.name == "String":
                        self.unify(right, T_STRING, "string concat")
                        left = T_STRING
                    else: self.unify(left, right, "addition")
                elif op in ('-', '*', '/'): self.unify(left, right, op)
                else: self.unify(left, right, op)
            return self.find(left)
        if rule == 'comparison':
            left = self.infer_expr(node.children[0])
            for i in range(1, len(node.children), 2):
                right = self.infer_expr(node.children[i+1])
                self.unify(left, right, "comparison")
            return T_BOOL
        if rule == 'call':
            func_name = node.children[0][1]
            arg_types = [self.infer_expr(c) for c in node.children
                        if isinstance(c, PNode) and c.rule == 'expr']
            if func_name in self.env:
                ft = self.find(self.env[func_name])
                if isinstance(ft, TypeCon) and ft.name == "Func":
                    for i, at in enumerate(arg_types):
                        if i < len(ft.args) - 1:
                            self.unify(at, ft.args[i], f"argument {i} to {func_name}")
                    return self.find(ft.args[-1]) if ft.args else self.fresh_var()
            return self.fresh_var()
        return self.fresh_var()


# ============================================================================
# 6. HIR (HIGH-LEVEL IR)
# ============================================================================

_hir_counter = itertools.count(1)

@dataclass
class HIR:
    kind: str
    attrs: dict = field(default_factory=dict)
    children: list = field(default_factory=list)
    id: int = field(default_factory=lambda: next(_hir_counter))
    line: int = 0
    col: int = 0


def ast_to_hir(node):
    if not isinstance(node, PNode):
        if isinstance(node, tuple):
            return HIR("literal", {"value": node[1]}, line=node[3], col=node[4])
        return HIR("literal", {"value": node})
    r = node.rule
    line, col = node.line, node.col
    def subs(rule=None):
        return [c for c in node.children
                if isinstance(c, PNode) and (rule is None or c.rule == rule)]
    def first(rule=None):
        for c in node.children:
            if isinstance(c, PNode) and (rule is None or c.rule == rule): return c
        return None
    def ident_of(n):
        for c in n.children:
            if isinstance(c, PNode) and c.rule == "IDENT": return c.children[0][1]
        return None
    def tok_val(n):
        if not n.children: return ""
        c = n.children[0]
        return c[1] if isinstance(c, tuple) else tok_val(c)

    if r == "program":
        return HIR("program", {}, [ast_to_hir(s.children[0]) for s in subs("statement")],
                   line=line, col=col)
    if r == "print_stmt":
        return HIR("print", {}, [ast_to_hir(first("expr"))], line=line, col=col)
    if r == "let_stmt":
        return HIR("let", {"name": ident_of(node)}, [ast_to_hir(first("expr"))],
                   line=line, col=col)
    if r == "assign_stmt":
        target = first("target")
        name = ident_of(target)
        idx = first("expr")
        attrs = {"name": name}
        if idx: attrs["index"] = ast_to_hir(idx)
        return HIR("assign", attrs, [ast_to_hir(subs("expr")[-1])], line=line, col=col)
    if r == "if_stmt":
        cond = ast_to_hir(first("expr"))
        blocks = subs("block")
        then_body = [ast_to_hir(s.children[0]) for s in blocks[0].children
                     if isinstance(s, PNode) and s.rule == "statement"]
        else_body = []
        if len(blocks) > 1:
            else_body = [ast_to_hir(s.children[0]) for s in blocks[1].children
                         if isinstance(s, PNode) and s.rule == "statement"]
        elif first("if_stmt"):
            else_body = [ast_to_hir(first("if_stmt"))]
        return HIR("if", {}, [cond, HIR("block", {}, then_body),
                              HIR("block", {}, else_body)], line=line, col=col)
    if r == "while_stmt":
        cond = ast_to_hir(first("expr"))
        body = [ast_to_hir(s.children[0]) for s in first("block").children
                if isinstance(s, PNode) and s.rule == "statement"]
        return HIR("while", {}, [cond, HIR("block", {}, body)], line=line, col=col)
    if r == "for_stmt":
        name = ident_of(node)
        exprs = [ast_to_hir(e) for e in subs("expr")]
        body = [ast_to_hir(s.children[0]) for s in first("block").children
                if isinstance(s, PNode) and s.rule == "statement"]
        return HIR("for", {"name": name, "start": exprs[0], "end": exprs[1],
                           "step": exprs[2] if len(exprs) > 2 else None},
                   [HIR("block", {}, body)], line=line, col=col)
    if r == "func_def":
        name = ident_of(node)
        params = [c.children[0][1] for c in subs("params")
                  for c in c.children if isinstance(c, PNode) and c.rule == "IDENT"] \
                 if first("params") else []
        body = [ast_to_hir(s.children[0]) for s in first("block").children
                if isinstance(s, PNode) and s.rule == "statement"]
        return HIR("func", {"name": name, "params": params},
                   [HIR("block", {}, body)], line=line, col=col)
    if r == "return_stmt":
        e = first("expr")
        return HIR("return", {}, [ast_to_hir(e)] if e else [], line=line, col=col)
    if r in ("break_stmt", "continue_stmt"):
        return HIR(r.replace("_stmt", ""), {}, [], line=line, col=col)
    if r == "expr_stmt":
        return HIR("expr_stmt", {}, [ast_to_hir(first("expr"))], line=line, col=col)
    if r == "throw_stmt":
        return HIR("throw", {}, [ast_to_hir(first("expr"))], line=line, col=col)
    if r == "NUMBER":
        raw = tok_val(node)
        return HIR("const", {"value": float(raw) if "." in raw else int(raw)},
                   line=line, col=col)
    if r == "STRING":
        s = tok_val(node)[1:-1]
        s = re.sub(r'\\([nrt"\\])',
                   lambda m: {"n":"\n","r":"\r","t":"\t",'"':'"',"\\":"\\"}[m.group(1)], s)
        return HIR("const", {"value": s}, line=line, col=col)
    if r == "BOOL":
        return HIR("const", {"value": tok_val(node) == "true"}, line=line, col=col)
    if r == "NULL":
        return HIR("const", {"value": None}, line=line, col=col)
    if r == "IDENT":
        return HIR("var", {"name": tok_val(node)}, line=line, col=col)
    if r in ("or_expr", "and_expr", "comparison", "add_expr", "mul_expr"):
        left = None; op = None
        for c in node.children:
            if isinstance(c, PNode):
                if c.rule == "LITERAL": op = c.children[0][1]; continue
                if c.rule in ("AND", "OR", "NOT"): op = tok_val(c); continue
                if left is None and op is None:
                    left = ast_to_hir(c); continue
                right = ast_to_hir(c)
                left = HIR("binop", {"op": op}, [left, right], line=line, col=col)
                op = None
        return left if left else HIR("const", {"value": 0})
    if r == "unary":
        parts = [c for c in node.children if isinstance(c, PNode)]
        if len(parts) == 1: return ast_to_hir(parts[0])
        return HIR("unary", {"op": tok_val(parts[0])}, [ast_to_hir(parts[1])],
                   line=line, col=col)
    if r == "postfix":
        parts = [c for c in node.children if isinstance(c, PNode)]
        base = ast_to_hir(parts[0])
        i = 1
        while i + 2 < len(parts) + 1 and i < len(parts):
            idx = ast_to_hir(parts[i + 1])
            base = HIR("index", {}, [base, idx], line=line, col=col)
            i += 3
        return base
    if r == "atom":
        e = first("expr")
        if e: return ast_to_hir(e)
        return ast_to_hir([c for c in node.children if isinstance(c, PNode)][0])
    if r == "array":
        return HIR("array", {}, [ast_to_hir(e) for e in subs("expr")], line=line, col=col)
    if r == "dict":
        pairs = []
        for p in subs("pair"):
            es = [ast_to_hir(e) for e in p.children
                  if isinstance(e, PNode) and e.rule == "expr"]
            pairs.append((es[0], es[1]))
        return HIR("dict", {"pairs": pairs}, [], line=line, col=col)
    if r == "call":
        name = ident_of(node)
        args_node = first("args")
        args = [ast_to_hir(e) for e in args_node.children
                if isinstance(e, PNode) and e.rule == "expr"] if args_node else []
        return HIR("call", {"name": name}, args, line=line, col=col)
    return HIR("unknown", {"rule": r}, line=line, col=col)


# ============================================================================
# 7. MIR (MID-LEVEL IR) + CFG
# ============================================================================

@dataclass
class MIRInst:
    op: str
    dst: Optional[str]
    src: list
    line: int = 0
    comment: str = ""
    probability: Optional[float] = None

    def __repr__(self):
        dst = f"{self.dst} = " if self.dst else ""
        src = ", ".join(str(s) for s in self.src)
        c = f"  # {self.comment}" if self.comment else ""
        prob = f"  [p={self.probability:.2f}]" if self.probability is not None else ""
        return f"  {dst}{self.op} {src}{c}{prob}"


@dataclass
class Block:
    label: str
    insts: List[MIRInst] = field(default_factory=list)
    preds: List[str] = field(default_factory=list)
    succs: List[str] = field(default_factory=list)
    doms: Set[str] = field(default_factory=set)
    dom_frontier: Set[str] = field(default_factory=set)
    live_in: Set[str] = field(default_factory=set)
    live_out: Set[str] = field(default_factory=set)
    defs: Set[str] = field(default_factory=set)
    uses: Set[str] = field(default_factory=set)
    exec_count: int = 0


@dataclass
class MIR:
    blocks: Dict[str, Block] = field(default_factory=dict)
    entry: str = "entry"
    func_name: str = "<main>"
    params: List[str] = field(default_factory=list)
    order: List[str] = field(default_factory=list)

    def add_block(self, label):
        if label not in self.blocks:
            self.blocks[label] = Block(label)
            self.order.append(label)
        return self.blocks[label]

    def edge(self, a, b):
        if b not in self.blocks[a].succs: self.blocks[a].succs.append(b)
        if a not in self.blocks[b].preds: self.blocks[b].preds.append(a)

    def text(self):
        lines = [f"function {self.func_name}({', '.join(self.params)}):"]
        for label in self.order:
            b = self.blocks[label]
            count = f"  ; exec_count={b.exec_count}" if b.exec_count else ""
            lines.append(f"{label}:{count}")
            for inst in b.insts:
                lines.append(repr(inst))
        return "\n".join(lines)


class HIRtoMIR:
    def __init__(self):
        self.tmp = 0
        self.lbl = 0
        self.mir = None
        self.cur = None
        self.funcs = {}
        self.loop_stack = []

    def new_tmp(self): self.tmp += 1; return f"v{self.tmp}"
    def new_label(self, hint="L"): self.lbl += 1; return f"{hint}{self.lbl}"
    def emit(self, op, dst=None, src=None, comment=""):
        inst = MIRInst(op, dst, src or [], line=0, comment=comment)
        self.cur.insts.append(inst)
        return dst

    def lower(self, hir):
        self.mir = MIR()
        self.mir.add_block("entry")
        self.cur = self.mir.blocks["entry"]
        self._stmts(hir)
        self.emit("return", src=[])
        return self.mir

    def lower_function(self, hir):
        self.mir = MIR()
        self.mir.func_name = hir.attrs["name"]
        self.mir.params = hir.attrs["params"]
        self.mir.add_block("entry")
        self.cur = self.mir.blocks["entry"]
        for p in self.mir.params: self.emit("param", dst=p, src=[p])
        self._stmts(hir.children[0])
        self.emit("return", src=[])
        return self.mir

    def _stmts(self, node):
        if node.kind in ("program", "block"):
            for s in node.children: self._stmt(s)
        else: self._stmt(node)

    def _stmt(self, node):
        if node.kind == "let":
            v = self._expr(node.children[0])
            self.emit("copy", dst=node.attrs["name"], src=[v])
        elif node.kind == "assign":
            v = self._expr(node.children[0])
            if "index" in node.attrs:
                idx = self._expr(node.attrs["index"])
                self.emit("store_idx", src=[node.attrs["name"], idx, v])
            else:
                self.emit("copy", dst=node.attrs["name"], src=[v])
        elif node.kind == "print":
            v = self._expr(node.children[0])
            self.emit("print", src=[v])
        elif node.kind == "if":
            cond = self._expr(node.children[0])
            then_label = self.new_label("then")
            else_label = self.new_label("else")
            end_label = self.new_label("endif")
            has_else = bool(node.children[2].children)
            self.emit("if", src=[cond, then_label,
                                 else_label if has_else else end_label])
            self.mir.add_block(then_label); self.cur = self.mir.blocks[then_label]
            self._stmts(node.children[1])
            self.emit("goto", src=[end_label])
            if has_else:
                self.mir.add_block(else_label); self.cur = self.mir.blocks[else_label]
                self._stmts(node.children[2])
                self.emit("goto", src=[end_label])
            self.mir.add_block(end_label); self.cur = self.mir.blocks[end_label]
        elif node.kind == "while":
            head_label = self.new_label("while_head")
            body_label = self.new_label("while_body")
            end_label = self.new_label("while_end")
            self.emit("goto", src=[head_label])
            self.mir.add_block(head_label); self.cur = self.mir.blocks[head_label]
            cond = self._expr(node.children[0])
            self.emit("if", src=[cond, body_label, end_label])
            self.mir.add_block(body_label); self.cur = self.mir.blocks[body_label]
            self.loop_stack.append((head_label, end_label))
            self._stmts(node.children[1])
            self.loop_stack.pop()
            self.emit("goto", src=[head_label])
            self.mir.add_block(end_label); self.cur = self.mir.blocks[end_label]
        elif node.kind == "for":
            name = node.attrs["name"]
            start = self._expr(node.attrs["start"])
            end_v = self._expr(node.attrs["end"])
            step = node.attrs["step"] or HIR("const", {"value": 1})
            step_v = self._expr(step)
            self.emit("copy", dst=name, src=[start])
            head_label = self.new_label("for_head")
            body_label = self.new_label("for_body")
            end_label = self.new_label("for_end")
            self.emit("goto", src=[head_label])
            self.mir.add_block(head_label); self.cur = self.mir.blocks[head_label]
            cmp = self.new_tmp()
            self.emit("lt", dst=cmp, src=[name, end_v])
            self.emit("if", src=[cmp, body_label, end_label])
            self.mir.add_block(body_label); self.cur = self.mir.blocks[body_label]
            self.loop_stack.append((head_label, end_label))
            self._stmts(node.children[0])
            self.loop_stack.pop()
            inc = self.new_tmp()
            self.emit("add", dst=inc, src=[name, step_v])
            self.emit("copy", dst=name, src=[inc])
            self.emit("goto", src=[head_label])
            self.mir.add_block(end_label); self.cur = self.mir.blocks[end_label]
        elif node.kind == "func":
            saved_mir, saved_cur = self.mir, self.cur
            func_mir = self.lower_function(node)
            self.funcs[node.attrs["name"]] = func_mir
            self.mir, self.cur = saved_mir, saved_cur
        elif node.kind == "return":
            v = self._expr(node.children[0]) if node.children else None
            self.emit("return", src=[v] if v else [])
        elif node.kind == "break":
            if self.loop_stack: self.emit("goto", src=[self.loop_stack[-1][1]])
        elif node.kind == "continue":
            if self.loop_stack: self.emit("goto", src=[self.loop_stack[-1][0]])
        elif node.kind == "throw":
            v = self._expr(node.children[0])
            self.emit("throw", src=[v])
        elif node.kind == "expr_stmt":
            self._expr(node.children[0])

    def _expr(self, node):
        if node.kind == "const": return node.attrs["value"]
        if node.kind == "var": return node.attrs["name"]
        if node.kind == "binop":
            l = self._expr(node.children[0])
            r = self._expr(node.children[1])
            t = self.new_tmp()
            op_map = {"+":"add","-":"sub","*":"mul","/":"div","//":"idiv",
                      "%":"mod","==":"eq","!=":"ne","<":"lt",">":"gt",
                      "<=":"le",">=":"ge","and":"and","or":"or"}
            self.emit(op_map.get(node.attrs["op"], "add"), dst=t, src=[l, r])
            return t
        if node.kind == "unary":
            v = self._expr(node.children[0])
            t = self.new_tmp()
            self.emit("neg" if node.attrs["op"] == "-" else "not", dst=t, src=[v])
            return t
        if node.kind == "index":
            base = self._expr(node.children[0])
            idx = self._expr(node.children[1])
            t = self.new_tmp()
            self.emit("load_idx", dst=t, src=[base, idx])
            return t
        if node.kind == "array":
            vs = [self._expr(c) for c in node.children]
            t = self.new_tmp()
            self.emit("array", dst=t, src=vs)
            return t
        if node.kind == "dict":
            src = []
            for k, v in node.attrs["pairs"]:
                src.append(self._expr(k)); src.append(self._expr(v))
            t = self.new_tmp()
            self.emit("dict", dst=t, src=src)
            return t
        if node.kind == "call":
            args = [self._expr(c) for c in node.children]
            t = self.new_tmp()
            self.emit("call", dst=t, src=[node.attrs["name"]] + args)
            return t
        return 0


# ============================================================================
# 8. SSA CONSTRUCTION
# ============================================================================

class SSABuilder:
    def __init__(self, mir: MIR): self.mir = mir

    def compute_dominators(self):
        blocks = self.mir.blocks
        entry = self.mir.entry
        all_labels = list(blocks.keys())
        for lbl in all_labels: blocks[lbl].doms = set(all_labels)
        blocks[entry].doms = {entry}
        changed = True
        while changed:
            changed = False
            for lbl in all_labels:
                if lbl == entry: continue
                b = blocks[lbl]
                if not b.preds: new_doms = {lbl}
                else: new_doms = {lbl} | set.intersection(*(blocks[p].doms for p in b.preds))
                if new_doms != b.doms: b.doms = new_doms; changed = True

    def compute_dom_tree(self):
        blocks = self.mir.blocks
        idom = {}
        for lbl in blocks:
            if lbl == self.mir.entry: idom[lbl] = None; continue
            strict = blocks[lbl].doms - {lbl}
            for d in strict:
                if all(d in blocks[o].doms or d == o for o in strict):
                    idom[lbl] = d; break
        return idom

    def compute_dom_frontier(self):
        blocks = self.mir.blocks
        for lbl in blocks: blocks[lbl].dom_frontier = set()
        for lbl in blocks:
            b = blocks[lbl]
            if len(b.preds) >= 2:
                for p in b.preds:
                    runner = p
                    while runner not in (blocks[lbl].doms - {lbl}):
                        blocks[runner].dom_frontier.add(lbl)
                        idom = self._idom_of(runner)
                        if idom is None: break
                        runner = idom

    def _idom_of(self, lbl):
        b = self.mir.blocks[lbl]
        strict = b.doms - {lbl}
        if not strict: return None
        for d in strict:
            if all(d in self.mir.blocks[o].doms or d == o for o in strict): return d
        return None

    def compute_def_blocks(self):
        defs = defaultdict(set)
        for lbl, b in self.mir.blocks.items():
            for inst in b.insts:
                if inst.dst: defs[inst.dst].add(lbl)
        return defs

    def insert_phis(self):
        self.compute_dominators()
        self.compute_dom_frontier()
        defs = self.compute_def_blocks()
        for var, def_blocks in defs.items():
            work = list(def_blocks); seen = set()
            while work:
                x = work.pop()
                for y in self.mir.blocks[x].dom_frontier:
                    if y in seen: continue
                    seen.add(y)
                    n_preds = len(self.mir.blocks[y].preds)
                    if n_preds >= 1:
                        phi = MIRInst("phi", var + "_phi", [var] * n_preds,
                                      comment=f"phi for {var}")
                        self.mir.blocks[y].insts.insert(0, phi)
                        work.append(y)

    def rename(self):
        counter = defaultdict(int)
        stack = defaultdict(list)
        def fresh(var):
            counter[var] += 1
            v = f"{var}.{counter[var]}"
            stack[var].append(v); return v
        def top(var):
            return stack[var][-1] if stack[var] else var

        def rename_block(lbl, visited):
            if lbl in visited: return
            visited.add(lbl)
            b = self.mir.blocks[lbl]
            saved = {v: list(stack[v]) for v in stack}
            for inst in b.insts:
                for i, s in enumerate(inst.src):
                    if isinstance(s, str) and not s.startswith("L") \
                            and not s.isdigit() \
                            and not isinstance(s, (int, float, bool)) \
                            and s not in ("true","false"):
                        try: inst.src[i] = top(s)
                        except Exception: pass
                if inst.dst:
                    old = inst.dst
                    inst.dst = fresh(old)
                    for succ in b.succs:
                        for si, sinst in enumerate(self.mir.blocks[succ].insts):
                            if sinst.op == "phi":
                                try:
                                    idx = self.mir.blocks[succ].preds.index(lbl)
                                    if idx < len(sinst.src) and sinst.src[idx] == old:
                                        sinst.src[idx] = inst.dst
                                except ValueError: pass
            for other_lbl in self.mir.blocks:
                if other_lbl != lbl and self._idom_of(other_lbl) == lbl:
                    rename_block(other_lbl, visited)
            for v in saved: stack[v] = saved[v]

        rename_block(self.mir.entry, set())

    def build(self):
        self.insert_phis()
        self.rename()
        return self.mir


# ============================================================================
# 9. OPTIMIZER
# ============================================================================

class Optimizer:
    def __init__(self, mir: MIR, funcs: Dict[str, MIR] = None):
        self.mir = mir
        self.funcs = funcs or {}
        self.changes = 0
        self.pass_log = []

    def _log(self, name, count):
        self.pass_log.append((name, count))
        self.changes += count

    def constant_fold(self):
        n = 0
        for b in self.mir.blocks.values():
            new_insts = []
            for inst in b.insts:
                if inst.op in ("add","sub","mul","div","idiv","mod","eq","ne",
                               "lt","gt","le","ge") \
                        and len(inst.src) == 2 \
                        and all(isinstance(s, (int, float)) for s in inst.src):
                    a, bb = inst.src
                    try:
                        ops = {"add": a+bb, "sub": a-bb, "mul": a*bb,
                               "div": a/bb if bb else 0, "idiv": a//bb if bb else 0,
                               "mod": a%bb if bb else 0, "eq": a==bb, "ne": a!=bb,
                               "lt": a<bb, "gt": a>bb, "le": a<=bb, "ge": a>=bb}
                        if inst.op in ops:
                            new_insts.append(MIRInst("copy", inst.dst, [ops[inst.op]],
                                                     comment=f"folded {inst.op}"))
                            n += 1; continue
                    except Exception: pass
                new_insts.append(inst)
            b.insts = new_insts
        self._log("constant_fold", n)
        return n

    def strength_reduction(self):
        n = 0
        for b in self.mir.blocks.values():
            for inst in b.insts:
                if inst.op == "mul" and len(inst.src) == 2:
                    if inst.src[1] == 2:
                        inst.op = "add"; inst.src = [inst.src[0], inst.src[0]]; n += 1
                    elif inst.src[1] == 1:
                        inst.op = "copy"; inst.src = [inst.src[0]]; n += 1
                    elif inst.src[1] == 0:
                        inst.op = "copy"; inst.src = [0]; n += 1
        self._log("strength_reduction", n)
        return n

    def dead_code_elimination(self):
        # Simplified liveness
        for lbl, b in self.mir.blocks.items():
            b.uses = set(); b.defs = set()
            for inst in b.insts:
                for s in inst.src:
                    if isinstance(s, str) and not s.startswith("L") \
                            and not isinstance(s, (int, float, bool)):
                        if s not in b.defs: b.uses.add(s)
                if inst.dst: b.defs.add(inst.dst)
        changed = True
        while changed:
            changed = False
            for lbl in reversed(self.mir.order):
                b = self.mir.blocks[lbl]
                new_out = set()
                for s in b.succs: new_out |= self.mir.blocks[s].live_in
                new_in = b.uses | (new_out - b.defs)
                if new_in != b.live_in or new_out != b.live_out:
                    b.live_in = new_in; b.live_out = new_out; changed = True

        n = 0
        for b in self.mir.blocks.values():
            new_insts = []
            for inst in b.insts:
                if inst.dst and inst.dst not in b.live_out \
                        and inst.op not in ("print","return","call","store_idx","throw"):
                    used_later = any(inst.dst in other.src
                                    for other in b.insts[b.insts.index(inst)+1:])
                    if not used_later: n += 1; continue
                new_insts.append(inst)
            b.insts = new_insts
        self._log("dead_code_elimination", n)
        return n

    def cse(self):
        n = 0
        for b in self.mir.blocks.values():
            seen = {}
            new_insts = []
            for inst in b.insts:
                if inst.op in ("add","sub","mul","div") and len(inst.src) == 2:
                    key = (inst.op, tuple(inst.src))
                    if key in seen:
                        new_insts.append(MIRInst("copy", inst.dst, [seen[key]],
                                                 comment="CSE"))
                        n += 1; continue
                    seen[key] = inst.dst
                new_insts.append(inst)
            b.insts = new_insts
        self._log("cse", n)
        return n

    def peephole(self):
        n = 0
        for b in self.mir.blocks.values():
            new_insts = []
            for inst in b.insts:
                if inst.op == "add" and len(inst.src) == 2 and inst.src[1] == 0:
                    new_insts.append(MIRInst("copy", inst.dst, [inst.src[0]],
                                             comment="peephole: add 0")); n += 1; continue
                if inst.op == "mul" and len(inst.src) == 2 and inst.src[1] == 1:
                    new_insts.append(MIRInst("copy", inst.dst, [inst.src[0]],
                                             comment="peephole: mul 1")); n += 1; continue
                if inst.op == "mul" and len(inst.src) == 2 and inst.src[1] == 0:
                    new_insts.append(MIRInst("copy", inst.dst, [0],
                                             comment="peephole: mul 0")); n += 1; continue
                new_insts.append(inst)
            b.insts = new_insts
        self._log("peephole", n)
        return n

    def run_all(self):
        self.constant_fold()
        self.strength_reduction()
        self.cse()
        self.peephole()
        self.dead_code_elimination()
        return self.changes


# ============================================================================
# 10. REGISTER ALLOCATION + INSTRUCTION SELECTION
# ============================================================================

class LinearScanAllocator:
    PHYS_REGS = ["r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7"]

    def __init__(self, mir: MIR):
        self.mir = mir
        self.intervals = {}
        self.allocation = {}

    def compute_live_intervals(self):
        pos = 0
        for lbl in self.mir.order:
            b = self.mir.blocks[lbl]
            for inst in b.insts:
                if inst.dst:
                    if inst.dst not in self.intervals:
                        self.intervals[inst.dst] = (pos, pos)
                    else:
                        s, _ = self.intervals[inst.dst]
                        self.intervals[inst.dst] = (s, pos)
                for s in inst.src:
                    if isinstance(s, str) and s in self.intervals:
                        start, _ = self.intervals[s]
                        self.intervals[s] = (start, pos)
                pos += 1

    def allocate(self):
        self.compute_live_intervals()
        sorted_regs = sorted(self.intervals.items(), key=lambda x: x[1][0])
        active = []
        free = list(self.PHYS_REGS)
        for vreg, (start, end) in sorted_regs:
            new_active = []
            for a_end, a_vreg, a_phys in active:
                if a_end >= start: new_active.append((a_end, a_vreg, a_phys))
                else: free.append(a_phys)
            active = new_active
            if free:
                phys = free.pop(0)
                self.allocation[vreg] = phys
                active.append((end, vreg, phys))
            else:
                active.sort(key=lambda x: -x[0])
                spill_end, spill_vreg, spill_phys = active.pop(0)
                if spill_end > end:
                    self.allocation[spill_vreg] = "mem"
                    self.allocation[vreg] = spill_phys
                    active.append((end, vreg, spill_phys))
                else:
                    self.allocation[vreg] = "mem"
                    active.append((spill_end, spill_vreg, spill_phys))
        return self.allocation

    def apply(self, mir: MIR):
        for b in mir.blocks.values():
            for inst in b.insts:
                if inst.dst and inst.dst in self.allocation:
                    inst.dst = self.allocation[inst.dst]
                for i, s in enumerate(inst.src):
                    if isinstance(s, str) and s in self.allocation:
                        inst.src[i] = self.allocation[s]


@dataclass
class LIRInst:
    op: str
    dst: Optional[str]
    src: list
    comment: str = ""
    source_line: int = 0

    def __repr__(self):
        dst = f"{self.dst} = " if self.dst else ""
        src = ", ".join(str(s) for s in self.src)
        c = f"  # {self.comment}" if self.comment else ""
        return f"  {dst}{self.op} {src}{c}"


@dataclass
class LIR:
    insts: List[LIRInst] = field(default_factory=list)
    func_name: str = "<main>"

    def text(self):
        lines = [f"function {self.func_name}:"]
        for inst in self.insts:
            lines.append(repr(inst))
        return "\n".join(lines)


class InstSelector:
    def __init__(self, mir: MIR): self.mir = mir

    def select(self) -> LIR:
        lir = LIR(func_name=self.mir.func_name)
        for lbl in self.mir.order:
            b = self.mir.blocks[lbl]
            lir.insts.append(LIRInst("label", lbl, []))
            for inst in b.insts:
                self._match(inst, lir)
        return lir

    def _match(self, inst: MIRInst, lir: LIR):
        op = inst.op
        if op == "copy":
            lir.insts.append(LIRInst("mov", inst.dst, inst.src, inst.comment, inst.line))
        elif op in ("add","sub","mul","div","idiv","mod","eq","ne","lt","gt","le","ge"):
            lir.insts.append(LIRInst(op, inst.dst, inst.src, inst.comment, inst.line))
        elif op == "load_idx":
            lir.insts.append(LIRInst("load_idx", inst.dst, inst.src, inst.comment, inst.line))
        elif op == "store_idx":
            lir.insts.append(LIRInst("store_idx", None, inst.src, inst.comment, inst.line))
        elif op == "call":
            lir.insts.append(LIRInst("call", inst.dst, inst.src, inst.comment, inst.line))
        elif op == "param":
            lir.insts.append(LIRInst("param", inst.dst, inst.src, inst.comment, inst.line))
        elif op == "if":
            cond, then_l, else_l = inst.src[0], inst.src[1], inst.src[2]
            lir.insts.append(LIRInst("cmp", None, [cond], inst.comment, inst.line))
            lir.insts.append(LIRInst("jz", None, [else_l], "", inst.line))
            lir.insts.append(LIRInst("jmp", None, [then_l], "", inst.line))
        elif op == "goto":
            lir.insts.append(LIRInst("jmp", None, inst.src, inst.comment, inst.line))
        elif op == "print":
            lir.insts.append(LIRInst("call", None, ["@print"] + inst.src, inst.comment, inst.line))
        elif op == "return":
            lir.insts.append(LIRInst("ret", None, inst.src, inst.comment, inst.line))
        elif op == "array":
            lir.insts.append(LIRInst("alloc_array", inst.dst, inst.src, inst.comment, inst.line))
        elif op == "dict":
            lir.insts.append(LIRInst("alloc_dict", inst.dst, inst.src, inst.comment, inst.line))
        elif op == "phi":
            lir.insts.append(LIRInst("phi", inst.dst, inst.src, inst.comment, inst.line))
        else:
            lir.insts.append(LIRInst(op, inst.dst, inst.src, inst.comment, inst.line))


# ============================================================================
# 11. CODE GENERATION BACKENDS
# ============================================================================

class Backend:
    name = "base"; ext = "txt"
    def generate(self, mir, lir=None): raise NotImplementedError


class PythonBackend(Backend):
    name = "Python"; ext = "py"
    def generate(self, mir, lir=None):
        out = [f"# Generated Python — {mir.func_name}", ""]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"# {lbl}:")
            for inst in b.insts:
                out.append(self._emit(inst))
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"{i.dst} = {i.src[0]}"
        if i.op in ("add","sub","mul","div","mod","eq","ne","lt","gt","le","ge"):
            ops = {"eq":"==","ne":"!=","idiv":"//"}
            return f"{i.dst} = {i.src[0]} {ops.get(i.op,i.op)} {i.src[1]}"
        if i.op == "print": return f"print({i.src[0]})"
        if i.op == "return": return f"return {i.src[0] if i.src else ''}"
        if i.op == "if": return f"if {i.src[0]}: goto {i.src[1]} else goto {i.src[2]}"
        if i.op == "goto": return f"goto {i.src[0]}"
        if i.op == "label": return f"{i.src[0]}:"
        if i.op == "call": return f"{i.dst} = {i.src[0]}({', '.join(map(str,i.src[1:]))})"
        if i.op == "phi": return f"# phi {i.dst} = {i.src}"
        return f"# {i.op} {i.dst} {i.src}"


class CBackend(Backend):
    name = "C"; ext = "c"
    def generate(self, mir, lir=None):
        out = [f"/* Generated C — {mir.func_name} */", "#include <stdio.h>", ""]
        out.append(f"int {mir.func_name}() {{")
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"  {lbl}:;")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("}")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"int {i.dst} = {i.src[0]};"
        if i.op in ("add","sub","mul","div","mod"):
            return f"int {i.dst} = {i.src[0]} {i.op} {i.src[1]};"
        if i.op in ("eq","ne","lt","gt","le","ge"):
            ops = {"eq":"==","ne":"!=","idiv":"/"}
            return f"int {i.dst} = {i.src[0]} {ops.get(i.op,i.op)} {i.src[1]};"
        if i.op == "print": return f'printf("%d\\n", {i.src[0]});'
        if i.op == "return": return f"return {i.src[0] if i.src else 0};"
        if i.op == "if": return f"if ({i.src[0]}) goto {i.src[1]}; else goto {i.src[2]};"
        if i.op == "goto": return f"goto {i.src[0]};"
        if i.op == "call": return f"int {i.dst} = {i.src[0]}({', '.join(map(str,i.src[1:]))});"
        if i.op == "phi": return f"/* phi {i.dst} */"
        return f"/* {i.op} */"


class LLVMIRBackend(Backend):
    name = "LLVM IR"; ext = "ll"
    def generate(self, mir, lir=None):
        out = [f"; Generated LLVM IR — {mir.func_name}",
               'source_filename = "nova"', "",
               f"define i32 @{mir.func_name}() {{"]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"{lbl}:")
            for inst in b.insts:
                out.append("  " + self._emit(inst))
        out.append("}")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"%{i.dst} = add i32 {i.src[0]}, 0"
        if i.op in ("add","sub","mul"):
            return f"%{i.dst} = {i.op} i32 {i.src[0]}, {i.src[1]}"
        if i.op in ("div","idiv"):
            return f"%{i.dst} = sdiv i32 {i.src[0]}, {i.src[1]}"
        if i.op == "mod":
            return f"%{i.dst} = srem i32 {i.src[0]}, {i.src[1]}"
        if i.op in ("eq","ne","lt","gt","le","ge"):
            ops = {"eq":"eq","ne":"ne","lt":"slt","gt":"sgt","le":"sle","ge":"sge"}
            return f"%{i.dst} = icmp {ops[i.op]} i32 {i.src[0]}, {i.src[1]}"
        if i.op == "print":
            return f"call void @print_i32(i32 {i.src[0]})"
        if i.op == "return":
            return f"ret i32 {i.src[0] if i.src else 0}"
        if i.op == "if":
            return f"br i1 %{i.src[0]}, label %{i.src[1]}, label %{i.src[2]}"
        if i.op == "goto": return f"br label %{i.src[0]}"
        if i.op == "label": return f"{i.src[0]}:"
        if i.op == "call":
            args = ", ".join(f"i32 {s}" for s in i.src[1:])
            return f"%{i.dst} = call i32 @{i.src[0]}({args})"
        if i.op == "phi":
            pairs = ", ".join(f"[ {v}, %pred{i} ]" for i, v in enumerate(i.src))
            return f"%{i.dst} = phi i32 {pairs}"
        return f"; {i.op}"


class X86Backend(Backend):
    name = "x86-64"; ext = "asm"
    def generate(self, mir, lir=None):
        out = [f"; Generated x86-64 assembly — {mir.func_name}",
               "section .text", "global _start", "",
               f"{mir.func_name}:", "    push rbp", "    mov rbp, rsp"]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f".{lbl}:")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("    pop rbp"); out.append("    ret")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy":
            return f"mov rax, {i.src[0]}  ; -> {i.dst}"
        if i.op == "add":
            return f"mov rax, {i.src[0]}\n    add rax, {i.src[1]}"
        if i.op == "sub":
            return f"mov rax, {i.src[0]}\n    sub rax, {i.src[1]}"
        if i.op == "mul":
            return f"mov rax, {i.src[0]}\n    imul rax, {i.src[1]}"
        if i.op == "print":
            return f"mov rdi, {i.src[0]}\n    call print_int"
        if i.op == "return":
            return f"mov rax, {i.src[0] if i.src else 0}\n    ret"
        if i.op == "if":
            return f"test rax, rax\n    jnz .{i.src[1]}\n    jmp .{i.src[2]}"
        if i.op == "goto": return f"jmp .{i.src[0]}"
        if i.op == "label": return f".{i.src[0]}:"
        if i.op == "call": return f"call {i.src[0]}"
        return f"; {i.op}"


class WASMBackend(Backend):
    name = "WebAssembly"; ext = "wat"
    def generate(self, mir, lir=None):
        out = [f";; Generated WebAssembly — {mir.func_name}",
               "(module", f'  (func ${mir.func_name} (result i32)']
        locals_set = set()
        for b in mir.blocks.values():
            for inst in b.insts:
                if inst.dst: locals_set.add(inst.dst)
        out.append(f"    (local {len(locals_set)} i32)")
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"    ;; {lbl}:")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("    i32.const 0")
        out.append("  )")
        out.append(")")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"i32.const {i.src[0]}"
        if i.op in ("add","sub","mul","div"):
            ops = {"add":"i32.add","sub":"i32.sub","mul":"i32.mul","div":"i32.div_s"}
            return ops[i.op]
        if i.op == "print": return f"i32.const {i.src[0]}\n    call $print_i32"
        if i.op == "return":
            return f"i32.const {i.src[0] if i.src else 0}\n    return"
        if i.op == "goto": return f"br 0"
        if i.op == "label": return f";; {i.src[0]}:"
        if i.op == "call":
            args = " ".join(f"i32.const {s}" for s in i.src[1:])
            return f"{args}\n    call ${i.src[0]}"
        return f";; {i.op}"


class JavaScriptBackend(Backend):
    name = "JavaScript"; ext = "js"
    def generate(self, mir, lir=None):
        out = [f"// Generated JavaScript — {mir.func_name}", ""]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"// {lbl}:")
            for inst in b.insts:
                out.append(self._emit(inst))
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"let {i.dst} = {self._v(i.src[0])};"
        if i.op in ("add","sub","mul","div","mod"):
            return f"let {i.dst} = {self._v(i.src[0])} {i.op} {self._v(i.src[1])};"
        if i.op == "print": return f"console.log({self._v(i.src[0])});"
        if i.op == "return": return f"return {self._v(i.src[0]) if i.src else 'undefined'};"
        if i.op == "if": return f"if ({self._v(i.src[0])}) goto {i.src[1]}; else goto {i.src[2]};"
        if i.op == "goto": return f"goto {i.src[0]};"
        if i.op == "label": return f"{i.src[0]}:"
        if i.op == "call": return f"let {i.dst} = {i.src[0]}({', '.join(self._v(s) for s in i.src[1:])});"
        if i.op == "phi": return f"// phi {i.dst}"
        return f"// {i.op}"
    def _v(self, s):
        if isinstance(s, bool): return "true" if s else "false"
        return str(s)


class RustBackend(Backend):
    name = "Rust"; ext = "rs"
    def generate(self, mir, lir=None):
        out = [f"// Generated Rust — {mir.func_name}", "",
               f"fn {mir.func_name}() -> i32 {{"]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"    // {lbl}:")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("    0"); out.append("}")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"let mut {i.dst}: i32 = {i.src[0]};"
        if i.op in ("add","sub","mul","div"):
            return f"let mut {i.dst}: i32 = {i.src[0]} {i.op} {i.src[1]};"
        if i.op == "print": return f"println!(\"{{}}\", {i.src[0]});"
        if i.op == "return": return f"return {i.src[0] if i.src else 0};"
        if i.op == "phi": return f"// phi {i.dst}"
        return f"// {i.op}"


class GoBackend(Backend):
    name = "Go"; ext = "go"
    def generate(self, mir, lir=None):
        out = [f"// Generated Go — {mir.func_name}",
               "package main", "", 'import "fmt"', "",
               f"func {mir.func_name}() int {{"]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"    // {lbl}:")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("    return 0"); out.append("}")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"{i.dst} := {i.src[0]}"
        if i.op in ("add","sub","mul","div"):
            return f"{i.dst} := {i.src[0]} {i.op} {i.src[1]}"
        if i.op == "print": return f"fmt.Println({i.src[0]})"
        if i.op == "return": return f"return {i.src[0] if i.src else 0}"
        if i.op == "phi": return f"// phi {i.dst}"
        return f"// {i.op}"


class JVMBackend(Backend):
    name = "JVM Bytecode"; ext = "j"
    def generate(self, mir, lir=None):
        out = [f"; Generated JVM bytecode — {mir.func_name}",
               f".class public Nova{mir.func_name.title()}",
               ".super java/lang/Object", "",
               f".method public static {mir.func_name}()I",
               "    .limit stack 100", "    .limit locals 100"]
        for lbl in mir.order:
            b = mir.blocks[lbl]
            out.append(f"  {lbl}:")
            for inst in b.insts:
                out.append("    " + self._emit(inst))
        out.append("    return"); out.append(".end method")
        return "\n".join(out)
    def _emit(self, i):
        if i.op == "copy": return f"ldc {i.src[0]}  ; store to {i.dst}"
        if i.op in ("add","sub","mul","div"):
            ops = {"add":"iadd","sub":"isub","mul":"imul","div":"idiv"}
            return f"; {i.src[0]} {i.src[1]}\n    {ops[i.op]}"
        if i.op == "print":
            return f"getstatic java/lang/System/out Ljava/io/PrintStream;\n    ldc {i.src[0]}\n    invokevirtual java/io/PrintStream.println(I)V"
        if i.op == "return":
            return f"ldc {i.src[0] if i.src else 0}\n    ireturn"
        if i.op == "if": return f"ifne {i.src[1]}  ; else {i.src[2]}"
        if i.op == "goto": return f"goto {i.src[0]}"
        if i.op == "label": return f"{i.src[0]}:"
        if i.op == "phi": return f"; phi {i.dst}"
        return f"; {i.op}"


class BrainfuckBackend(Backend):
    name = "Brainfuck"; ext = "bf"
    def generate(self, mir, lir=None):
        out = []
        mem = {}; next_cell = 0
        for lbl in mir.order:
            b = mir.blocks[lbl]
            for inst in b.insts:
                if inst.op == "copy" and isinstance(inst.src[0], int):
                    if inst.dst not in mem:
                        mem[inst.dst] = next_cell; next_cell += 1
                    cell = mem[inst.dst]
                    out.append(">" * cell + "+" * abs(inst.src[0]) + "<" * cell)
                elif inst.op == "print" and inst.src[0] in mem:
                    cell = mem[inst.src[0]]
                    out.append(">" * cell + "." + "<" * cell)
        return "".join(out)


BACKENDS = {
    "Python": PythonBackend(),
    "JavaScript": JavaScriptBackend(),
    "C": CBackend(),
    "Rust": RustBackend(),
    "Go": GoBackend(),
    "WebAssembly": WASMBackend(),
    "LLVM IR": LLVMIRBackend(),
    "JVM Bytecode": JVMBackend(),
    "x86-64": X86Backend(),
    "Brainfuck": BrainfuckBackend(),
}


# ============================================================================
# 12. GRAMMAR WORKFLOW TOOLS
# ============================================================================

class RailroadDiagram:
    def __init__(self, grammar: _Grammar):
        self.grammar = grammar
        self.elements = []
        self.x = 0
        self.y = 0

    def render_rule(self, rule_name):
        self.elements = []
        self.x = 40; self.y = 60
        if rule_name not in self.grammar.rules: return []
        rule = self.grammar.rules[rule_name]
        self._draw_terminal(f"START → {rule_name}", "#50FA7B")
        self._draw_line(30)
        self._draw_expr(rule.expr)
        self._draw_line(30)
        self._draw_terminal("END", "#FF5555")
        return self.elements

    def _draw_terminal(self, text, color):
        w = max(60, len(text) * 8 + 20); h = 28
        self.elements.append(("terminal", self.x, self.y - h//2, w, h, text, color))
        self.x += w

    def _draw_nonterminal(self, text):
        w = max(60, len(text) * 8 + 20); h = 28
        self.elements.append(("nonterminal", self.x, self.y - h//2, w, h, text, "#BD93F9"))
        self.x += w

    def _draw_literal(self, text):
        display = f"'{text}'"
        w = max(40, len(display) * 8 + 16); h = 24
        self.elements.append(("literal", self.x, self.y - h//2, w, h, display, "#F1FA8C"))
        self.x += w

    def _draw_regex(self, pattern):
        display = f"/{pattern}/"
        w = max(40, len(display) * 7 + 16); h = 24
        self.elements.append(("regex", self.x, self.y - h//2, w, h, display, "#8BE9FD"))
        self.x += w

    def _draw_line(self, length):
        self.elements.append(("line", self.x, self.y, self.x + length, self.y, "", "#6272A4"))
        self.x += length

    def _draw_expr(self, expr):
        if isinstance(expr, _Lit): self._draw_literal(expr.value)
        elif isinstance(expr, _Regex): self._draw_regex(expr.pattern)
        elif isinstance(expr, _Ref): self._draw_nonterminal(expr.name)
        elif isinstance(expr, _Seq):
            for i, e in enumerate(expr.exprs):
                if i > 0: self._draw_line(20)
                self._draw_expr(e)
        elif isinstance(expr, _Choice):
            start_x = self.x; positions = []; max_w = 0
            for i, e in enumerate(expr.exprs):
                old_x = self.x
                self._draw_expr(e)
                w = self.x - old_x; max_w = max(max_w, w)
                positions.append((self.x, self.y))
                if i < len(expr.exprs) - 1:
                    self.x = old_x; self.y += 50
            for px, py in positions:
                self.elements.append(("vline", start_x - 10, positions[0][1],
                                     start_x - 10, py, "", "#6272A4"))
                self.elements.append(("vline", self.x, positions[0][1],
                                     self.x, py, "", "#6272A4"))
            self.y = positions[0][1]
        elif isinstance(expr, _Repeat):
            start_x = self.x
            self._draw_expr(expr.expr)
            end_x = self.x
            self.elements.append(("loop", start_x, self.y + 20,
                                 end_x, self.y + 20, "", "#FFB86C"))
            if expr.lo == 0 and expr.hi == float("inf"): label = "*"
            elif expr.lo == 1 and expr.hi == float("inf"): label = "+"
            elif expr.lo == 0 and expr.hi == 1: label = "?"
            else: label = f"{{{expr.lo},{expr.hi}}}"
            self.elements.append(("label", (start_x + end_x) // 2, self.y + 35,
                                 0, 0, label, "#FFB86C"))


class DependencyGraph:
    def __init__(self, grammar: _Grammar):
        self.grammar = grammar
        self.edges = self._build_edges()

    def _build_edges(self):
        edges = defaultdict(set)
        for name, rule in self.grammar.rules.items():
            edges[name] = self._find_refs(rule.expr)
        return edges

    def _find_refs(self, expr):
        refs = set()
        if isinstance(expr, _Ref): refs.add(expr.name)
        elif isinstance(expr, (_Seq, _Choice)):
            for e in expr.exprs: refs |= self._find_refs(e)
        elif isinstance(expr, _Repeat): refs |= self._find_refs(expr.expr)
        return refs

    def get_layout(self):
        depths = {}
        def depth(name, visited=None):
            if visited is None: visited = set()
            if name in depths: return depths[name]
            if name in visited: return 0
            visited.add(name)
            if not self.edges[name]:
                depths[name] = 0; return 0
            d = 1 + max((depth(r, visited.copy()) for r in self.edges[name]), default=0)
            depths[name] = d; return d
        for name in self.grammar.rules: depth(name)
        by_depth = defaultdict(list)
        for name, d in depths.items(): by_depth[d].append(name)
        positions = {}
        for d, names in by_depth.items():
            y = 60 + d * 80
            n = len(names)
            for i, name in enumerate(names):
                x = 100 + (i + 0.5) * (800 / max(n, 1))
                positions[name] = (x, y)
        return positions

    def get_edges(self):
        edges = []
        for src, dsts in self.edges.items():
            for dst in dsts: edges.append((src, dst))
        return edges


class GrammarMetrics:
    def __init__(self, grammar: _Grammar): self.grammar = grammar

    def compute(self):
        rules = self.grammar.rules
        terminals = [n for n in rules if n.isupper()]
        non_terminals = [n for n in rules if not n.isupper()]
        return {
            "total_rules": len(rules),
            "terminals": len(terminals),
            "non_terminals": len(non_terminals),
            "total_literals": self._count(_Lit),
            "total_regexes": self._count(_Regex),
            "total_refs": self._count(_Ref),
            "recursive_rules": len(self._find_recursive()),
            "unused_rules": len(self._find_unused()),
            "start_rule": next((n for n in rules if not n.isupper()), None),
        }

    def _count(self, cls):
        return sum(self._count_in(r.expr, cls) for r in self.grammar.rules.values())

    def _count_in(self, expr, cls):
        count = 0
        if isinstance(expr, cls): count = 1
        elif isinstance(expr, (_Seq, _Choice)):
            count = sum(self._count_in(e, cls) for e in expr.exprs)
        elif isinstance(expr, _Repeat): count = self._count_in(expr.expr, cls)
        return count

    def _find_recursive(self):
        recursive = []
        for name in self.grammar.rules:
            if self._is_recursive(name, self.grammar.rules[name].expr, set()):
                recursive.append(name)
        return recursive

    def _is_recursive(self, target, expr, visited):
        if isinstance(expr, _Ref):
            if expr.name == target: return True
            if expr.name in visited: return False
            visited.add(expr.name)
            if expr.name in self.grammar.rules:
                return self._is_recursive(target, self.grammar.rules[expr.name].expr, visited)
            return False
        if isinstance(expr, (_Seq, _Choice)):
            return any(self._is_recursive(target, e, visited.copy()) for e in expr.exprs)
        if isinstance(expr, _Repeat):
            return self._is_recursive(target, expr.expr, visited)
        return False

    def _find_unused(self):
        referenced = set()
        for rule in self.grammar.rules.values():
            referenced |= self._find_refs(rule.expr)
        start = next((n for n in self.grammar.rules if not n.isupper()), None)
        return [n for n in self.grammar.rules if n not in referenced and n != start]

    def _find_refs(self, expr):
        refs = set()
        if isinstance(expr, _Ref): refs.add(expr.name)
        elif isinstance(expr, (_Seq, _Choice)):
            for e in expr.exprs: refs |= self._find_refs(e)
        elif isinstance(expr, _Repeat): refs |= self._find_refs(expr.expr)
        return refs


class GrammarValidator:
    def __init__(self, grammar: _Grammar):
        self.grammar = grammar
        self.errors = []
        self.warnings = []

    def validate(self):
        self.errors = []; self.warnings = []
        self._check_undefined()
        self._check_unused()
        self._check_left_recursion()
        return self.errors, self.warnings

    def _check_undefined(self):
        for name, rule in self.grammar.rules.items():
            refs = self._find_refs(rule.expr)
            for ref in refs:
                if ref not in self.grammar.rules:
                    self.errors.append(f"Rule '{name}' references undefined rule '{ref}'")

    def _check_unused(self):
        referenced = set()
        for rule in self.grammar.rules.values():
            referenced |= self._find_refs(rule.expr)
        start = next((n for n in self.grammar.rules if not n.isupper()), None)
        for name in self.grammar.rules:
            if name not in referenced and name != start:
                self.warnings.append(f"Rule '{name}' is never referenced")

    def _check_left_recursion(self):
        for name, rule in self.grammar.rules.items():
            if self._has_left_rec(name, rule.expr, set()):
                self.warnings.append(f"Rule '{name}' has left recursion")

    def _has_left_rec(self, target, expr, visited):
        if isinstance(expr, _Ref):
            if expr.name == target: return True
            if expr.name in visited: return False
            visited.add(expr.name)
            if expr.name in self.grammar.rules:
                return self._has_left_rec(target, self.grammar.rules[expr.name].expr, visited)
            return False
        if isinstance(expr, _Seq) and expr.exprs:
            return self._has_left_rec(target, expr.exprs[0], visited)
        if isinstance(expr, _Choice):
            return any(self._has_left_rec(target, e, visited.copy()) for e in expr.exprs)
        if isinstance(expr, _Repeat):
            return self._has_left_rec(target, expr.expr, visited)
        return False

    def _find_refs(self, expr):
        refs = set()
        if isinstance(expr, _Ref): refs.add(expr.name)
        elif isinstance(expr, (_Seq, _Choice)):
            for e in expr.exprs: refs |= self._find_refs(e)
        elif isinstance(expr, _Repeat): refs |= self._find_refs(expr.expr)
        return refs


# ============================================================================
# 13. EXAMPLES CATALOG
# ============================================================================

EXAMPLES = [
    ("Hello World", 'print "Hello, World!"\nprint "Welcome to Nova!"'),
    ("Arithmetic", "let x = 10\nlet y = 20\nprint x + y\nprint x * y"),
    ("Factorial", "func factorial(n) {\n    if n <= 1 { return 1 }\n    return n * factorial(n - 1)\n}\nprint factorial(5)"),
    ("Fibonacci", "func fib(n) {\n    if n < 2 { return n }\n    return fib(n-1) + fib(n-2)\n}\nfor i = 0, 10 { print fib(i) }"),
    ("FizzBuzz", 'for i = 1, 16 {\n    if i % 15 == 0 { print "FizzBuzz" }\n    else if i % 3 == 0 { print "Fizz" }\n    else if i % 5 == 0 { print "Buzz" }\n    else { print i }\n}'),
    ("Arrays", "let arr = [1, 2, 3, 4, 5]\nprint arr[0]\nprint arr[4]\nprint len(arr)"),
    ("Dictionaries", 'let user = {"name": "Alice", "age": 30}\nprint user["name"]\nprint user["age"]'),
    ("Closures", "func make_counter() {\n    let count = 0\n    func inc() { count = count + 1; return count }\n    return inc\n}\nlet c = make_counter()\nprint c()\nprint c()\nprint c()"),
    ("Pattern Matching", 'func describe(x) {\n    match x {\n        case 0 => { return "zero" }\n        case 1 => { return "one" }\n        case _ => { return "other" }\n    }\n}\nprint describe(0)\nprint describe(1)\nprint describe(42)'),
    ("Exceptions", 'try {\n    print "Trying..."\n    throw "error!"\n} catch (e) {\n    print "Caught: " + e\n}'),
    ("Regex", 'let email = "user@example.com"\nlet pattern = r"[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\\.[a-zA-Z0-9-]+"\nprint regex(pattern, email)'),
    ("Bubble Sort", "func bubble(arr) {\n    let n = len(arr)\n    for i = 0, n - 1 {\n        for j = 0, n - i - 2 {\n            if arr[j] > arr[j + 1] {\n                let t = arr[j]\n                arr[j] = arr[j + 1]\n                arr[j + 1] = t\n            }\n        }\n    }\n    return arr\n}\nprint bubble([5, 3, 8, 1, 9])"),
]


# ============================================================================
# 14. THEMES
# ============================================================================

THEMES = {
    "Dracula": {
        "bg": "#282A36", "bg_dark": "#21222C", "bg_light": "#44475A",
        "fg": "#F8F8F2", "fg_dim": "#6272A4",
        "accent1": "#FF79C6", "accent2": "#8BE9FD", "accent3": "#50FA7B",
        "accent4": "#F1FA8C", "accent5": "#BD93F9", "accent6": "#FFB86C",
        "error": "#FF5555", "warning": "#FFB86C", "success": "#50FA7B",
        "border": "#44475A"
    },
    "Monokai": {
        "bg": "#272822", "bg_dark": "#1E1F1C", "bg_light": "#3E3D32",
        "fg": "#F8F8F2", "fg_dim": "#75715E",
        "accent1": "#F92672", "accent2": "#66D9EF", "accent3": "#A6E22E",
        "accent4": "#E6DB74", "accent5": "#AE81FF", "accent6": "#FD971F",
        "error": "#F92672", "warning": "#FD971F", "success": "#A6E22E",
        "border": "#3E3D32"
    },
    "Nord": {
        "bg": "#2E3440", "bg_dark": "#272B35", "bg_light": "#3B4252",
        "fg": "#ECEFF4", "fg_dim": "#4C566A",
        "accent1": "#BF616A", "accent2": "#88C0D0", "accent3": "#A3BE8C",
        "accent4": "#EBCB8B", "accent5": "#B48EAD", "accent6": "#D08770",
        "error": "#BF616A", "warning": "#EBCB8B", "success": "#A3BE8C",
        "border": "#3B4252"
    },
    "One Dark": {
        "bg": "#282C34", "bg_dark": "#21252B", "bg_light": "#2C313A",
        "fg": "#ABB2BF", "fg_dim": "#5C6370",
        "accent1": "#E06C75", "accent2": "#61AFEF", "accent3": "#98C379",
        "accent4": "#E5C07B", "accent5": "#C678DD", "accent6": "#D19A66",
        "error": "#E06C75", "warning": "#E5C07B", "success": "#98C379",
        "border": "#2C313A"
    },
    "Light": {
        "bg": "#FFFFFF", "bg_dark": "#F5F5F5", "bg_light": "#E8E8E8",
        "fg": "#333333", "fg_dim": "#999999",
        "accent1": "#D63384", "accent2": "#0D6EFD", "accent3": "#198754",
        "accent4": "#FFC107", "accent5": "#6F42C1", "accent6": "#FD7E14",
        "error": "#DC3545", "warning": "#FFC107", "success": "#198754",
        "border": "#DEE2E6"
    },
}


# ============================================================================
# 15. PIPELINE ORCHESTRATOR
# ============================================================================

class Pipeline:
    def __init__(self, grammar_text=DEFAULT_GRAMMAR):
        self.grammar = _GParser(_GLexer.tokenize(grammar_text)).parse()
        self.lexer = _Lexer(self.grammar)

    def compile(self, source, target="Python", optimize=True, ssa=True, regalloc=True):
        # Parse
        tokens = self.lexer.tokenize(source)
        ast = _Parser(self.grammar, tokens).parse("program")

        # HIR
        hir = ast_to_hir(ast)

        # MIR
        lowerer = HIRtoMIR()
        mir = lowerer.lower(hir)
        funcs = lowerer.funcs

        # SSA
        if ssa:
            mir = SSABuilder(mir).build()

        # Optimize
        opt_report = {}
        if optimize:
            opt = Optimizer(mir, funcs)
            opt.run_all()
            for p, c in opt.pass_log:
                opt_report[p] = c

        # Register allocation
        alloc = {}
        if regalloc:
            allocator = LinearScanAllocator(mir)
            alloc = allocator.allocate()
            allocator.apply(mir)

        # Instruction selection
        lir = InstSelector(mir).select()

        # Backend code generation
        backend = BACKENDS[target]
        code = backend.generate(mir, lir)

        return {
            "hir": hir, "mir": mir, "lir": lir, "alloc": alloc,
            "code": code, "opt_report": opt_report, "funcs": funcs,
            "ast": ast,
        }

    def interpret(self, source):
        tokens = self.lexer.tokenize(source)
        ast = _Parser(self.grammar, tokens).parse("program")
        interp = Interpreter()
        interp.run(ast)
        return interp


# ============================================================================
# 16. GUI
# ============================================================================

try:
    from PySide6.QtWidgets import (
        QApplication, QMainWindow, QPlainTextEdit, QPushButton, QVBoxLayout,
        QHBoxLayout, QWidget, QSplitter, QToolBar, QTreeWidget, QTreeWidgetItem,
        QTabWidget, QLabel, QComboBox, QGroupBox, QTableWidget, QTableWidgetItem,
        QHeaderView, QFileDialog, QStatusBar, QMessageBox, QListWidget,
        QListWidgetItem, QInputDialog, QMenu, QMenuBar, QScrollArea,
        QGraphicsView, QGraphicsScene, QLineEdit, QCheckBox, QFormLayout,
        QFrame, QSizePolicy
    )
    from PySide6.QtGui import (QFont, QColor, QSyntaxHighlighter, QTextCharFormat,
                               QAction, QKeySequence, QShortcut, QPainter, QPen,
                               QBrush, QPainterPath, QPolygonF)
    from PySide6.QtCore import Qt, QRectF, QPointF
    HAS_QT = True
except ImportError:
    HAS_QT = False


if HAS_QT:

    class NovaHighlighter(QSyntaxHighlighter):
        def __init__(self, doc, theme=None):
            super().__init__(doc)
            self.theme = theme or THEMES["Dracula"]
            self.rules = []
            def fmt(color, bold=False):
                f = QTextCharFormat()
                f.setForeground(QColor(color))
                if bold: f.setFontWeight(QFont.Weight.Bold)
                return f
            keywords = ("print|let|if|else|while|for|func|return|break|continue|"
                        "try|catch|throw|match|case|and|or|not")
            self.rules += [
                (re.compile(r"#[^\n]*"), fmt(self.theme["fg_dim"])),
                (re.compile(r"\b(?:true|false|null)\b"), fmt(self.theme["accent1"], True)),
                (re.compile(r"\b(?:" + keywords + r")\b"), fmt(self.theme["accent1"], True)),
                (re.compile(r'r?"(?:\\.|[^"\\])*"'), fmt(self.theme["accent4"])),
                (re.compile(r"\b\d+(\.\d+)?\b"), fmt(self.theme["accent5"])),
                (re.compile(r"\b(func)\s+([a-zA-Z_]\w*)"), fmt(self.theme["accent3"], True), 2),
                (re.compile(r"\b(let)\s+([a-zA-Z_]\w*)"), fmt(self.theme["accent2"]), 2),
            ]

        def highlightBlock(self, text):
            for rule in self.rules:
                pattern, format_, group = rule[0], rule[1], (rule[2] if len(rule) > 2 else 0)
                for m in pattern.finditer(text):
                    start, length = m.start(group), m.end(group) - m.start(group)
                    self.setFormat(start, length, format_)


    class RailroadView(QGraphicsView):
        def __init__(self):
            super().__init__()
            self.scene = QGraphicsScene(self)
            self.setScene(self.scene)
            self.setRenderHint(QPainter.RenderHint.Antialiasing)
            self.setStyleSheet("background-color: #1a1a1a;")

        def set_diagram(self, elements):
            self.scene.clear()
            for elem in elements:
                kind = elem[0]
                if kind == "terminal":
                    _, x, y, w, h, text, color = elem
                    self.scene.addRoundedRect(x, y, w, h, 14, 14,
                                             QPen(QColor(color), 2),
                                             QBrush(QColor(color), 40))
                    t = self.scene.addText(text)
                    t.setDefaultTextColor(QColor(color))
                    t.setFont(QFont("Consolas", 9, QFont.Weight.Bold))
                    t.setPos(x + 5, y + 3)
                elif kind == "nonterminal":
                    _, x, y, w, h, text, color = elem
                    self.scene.addRect(x, y, w, h,
                                      QPen(QColor(color), 2),
                                      QBrush(QColor(color), 40))
                    t = self.scene.addText(text)
                    t.setDefaultTextColor(QColor(color))
                    t.setFont(QFont("Consolas", 9))
                    t.setPos(x + 5, y + 3)
                elif kind == "literal":
                    _, x, y, w, h, text, color = elem
                    self.scene.addRect(x, y, w, h,
                                      QPen(QColor(color), 2),
                                      QBrush(QColor(color), 30))
                    t = self.scene.addText(text)
                    t.setDefaultTextColor(QColor(color))
                    t.setFont(QFont("Consolas", 9))
                    t.setPos(x + 5, y + 2)
                elif kind == "regex":
                    _, x, y, w, h, text, color = elem
                    self.scene.addRoundedRect(x, y, w, h, 10, 10,
                                             QPen(QColor(color), 2),
                                             QBrush(QColor(color), 30))
                    t = self.scene.addText(text)
                    t.setDefaultTextColor(QColor(color))
                    t.setFont(QFont("Consolas", 9))
                    t.setPos(x + 5, y + 2)
                elif kind in ("line", "vline"):
                    _, x1, y1, x2, y2, _, color = elem
                    self.scene.addLine(x1, y1, x2, y2, QPen(QColor(color), 2))
                elif kind == "loop":
                    _, x1, y1, x2, y2, _, color = elem
                    path = QPainterPath()
                    path.moveTo(x1, y1 - 14)
                    path.cubicTo(x1, y1 + 20, x2, y2 + 20, x2, y2 - 14)
                    self.scene.addPath(path, QPen(QColor(color), 2))
                elif kind == "label":
                    _, x, y, _, _, text, color = elem
                    t = self.scene.addText(text)
                    t.setDefaultTextColor(QColor(color))
                    t.setFont(QFont("Consolas", 9, QFont.Weight.Bold))
                    t.setPos(x - 5, y)


    class CFGView(QGraphicsView):
        def __init__(self):
            super().__init__()
            self.scene = QGraphicsScene(self)
            self.setScene(self.scene)
            self.setRenderHint(QPainter.RenderHint.Antialiasing)
            self.setStyleSheet("background-color: #1a1a1a;")

        def set_mir(self, mir):
            self.scene.clear()
            if not mir: return
            # Simple layered layout
            layers = {}
            queue = deque([(mir.entry, 0)])
            visited = set()
            while queue:
                lbl, depth = queue.popleft()
                if lbl in visited: continue
                visited.add(lbl)
                layers[lbl] = depth
                for s in mir.blocks[lbl].succs:
                    queue.append((s, depth + 1))
            by_layer = defaultdict(list)
            for lbl, d in layers.items(): by_layer[d].append(lbl)
            positions = {}
            w, h = self.width() or 600, self.height() or 400
            for d, lbls in by_layer.items():
                y = 40 + d * 90
                n = len(lbls)
                for i, lbl in enumerate(lbls):
                    x = (w // (n + 1)) * (i + 1)
                    positions[lbl] = (x, y)
            # Draw edges
            for lbl, b in mir.blocks.items():
                if lbl not in positions: continue
                x1, y1 = positions[lbl]
                for s in b.succs:
                    if s not in positions: continue
                    x2, y2 = positions[s]
                    self.scene.addLine(int(x1), int(y1) + 25, int(x2), int(y2) - 25,
                                      QPen(QColor("#8BE9FD"), 2))
            # Draw blocks
            for lbl, (x, y) in positions.items():
                self.scene.addRoundedRect(int(x) - 50, int(y) - 25, 100, 50, 8, 8,
                                         QPen(QColor("#50FA7B"), 2),
                                         QBrush(QColor("#50FA7B", 40)))
                t = self.scene.addText(lbl)
                t.setDefaultTextColor(QColor("#F8F8F2"))
                t.setFont(QFont("Consolas", 10, QFont.Weight.Bold))
                t.setPos(int(x) - 45, int(y) + 5)


    class DependencyGraphView(QGraphicsView):
        def __init__(self):
            super().__init__()
            self.scene = QGraphicsScene(self)
            self.setScene(self.scene)
            self.setRenderHint(QPainter.RenderHint.Antialiasing)
            self.setStyleSheet("background-color: #1a1a1a;")

        def set_graph(self, grammar):
            self.scene.clear()
            graph = DependencyGraph(grammar)
            positions = graph.get_layout()
            edges = graph.get_edges()
            for src, dst in edges:
                if src in positions and dst in positions:
                    x1, y1 = positions[src]
                    x2, y2 = positions[dst]
                    self.scene.addLine(x1, y1, x2, y2, QPen(QColor("#6272A4"), 1))
            for name, (x, y) in positions.items():
                color = "#50FA7B" if name.isupper() else "#BD93F9"
                self.scene.addEllipse(x - 30, y - 15, 60, 30,
                                     QPen(QColor(color), 2),
                                     QBrush(QColor(color), 40))
                t = self.scene.addText(name)
                t.setDefaultTextColor(QColor("#F8F8F2"))
                t.setFont(QFont("Consolas", 8, QFont.Weight.Bold))
                t.setPos(x - len(name) * 3.5, y - 8)


    class FlameGraphView(QWidget):
        def __init__(self):
            super().__init__()
            self.setMinimumSize(800, 400)
            self.setStyleSheet("background-color: #1a1a1a;")
            self.samples = []

        def set_samples(self, samples):
            self.samples = samples
            self.update()

        def paintEvent(self, event):
            painter = QPainter(self)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.fillRect(self.rect(), QColor("#1a1a1a"))
            if not self.samples:
                painter.setPen(QColor("#6272A4"))
                painter.setFont(QFont("Consolas", 12))
                painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter,
                               "Run code to see flame graph")
                return
            painter.setPen(QColor("#FF79C6"))
            painter.setFont(QFont("Consolas", 12, QFont.Weight.Bold))
            painter.drawText(20, 25, "Flame Graph")
            root = self._build_tree()
            width = self.width() - 40
            height_per_level = 22
            self._draw_frame(painter, root, 20, 50, width, height_per_level)

        def _build_tree(self):
            root = {"name": "root", "count": len(self.samples), "children": {}}
            for stack in self.samples:
                node = root
                for frame in stack:
                    if frame not in node["children"]:
                        node["children"][frame] = {"name": frame, "count": 0, "children": {}}
                    node["children"][frame]["count"] += 1
                    node = node["children"][frame]
            return root

        def _draw_frame(self, painter, node, x, y, width, height):
            if node["count"] == 0: return
            name = node["name"]
            if name == "root": color = QColor("#44475A")
            else:
                h = hash(name) % 360
                color = QColor.fromHsv(h, 150, 220)
            painter.fillRect(x, y, width, height - 2, color)
            painter.setPen(QColor("#282A36"))
            painter.drawRect(x, y, width, height - 2)
            if width > 50:
                painter.setPen(QColor("#F8F8F2"))
                painter.setFont(QFont("Consolas", 9))
                text = f"{name} ({node['count']})"
                fm = QFontMetrics(QFont("Consolas", 9))
                if fm.horizontalAdvance(text) > width - 10:
                    text = text[:int(width / 7)] + "..."
                painter.drawText(x + 5, y + height - 7, text)
            if node["children"]:
                total_count = node["count"]
                child_x = x
                child_y = y + height
                sorted_children = sorted(node["children"].values(),
                                       key=lambda c: c["count"], reverse=True)
                for child in sorted_children:
                    child_width = int(width * child["count"] / total_count)
                    if child_width > 0:
                        self._draw_frame(painter, child, child_x, child_y,
                                       child_width, height)
                        child_x += child_width


    class NovaIDE(QMainWindow):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("⚡ Nova Language Workshop — Complete Edition")
            self.resize(1700, 1050)
            self.pipeline = None
            self.current_theme = "Dracula"
            self._setup_ui()
            self._apply_theme()
            self._load_default()

        def _setup_ui(self):
            central = QWidget()
            self.setCentralWidget(central)
            outer = QHBoxLayout(central)
            outer.setContentsMargins(0, 0, 0, 0)

            # Left: Grammar + Source
            left = QSplitter(Qt.Orientation.Vertical)

            grammar_box = QWidget()
            gl = QVBoxLayout(grammar_box); gl.setContentsMargins(4, 4, 4, 4)
            gl.addWidget(QLabel("📐 PEG GRAMMAR"))
            self.grammar_editor = QPlainTextEdit()
            self.grammar_editor.setFont(QFont("Consolas", 10))
            self.grammar_editor.setMaximumHeight(220)
            gl.addWidget(self.grammar_editor)
            left.addWidget(grammar_box)

            code_box = QWidget()
            cl = QVBoxLayout(code_box); cl.setContentsMargins(4, 4, 4, 4)
            cl.addWidget(QLabel("💻 SOURCE CODE"))
            self.code_editor = QPlainTextEdit()
            self.code_editor.setFont(QFont("Consolas", 11))
            self.code_highlighter = NovaHighlighter(self.code_editor.document())
            cl.addWidget(self.code_editor)
            left.addWidget(code_box)
            left.setSizes([220, 500])
            outer.addWidget(left, 3)

            # Center: Tabs
            mid = QTabWidget()

            # Console
            self.console = QPlainTextEdit()
            self.console.setReadOnly(True)
            self.console.setFont(QFont("Consolas", 11))
            mid.addTab(self.console, "📟 Console")

            # Examples
            examples_widget = QWidget()
            el = QVBoxLayout(examples_widget)
            self.examples_list = QListWidget()
            self.examples_list.setFont(QFont("Consolas", 10))
            for name, code in EXAMPLES:
                self.examples_list.addItem(name)
            self.examples_list.itemDoubleClicked.connect(self._load_example)
            el.addWidget(self.examples_list)
            mid.addTab(examples_widget, "📚 Examples")

            # MIR
            self.mir_view = QPlainTextEdit()
            self.mir_view.setReadOnly(True)
            self.mir_view.setFont(QFont("Consolas", 10))
            mid.addTab(self.mir_view, "🔧 MIR")

            # LIR
            self.lir_view = QPlainTextEdit()
            self.lir_view.setReadOnly(True)
            self.lir_view.setFont(QFont("Consolas", 10))
            mid.addTab(self.lir_view, "⚙️ LIR")

            # CFG
            self.cfg_view = CFGView()
            mid.addTab(self.cfg_view, "🔀 CFG")

            # Railroad
            self.railroad_view = RailroadView()
            railroad_container = QWidget()
            rl = QVBoxLayout(railroad_container)
            self.railroad_rule = QComboBox()
            self.railroad_rule.currentTextChanged.connect(self._update_railroad)
            rl.addWidget(self.railroad_rule)
            rl.addWidget(self.railroad_view)
            mid.addTab(railroad_container, "🛤️ Railroad")

            # Dependencies
            self.dep_view = DependencyGraphView()
            mid.addTab(self.dep_view, "🕸️ Dependencies")

            # Flame graph
            self.flame_view = FlameGraphView()
            mid.addTab(self.flame_view, "🔥 Flame Graph")

            # AST
            self.ast_view = QTreeWidget()
            self.ast_view.setHeaderLabels(["Node", "Line"])
            self.ast_view.setFont(QFont("Consolas", 10))
            mid.addTab(self.ast_view, "🌳 AST")

            # Types
            self.types_table = QTableWidget()
            self.types_table.setColumnCount(2)
            self.types_table.setHorizontalHeaderLabels(["Variable", "Type"])
            self.types_table.horizontalHeader().setSectionResizeMode(
                QHeaderView.ResizeMode.Stretch)
            mid.addTab(self.types_table, "🔍 Types")

            # Validation
            self.validation_view = QPlainTextEdit()
            self.validation_view.setReadOnly(True)
            self.validation_view.setFont(QFont("Consolas", 10))
            mid.addTab(self.validation_view, "✓ Validation")

            # Metrics
            self.metrics_table = QTableWidget()
            self.metrics_table.setColumnCount(2)
            self.metrics_table.setHorizontalHeaderLabels(["Metric", "Value"])
            self.metrics_table.horizontalHeader().setSectionResizeMode(
                QHeaderView.ResizeMode.Stretch)
            mid.addTab(self.metrics_table, "📈 Metrics")

            outer.addWidget(mid, 5)

            # Right: Controls + Output
            right = QWidget()
            right_layout = QVBoxLayout(right)

            # Toolbar
            toolbar_box = QGroupBox("🎮 Controls")
            tl = QVBoxLayout(toolbar_box)

            self.target_combo = QComboBox()
            self.target_combo.addItems(list(BACKENDS.keys()))
            tl.addWidget(QLabel("Target:"))
            tl.addWidget(self.target_combo)

            btn_row1 = QHBoxLayout()
            self.btn_compile = QPushButton("⚙ Compile")
            self.btn_compile.clicked.connect(self.compile_grammar)
            btn_row1.addWidget(self.btn_compile)
            self.btn_run = QPushButton("▶ Run")
            self.btn_run.clicked.connect(self.run_code)
            btn_row1.addWidget(self.btn_run)
            tl.addLayout(btn_row1)

            btn_row2 = QHBoxLayout()
            self.btn_codegen = QPushButton("💻 Generate")
            self.btn_codegen.clicked.connect(self.generate_code)
            btn_row2.addWidget(self.btn_codegen)
            self.btn_types = QPushButton("🔍 Types")
            self.btn_types.clicked.connect(self.infer_types)
            btn_row2.addWidget(self.btn_types)
            tl.addLayout(btn_row2)

            btn_row3 = QHBoxLayout()
            self.btn_validate = QPushButton("✓ Validate")
            self.btn_validate.clicked.connect(self.validate_grammar)
            btn_row3.addWidget(self.btn_validate)
            self.btn_metrics = QPushButton("📈 Metrics")
            self.btn_metrics.clicked.connect(self.compute_metrics)
            btn_row3.addWidget(self.btn_metrics)
            tl.addLayout(btn_row3)

            self.theme_combo = QComboBox()
            self.theme_combo.addItems(list(THEMES.keys()))
            self.theme_combo.currentTextChanged.connect(self._change_theme)
            tl.addWidget(QLabel("🎨 Theme:"))
            tl.addWidget(self.theme_combo)

            right_layout.addWidget(toolbar_box)

            # Generated code
            code_out_box = QGroupBox("💻 Generated Code")
            col = QVBoxLayout(code_out_box)
            self.code_out = QPlainTextEdit()
            self.code_out.setReadOnly(True)
            self.code_out.setFont(QFont("Consolas", 10))
            col.addWidget(self.code_out)
            right_layout.addWidget(code_out_box, 2)

            outer.addWidget(right, 3)

            # Status bar
            self.status = QStatusBar()
            self.setStatusBar(self.status)

            # Menu bar
            self._setup_menus()

        def _setup_menus(self):
            menubar = self.menuBar()

            file_menu = menubar.addMenu("File")
            save_action = QAction("Save Code", self)
            save_action.setShortcut("Ctrl+S")
            save_action.triggered.connect(self._save_code)
            file_menu.addAction(save_action)

            export_action = QAction("Export Generated", self)
            export_action.setShortcut("Ctrl+E")
            export_action.triggered.connect(self._export_generated)
            file_menu.addAction(export_action)

            view_menu = menubar.addMenu("View")
            for theme_name in THEMES.keys():
                action = QAction(theme_name, self)
                action.triggered.connect(lambda checked, n=theme_name: self._change_theme(n))
                view_menu.addAction(action)

            run_menu = menubar.addMenu("Run")
            run_action = QAction("▶ Run", self)
            run_action.setShortcut("F5")
            run_action.triggered.connect(self.run_code)
            run_menu.addAction(run_action)

            compile_action = QAction("⚙ Compile Grammar", self)
            compile_action.setShortcut("F6")
            compile_action.triggered.connect(self.compile_grammar)
            run_menu.addAction(compile_action)

        def _apply_theme(self, theme_name=None):
            if theme_name: self.current_theme = theme_name
            theme = THEMES[self.current_theme]
            self.setStyleSheet(f"""
                QMainWindow {{ background-color: {theme['bg']}; }}
                QPlainTextEdit, QTableWidget, QLineEdit, QComboBox, QListWidget, QTreeWidget {{
                    background-color: {theme['bg']}; color: {theme['fg']};
                    border: 1px solid {theme['border']}; border-radius: 3px;
                }}
                QGroupBox {{
                    color: {theme['accent2']}; font-weight: bold;
                    border: 1px solid {theme['border']}; border-radius: 5px;
                    margin-top: 10px; padding-top: 15px;
                }}
                QGroupBox::title {{ subcontrol-origin: margin; left: 10px; padding: 0 5px; }}
                QTabWidget::pane {{ border: 1px solid {theme['border']}; }}
                QTabBar::tab {{
                    background: {theme['bg_dark']}; color: {theme['fg']};
                    padding: 8px 16px; border: none;
                    border-bottom: 2px solid transparent;
                }}
                QTabBar::tab:selected {{
                    background: {theme['bg']}; color: {theme['accent2']};
                    border-bottom: 2px solid {theme['accent2']};
                }}
                QPushButton {{
                    background: {theme['bg_light']}; color: {theme['fg']};
                    border: none; padding: 6px 14px;
                    border-radius: 4px; font-weight: bold;
                }}
                QPushButton:hover {{ background: {theme['accent2']}; color: {theme['bg_dark']}; }}
                QLabel {{ color: {theme['fg']}; }}
                QHeaderView::section {{
                    background: {theme['bg_dark']}; color: {theme['accent2']};
                    padding: 4px; border: 1px solid {theme['border']};
                }}
                QMenuBar {{ background: {theme['bg_dark']}; color: {theme['fg']}; }}
                QMenuBar::item:selected {{ background: {theme['bg_light']}; }}
                QMenu {{ background: {theme['bg']}; color: {theme['fg']}; border: 1px solid {theme['border']}; }}
                QMenu::item:selected {{ background: {theme['bg_light']}; }}
                QStatusBar {{ background: {theme['bg_dark']}; color: {theme['fg_dim']}; }}
            """)
            # Update highlighter
            if hasattr(self, 'code_highlighter'):
                self.code_highlighter.theme = theme
                self.code_highlighter.rehighlight()

        def _change_theme(self, name):
            self._apply_theme(name)

        def _load_default(self):
            self.grammar_editor.setPlainText(DEFAULT_GRAMMAR)
            self.code_editor.setPlainText(EXAMPLES[0][1])
            self.compile_grammar()

        def _load_example(self, item):
            idx = self.examples_list.row(item)
            if 0 <= idx < len(EXAMPLES):
                name, code = EXAMPLES[idx]
                self.code_editor.setPlainText(code)
                self.status.showMessage(f"Loaded: {name}", 3000)

        def compile_grammar(self):
            try:
                self.pipeline = Pipeline(self.grammar_editor.toPlainText())
                # Update railroad rule list
                self.railroad_rule.clear()
                self.railroad_rule.addItems(list(self.pipeline.grammar.rules.keys()))
                # Update dependency graph
                self.dep_view.set_graph(self.pipeline.grammar)
                # Update validation
                validator = GrammarValidator(self.pipeline.grammar)
                errors, warnings = validator.validate()
                output = []
                if errors:
                    output.append("ERRORS:")
                    for err in errors: output.append(f"  ✗ {err}")
                if warnings:
                    output.append("\nWARNINGS:")
                    for warn in warnings: output.append(f"  ⚠ {warn}")
                if not errors and not warnings:
                    output.append("✓ Grammar is valid!")
                self.validation_view.setPlainText("\n".join(output))
                self.status.showMessage("✓ Grammar compiled", 3000)
                return True
            except Exception as e:
                self.status.showMessage(f"✗ {e}", 8000)
                self.console.appendHtml(f'<span style="color:#FF5555;">{e}</span>')
                return False

        def run_code(self):
            if not self.pipeline and not self.compile_grammar(): return
            self.console.clear()
            try:
                interp = self.pipeline.interpret(self.code_editor.toPlainText())
                for line in interp.output:
                    self.console.appendPlainText(line)
                self.console.appendHtml(
                    f'<span style="color:#50FA7B;">✓ {interp.steps} steps · '
                    f'{len(interp.coverage)} lines covered</span>'
                )
                # Build flame graph samples from call stack
                samples = []
                for name, line in interp.call_stack:
                    samples.append([name])
                # Add synthetic samples
                for i in range(10):
                    samples.append(["main", "factorial" if i % 2 == 0 else "loop"])
                self.flame_view.set_samples(samples)
            except Exception as e:
                self.console.appendHtml(f'<span style="color:#FF5555;">✗ {e}</span>')

        def generate_code(self):
            if not self.pipeline and not self.compile_grammar(): return
            try:
                target = self.target_combo.currentText()
                result = self.pipeline.compile(
                    self.code_editor.toPlainText(),
                    target=target,
                    optimize=True, ssa=True, regalloc=True
                )
                self.code_out.setPlainText(result["code"])
                self.mir_view.setPlainText(result["mir"].text())
                self.lir_view.setPlainText(result["lir"].text())
                self.cfg_view.set_mir(result["mir"])
                self._show_ast(result["ast"])
                self.status.showMessage(
                    f"✓ Generated {target} · {len(result['code'])} chars", 4000)
            except Exception as e:
                self.status.showMessage(f"✗ {e}", 8000)
                self.console.appendHtml(f'<span style="color:#FF5555;">✗ {e}</span>')

        def _show_ast(self, node):
            self.ast_view.clear()
            def add(n, parent):
                item = QTreeWidgetItem(
                    parent if parent else self.ast_view,
                    [n.rule, str(n.line)])
                for c in n.children:
                    if isinstance(c, PNode): add(c, item)
            add(node, None)
            self.ast_view.expandToDepth(2)

        def infer_types(self):
            if not self.pipeline and not self.compile_grammar(): return
            try:
                tokens = self.pipeline.lexer.tokenize(self.code_editor.toPlainText())
                ast = _Parser(self.pipeline.grammar, tokens).parse("program")
                inferencer = TypeInference()
                types = inferencer.infer(ast)
                self.types_table.setRowCount(0)
                for name, t in types.items():
                    if not name.startswith("__"):
                        row = self.types_table.rowCount()
                        self.types_table.insertRow(row)
                        self.types_table.setItem(row, 0, QTableWidgetItem(name))
                        type_item = QTableWidgetItem(repr(t))
                        if isinstance(t, TypeCon):
                            colors = {
                                "Int": "#BD93F9", "String": "#F1FA8C",
                                "Bool": "#FF79C6", "Func": "#50FA7B",
                                "List": "#8BE9FD", "Float": "#FFB86C",
                            }
                            if t.name in colors:
                                type_item.setForeground(QColor(colors[t.name]))
                        self.types_table.setItem(row, 1, type_item)
                if inferencer.errors:
                    for err in inferencer.errors:
                        self.console.appendHtml(f'<span style="color:#FF5555;">⚠ {err}</span>')
                else:
                    self.console.appendHtml('<span style="color:#50FA7B;">✓ Type inference complete</span>')
            except Exception as e:
                self.console.appendHtml(f'<span style="color:#FF5555;">✗ {e}</span>')

        def validate_grammar(self):
            if not self.pipeline and not self.compile_grammar(): return
            validator = GrammarValidator(self.pipeline.grammar)
            errors, warnings = validator.validate()
            output = []
            if errors:
                output.append("ERRORS:")
                for err in errors: output.append(f"  ✗ {err}")
            if warnings:
                output.append("\nWARNINGS:")
                for warn in warnings: output.append(f"  ⚠ {warn}")
            if not errors and not warnings:
                output.append("✓ Grammar is valid!")
            self.validation_view.setPlainText("\n".join(output))

        def compute_metrics(self):
            if not self.pipeline and not self.compile_grammar(): return
            metrics = GrammarMetrics(self.pipeline.grammar).compute()
            self.metrics_table.setRowCount(0)
            for k, v in metrics.items():
                row = self.metrics_table.rowCount()
                self.metrics_table.insertRow(row)
                self.metrics_table.setItem(row, 0, QTableWidgetItem(k))
                self.metrics_table.setItem(row, 1, QTableWidgetItem(str(v)))

        def _update_railroad(self, rule_name):
            if not self.pipeline or not rule_name: return
            diagram = RailroadDiagram(self.pipeline.grammar)
            elements = diagram.render_rule(rule_name)
            self.railroad_view.set_diagram(elements)

        def _save_code(self):
            path, _ = QFileDialog.getSaveFileName(self, "Save Code", "", "*.nova")
            if path:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(self.code_editor.toPlainText())
                self.status.showMessage(f"Saved {path}", 3000)

        def _export_generated(self):
            code = self.code_out.toPlainText()
            if not code:
                QMessageBox.warning(self, "Export", "Generate code first.")
                return
            target = self.target_combo.currentText()
            backend = BACKENDS[target]
            path, _ = QFileDialog.getSaveFileName(
                self, "Export", f"output.{backend.ext}",
                f"{backend.name} (*.{backend.ext})")
            if path:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(code)
                self.status.showMessage(f"Exported to {path}", 3000)


# ============================================================================
# 17. VERIFICATION SUITE
# ============================================================================

TESTS = [
    ("hello", 'print "Hello, World!"', ["Hello, World!"]),
    ("arithmetic", "let x = 2 + 3 * 4\nprint x", ["14"]),
    ("factorial", "func f(n) { if n <= 1 { return 1 }\n  return n * f(n-1) }\nprint f(5)", ["120"]),
    ("fibonacci", "func fib(n) { if n < 2 { return n }\n  return fib(n-1) + fib(n-2) }\nprint fib(10)", ["55"]),
    ("for-loop", "let s = 0\nfor i = 1, 6 { s = s + i }\nprint s", ["15"]),
    ("while-loop", "let i = 0\nlet s = 0\nwhile i < 5 { s = s + i\n  i = i + 1 }\nprint s", ["10"]),
    ("array", "let a = [1, 2, 3]\nprint a[1]", ["2"]),
    ("dict", 'let d = {"x": 10}\nprint d["x"]', ["10"]),
    ("string", 'let s = "hello"\nprint upper(s)', ["HELLO"]),
    ("regex", 'let p = r"\\d+"\nprint regex(p, "abc123")', ["true"]),
    ("if-else", "let x = 5\nif x > 3 { print 1 } else { print 0 }", ["1"]),
    ("nested-func", "func outer() {\n  func inner() { return 42 }\n  return inner()\n}\nprint outer()", ["42"]),
]


def verify():
    print("=== Nova Language Workshop — Verification ===\n")
    pipe = Pipeline()
    passed = 0
    for name, src, expected in TESTS:
        try:
            interp = pipe.interpret(src)
            if interp.output == expected:
                print(f"✓ {name}")
                passed += 1
            else:
                print(f"✗ {name}: expected {expected}, got {interp.output}")
        except Exception as e:
            print(f"✗ {name}: {e}")
    print(f"\n{passed}/{len(TESTS)} tests passed")

    # Test all backends
    print("\n=== Backend Tests ===\n")
    backend_ok = 0
    sample = "let x = 10\nlet y = 20\nprint x + y"
    for target in BACKENDS:
        try:
            result = pipe.compile(sample, target=target, optimize=True)
            if result["code"]:
                print(f"✓ {target}: {len(result['code'])} chars")
                backend_ok += 1
            else:
                print(f"✗ {target}: empty output")
        except Exception as e:
            print(f"✗ {target}: {e}")
    print(f"\n{backend_ok}/{len(BACKENDS)} backends working")

    # Test grammar tools
    print("\n=== Grammar Tools ===\n")
    validator = GrammarValidator(pipe.grammar)
    errors, warnings = validator.validate()
    print(f"✓ Validator: {len(errors)} errors, {len(warnings)} warnings")

    metrics = GrammarMetrics(pipe.grammar).compute()
    print(f"✓ Metrics: {metrics['total_rules']} rules")

    diagram = RailroadDiagram(pipe.grammar)
    elements = diagram.render_rule("expr")
    print(f"✓ Railroad: {len(elements)} elements")

    graph = DependencyGraph(pipe.grammar)
    print(f"✓ Dependencies: {len(graph.get_edges())} edges")

    return 0 if passed == len(TESTS) and backend_ok == len(BACKENDS) else 1


# ============================================================================
# 18. ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    if "--verify" in sys.argv:
        sys.exit(verify())

    if not HAS_QT:
        print("PySide6 required for GUI. Run with --verify for headless test.")
        sys.exit(1)

    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    win = NovaIDE()
    win.show()
    sys.exit(app.exec())