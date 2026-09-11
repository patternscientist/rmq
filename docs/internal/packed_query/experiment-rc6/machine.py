"""Restricted Python is a source language, never a host query implementation.
Functions lower to acyclic register subroutines; every operation and call step ticks.
Only the final primitive interpreter is executed on query input.
"""
import ast
import collections
import hashlib
import json


class Compiler:
    def __init__(self, source, constants):
        tree = ast.parse(source)
        self.funcs = {x.name: x for x in tree.body if isinstance(x, ast.FunctionDef)}
        assert all(isinstance(x, (ast.FunctionDef, ast.Expr)) for x in tree.body)
        self.constants = constants
        self.code = []
        self.meta = []
        self.regs = 0
        self.globals = {}
        self.stack = []
        self.observers = collections.defaultdict(list)

    def fresh(self):
        r = self.regs
        self.regs += 1
        return r

    def emit(self, op, *args):
        self.code.append([op, *args])
        self.meta.append('/'.join(self.stack))
        return len(self.code) - 1

    def const(self, x):
        r = self.fresh()
        self.emit('const', r, int(x))
        return r

    def expr(self, x, env):
        if isinstance(x, ast.Constant):
            return self.const(x.value)
        if isinstance(x, ast.Name):
            if x.id in env:
                src = env[x.id]
            elif x.id in self.globals:
                src = self.globals[x.id]
            else:
                return self.const(self.constants[x.id])
            # Snapshot now: a later operand/call may mutate this global.
            r = self.fresh()
            self.emit('move',r,src)
            return r
        if isinstance(x, ast.BinOp):
            a, b = self.expr(x.left, env), self.expr(x.right, env)
            r = self.fresh()
            if isinstance(x.op, ast.Sub):
                # Lean Nat subtraction is lowered, not a saturating macro-op.
                cmp = self.fresh()
                self.emit('lt',cmp,a,b)
                p = self.emit('jnz',cmp,None)
                self.emit('sub',r,a,b)
                q = self.emit('jump',None)
                self.code[p][-1] = len(self.code)
                self.emit('const',r,0)
                self.code[q][-1] = len(self.code)
                return r
            names = {ast.Add:'add', ast.Sub:'sub', ast.Mult:'mul', ast.FloorDiv:'div',
                     ast.Mod:'mod', ast.LShift:'shl', ast.RShift:'shr', ast.BitAnd:'and', ast.BitOr:'or'}
            self.emit(names[type(x.op)], r, a, b)
            return r
        if isinstance(x, ast.UnaryOp) and isinstance(x.op, ast.Not):
            r = self.fresh()
            self.emit('eq', r, self.expr(x.operand, env), self.const(0))
            return r
        if isinstance(x, ast.Compare):
            assert len(x.ops) == 1
            names = {ast.Lt:'lt', ast.LtE:'le', ast.Eq:'eq', ast.NotEq:'ne', ast.Gt:'gt', ast.GtE:'ge'}
            a, b = self.expr(x.left, env), self.expr(x.comparators[0], env)
            r = self.fresh()
            self.emit(names[type(x.ops[0])], r, a, b)
            return r
        if isinstance(x, ast.BoolOp):
            r = self.fresh()
            patches = []
            for v in x.values:
                self.emit('move', r, self.expr(v, env))
                patches.append(self.emit('jz' if isinstance(x.op, ast.And) else 'jnz', r, None))
            for p in patches:
                self.code[p][-1] = len(self.code)
            return r
        if isinstance(x, ast.IfExp):
            r = self.fresh()
            p = self.emit('jz', self.expr(x.test, env), None)
            self.emit('move', r, self.expr(x.body, env))
            q = self.emit('jump', None)
            self.code[p][-1] = len(self.code)
            self.emit('move', r, self.expr(x.orelse, env))
            self.code[q][-1] = len(self.code)
            return r
        if isinstance(x, ast.Call):
            assert isinstance(x.func, ast.Name) and not x.keywords
            name = x.func.id
            args = [self.expr(a, env) for a in x.args]
            if name == 'load':
                assert len(args) == 1
                r = self.fresh()
                self.emit('load', r, args[0])
                return r
            if name in ('min', 'max'):
                assert len(args) == 2
                r, cmp = self.fresh(), self.fresh()
                self.emit('lt', cmp, *args)
                p = self.emit('jz', cmp, None)
                self.emit('move', r, args[0 if name == 'min' else 1])
                q = self.emit('jump', None)
                self.code[p][-1] = len(self.code)
                self.emit('move', r, args[1 if name == 'min' else 0])
                self.code[q][-1] = len(self.code)
                return r
            return self.call(name, args)
        raise ValueError(ast.dump(x))

    def call(self, name, args):
        assert name not in self.stack, ('recursive call forbidden', name)
        fn = self.funcs[name]
        assert len(args) == len(fn.args.args)
        self.stack.append(name)
        env = {}
        declared_globals = {s for x in ast.walk(fn) if isinstance(x, ast.Global) for s in x.names}
        for s in declared_globals:
            if s not in self.globals:
                self.globals[s] = self.fresh()
            env[s] = self.globals[s]
        for arg, src in zip(fn.args.args, args):
            env[arg.arg] = self.fresh()
            self.emit('move', env[arg.arg], src)
        result = self.fresh()
        self.emit('const', result, 0)
        if name == 'read':
            self.observers[len(self.code)].append(['begin',name,args,result])
        exits = []
        self.block(fn.body, env, result, exits)
        for p in exits:
            self.code[p][-1] = len(self.code)
        if name == 'read':
            self.observers[len(self.code)].append(['end',name,args,result])
        self.stack.pop()
        return result

    def block(self, body, env, result, exits):
        for x in body:
            if isinstance(x, ast.Global) or isinstance(x, ast.Pass):
                continue
            if isinstance(x, ast.Assign):
                value = self.expr(x.value, env)
                for target in x.targets:
                    assert isinstance(target, ast.Name)
                    if target.id not in env:
                        env[target.id] = self.fresh()
                    self.emit('move', env[target.id], value)
            elif isinstance(x, ast.AugAssign):
                v = self.expr(ast.BinOp(left=x.target, op=x.op, right=x.value), env)
                self.emit('move', env[x.target.id], v)
            elif isinstance(x, ast.Return):
                self.emit('move', result, self.expr(x.value, env))
                exits.append(self.emit('jump', None))
            elif isinstance(x, ast.If):
                p = self.emit('jz', self.expr(x.test, env), None)
                self.block(x.body, env, result, exits)
                q = self.emit('jump', None)
                self.code[p][-1] = len(self.code)
                self.block(x.orelse, env, result, exits)
                self.code[q][-1] = len(self.code)
            elif isinstance(x, ast.While):
                assert not x.orelse
                start = len(self.code)
                p = self.emit('jz', self.expr(x.test, env), None)
                self.block(x.body, env, result, exits)
                self.emit('jump', start)
                self.code[p][-1] = len(self.code)
            elif isinstance(x, ast.Expr):
                if not isinstance(x.value, ast.Constant):
                    self.expr(x.value, env)
            else:
                raise ValueError(ast.dump(x))

    def compile(self):
        left, right = self.fresh(), self.fresh()
        result = self.call('query', [left, right])
        self.emit('halt', result)
        return {'code':self.code, 'meta':self.meta, 'registers':self.regs,
                'inputs':[left,right], 'globals':self.globals,
                'observers':dict(self.observers)}


CATEGORIES = {'load':'memoryRead', 'const':'registerWrite', 'move':'registerWrite',
              **{x:'arithmetic' for x in ['add','sub','mul','div','mod','shl','shr','and','or']},
              **{x:'comparison' for x in ['lt','le','eq','ne','gt','ge']},
              'jz':'branch','jnz':'branch','jump':'branch','jreg':'branch','halt':'control'}


class SubroutineCompiler(Compiler):
    """Static acyclic subroutines; no hidden stack, call, or return primitive.

    Each function has fixed parameter, result, and return-PC registers. Calls
    are parameter moves, a return-PC constant, and a jump. Returns are jreg.
    Acyclicity ensures a live function frame is never re-entered/overwritten.
    """
    def __init__(self, source, constants):
        super().__init__(source,constants)
        self.frames = {}
        self.fixups = []
        self.labels = {}
        self.function_observers = collections.defaultdict(list)
        for fn in self.funcs.values():
            for x in ast.walk(fn):
                if isinstance(x, ast.Global):
                    for name in x.names:
                        if name not in self.globals:
                            self.globals[name] = self.fresh()
        for name,fn in self.funcs.items():
            self.frames[name] = ([self.fresh() for _ in fn.args.args],self.fresh(),self.fresh())
        def visit(name,path):
            assert name not in path, ('recursive call forbidden',path,name)
            for x in ast.walk(self.funcs[name]):
                if isinstance(x,ast.Call) and x.func.id in self.funcs:
                    visit(x.func.id,path+[name])
        visit('query',[])

    def call(self,name,args):
        params,result,retpc = self.frames[name]
        assert len(params)==len(args)
        for d,s in zip(params,args): self.emit('move',d,s)
        self.emit('const',retpc,len(self.code)+2)
        self.fixups.append((self.emit('jump',0),name))
        copy = self.fresh()
        self.emit('move',copy,result)
        return copy

    def compile(self):
        left,right=self.fresh(),self.fresh()
        result=self.call('query',[left,right])
        self.emit('halt',result)
        for name,fn in self.funcs.items():
            self.stack=[name]
            params,result,retpc=self.frames[name]
            self.labels[name]=len(self.code)
            self.function_observers[len(self.code)].append(['enter',name])
            env={a.arg:r for a,r in zip(fn.args.args,params)}
            for x in ast.walk(fn):
                if isinstance(x,ast.Global):
                    for s in x.names: env[s]=self.globals[s]
            self.emit('const',result,0)
            if name=='read':self.observers[len(self.code)].append(['begin',name,params,result])
            exits=[]
            self.block(fn.body,env,result,exits)
            for p in exits:self.code[p][-1]=len(self.code)
            if name=='read':self.observers[len(self.code)].append(['end',name,params,result])
            self.function_observers[len(self.code)].append(['leave',name])
            self.emit('jreg',retpc)
        for p,name in self.fixups:self.code[p][-1]=self.labels[name]
        self.stack=[]
        return {'code':self.code,'meta':self.meta,'registers':self.regs,
                'inputs':[left,right],'globals':self.globals,'observers':dict(self.observers),
                'functionObservers':dict(self.function_observers),'labels':self.labels}


def run(program, cells, width, left, right, limit=20000000, keep_trace=False):
    code = program['code']
    cap = 1 << width
    # Constructor-exhaustive static bound, including dormant code and IDs.
    static_max = max([len(code), program['registers']] + [a for ins in code for a in ins[1:]])
    if static_max >= cap:
        raise OverflowError(('static',static_max,width))
    assert all(0 <= x < cap for x in cells)
    regs = [0] * program['registers']
    for r,x in zip(program['inputs'], [left,right]):
        assert 0 <= x < cap
        regs[r] = x
    pc = steps = 0
    peak = max(left,right)
    counts = collections.Counter({c:0 for c in CATEGORIES.values()})
    phases = collections.Counter()
    reads, execution = [], []
    logical, pending = [], []
    callstack=[]
    result, failure = None, None
    while steps < limit:
        assert 0 <= pc < len(code)
        for kind,name in program.get('functionObservers',{}).get(pc,[]):
            if kind=='enter':callstack.append(name)
        phase='/'.join(callstack) if callstack else program['meta'][pc]
        for kind,name,args,r in program['observers'].get(pc, []):
            if kind == 'begin':
                pending.append({'segment':regs[args[0]],'index':regs[args[1]],
                                'readStart':len(reads),'phase':phase})
            else:
                event = pending.pop()
                event.update(valueTag=regs[r],readEnd=len(reads))
                logical.append(event)
        ins = code[pc]
        op, a = ins[0], ins[1:]
        oldpc = pc
        pc += 1
        steps += 1
        counts[CATEGORIES[op]] += 1
        phases[phase] += 1
        write = None
        if op == 'halt':
            result = regs[a[0]]
            break
        elif op == 'const': write = (a[0], a[1])
        elif op == 'move': write = (a[0], regs[a[1]])
        elif op == 'load':
            addr = regs[a[1]]
            val = cells[addr] if addr < len(cells) else None
            reads.append({'pc':oldpc,'address':addr,'reply':val,'phase':phase})
            if val is None:
                failure = 'missing-cell'
                break
            write = (a[0], val)
        elif op in ('jz','jnz'):
            if (regs[a[0]] == 0) == (op == 'jz'): pc = a[1]
        elif op == 'jump': pc = a[0]
        elif op == 'jreg': pc = regs[a[0]]
        else:
            d, ar, br = a
            x, y = regs[ar], regs[br]
            if op == 'add': z = x+y
            elif op == 'sub': z = x-y
            elif op == 'mul': z = x*y
            elif op == 'div': z = x//y if y else 0
            elif op == 'mod': z = x%y if y else x
            elif op == 'shl': z = x<<y
            elif op == 'shr': z = x>>y
            elif op == 'and': z = x&y
            elif op == 'or': z = x|y
            elif op == 'lt': z = int(x<y)
            elif op == 'le': z = int(x<=y)
            elif op == 'eq': z = int(x==y)
            elif op == 'ne': z = int(x!=y)
            elif op == 'gt': z = int(x>y)
            elif op == 'ge': z = int(x>=y)
            else: raise ValueError(ins)
            write = (d,z)
        if write:
            d,z = write
            if not 0 <= z < cap:
                raise OverflowError(('dynamic',oldpc,ins,z,width,program['meta'][oldpc]))
            regs[d] = z
            peak = max(peak,z)
        if keep_trace:
            execution.append([oldpc,write])
        for kind,name in program.get('functionObservers',{}).get(oldpc,[]):
            if kind=='leave':assert callstack.pop()==name
    else:
        failure = 'fuel-exhausted'
    assert sum(counts.values()) == steps
    return {'resultTag':result,'failure':failure,'steps':steps,'categories':dict(counts),
            'maxRegisterValue':peak,'staticMax':static_max,'registerWidth':width,
            'reads':reads,'logical':logical,'phases':dict(phases),'execution':execution}


def digest(x):
    return hashlib.sha256(json.dumps(x,separators=(',',':'),sort_keys=True).encode()).hexdigest()
