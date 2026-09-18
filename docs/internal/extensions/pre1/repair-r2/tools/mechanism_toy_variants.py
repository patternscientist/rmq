import subprocess, os, time, sys
base = open('base.lean', encoding='utf-8').read()
L = r'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
V = {
 'base': {},
 'a_example': {'--INJECT--': 'example : 1 + 1 = 3 := rfl'},
 'b_guard': {'--INJECT--': '#guard 1 + 1 = 3'},
 'b_runcmd': {'--INJECT--': 'open Lean Elab Command in\nrun_cmd do throwError "boom"'},
 'c_maxrec': {'--INJECT--': 'theorem deep : (List.replicate 20000 0).length = 20000 := rfl', '--WITNESS--': 'let _ := @deep'},
 'd_unknown': {'--INJECT--': 'theorem t2 : 1 = 1 := foo_unknown', '--WITNESS--': 'let _ := @t2'},
 'e_unreferenced': {'--INJECT--': 'theorem t3 : 1 + 1 = 3 := rfl'},
 'f_after_marker': {'--TRAILER--': '#guard 1 = 2'},
 'g_bad_end': {'end MechProbe': 'end WrongName'},
 'h_sorry_warning_unreferenced': {'--INJECT--': 'theorem t4 : 1 = 2 := sorry'},
 'i_crlf': {'__CRLF__': ''},
}
env = dict(os.environ, LEAN_NUM_THREADS='1')
for name, subs in V.items():
    text = base
    for k, v in subs.items():
        if k != '__CRLF__':
            assert k in text, k
            text = text.replace(k, v)
    fn = f'v_{name}.lean'
    data = text.replace('\n', '\r\n') if '__CRLF__' in subs else text
    open(fn, 'w', encoding='utf-8', newline='').write(data)
    t = time.time()
    p = subprocess.run([L, fn], capture_output=True, text=True, encoding='utf-8', env=env, timeout=600)
    out = p.stdout + p.stderr
    errs = [l for l in out.splitlines() if ': error' in l]
    diag = [l for l in out.splitlines() if l.startswith('DIAG') or 'PASS' in l]
    print(f'{name:32s} exit={p.returncode} dur={time.time()-t:5.1f}s errlines={len(errs)} {" | ".join(diag)}')
