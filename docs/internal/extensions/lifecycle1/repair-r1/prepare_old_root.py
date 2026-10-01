"""Materialize a read-only original production root in owned ignored scratch."""
import hashlib,json,pathlib,shutil,subprocess
root=pathlib.Path(__file__).resolve().parents[5]
source=pathlib.Path('C:/Users/poin/.codex/worktrees/8941/RMQ')
target=root/'.lake/repair-r1/old-root'
base='12bd7f0fc2c87f2c9bdef3825bd92477e48e3433'
assert not target.exists()
names=['lakefile.toml','RMQ/Validation/PackedLifecycle.lean','scripts/lifecycle_validator.ps1',
       'scripts/lifecycle_dependency_replay.ps1','scripts/owned_process_tree.ps1',
       'RMQ/Core/WordRAM/Lifecycle/Executable.lean','RMQ/Core/WordRAM/Lifecycle/Controls.lean',
       'RMQ/Core/WordRAM/Lifecycle/ArrayRun.lean','RMQ/Core/WordRAM/Lifecycle/Machine.lean',
       'RMQ/Core/WordRAM/Lifecycle/Program.lean','RMQ/Core/WordRAM/Lifecycle/Service.lean']
pins={}
for name in names:
    blob=subprocess.run(['git','show',base+':'+name],cwd=root,check=True,capture_output=True,timeout=30).stdout
    raw=(source/name).read_bytes()
    assert raw.replace(b'\r\n',b'\n')==blob.replace(b'\r\n',b'\n')
    (target/name).parent.mkdir(parents=True,exist_ok=True)
    (target/name).write_bytes(raw)
    pins[name]={'bytes':len(raw),'workingSha256':hashlib.sha256(raw).hexdigest(),'gitSha256':hashlib.sha256(blob).hexdigest()}
exe='.lake/build/bin/rmq_lifecycle_validate.exe'
(target/exe).parent.mkdir(parents=True,exist_ok=True)
shutil.copy2(root/exe,target/exe)
assert hashlib.sha256((target/exe).read_bytes()).hexdigest()=='4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c'
(target.parent/'old-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n',encoding='utf-8')
print('OLD SOURCE ROOT',target)
