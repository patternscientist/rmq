import hashlib,json,pathlib,zipfile

root=pathlib.Path(__file__).resolve().parent
files=sorted(p for p in root.iterdir() if p.is_file() and p.name!='manifest.json')
manifest={p.name:{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
target=root.with_suffix('.zip')
with zipfile.ZipFile(target,'w',zipfile.ZIP_DEFLATED) as z:
    for p in files+[root/'manifest.json']:z.write(p,root.name+'/'+p.name)
with zipfile.ZipFile(target) as z:
    assert z.testzip() is None
    for name,entry in manifest.items():
        data=z.read(root.name+'/'+name)
        assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
print(json.dumps({'archive':str(target),'files':len(files)+1,'bytes':target.stat().st_size,
                  'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'verified':True}))
