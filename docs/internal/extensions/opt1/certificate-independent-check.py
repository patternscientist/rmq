from pathlib import Path
import hashlib,json,re,sys
run=Path(sys.argv[1])
out=Path(sys.argv[2])
read=lambda p:json.loads(p.read_text(encoding="utf-8-sig"))
field_path=Path("docs/internal/extensions/opt1/certificate-replay/FIELDS.json")
assert hashlib.sha256(field_path.read_bytes()).hexdigest()=="0d1529c98d35b6ff2ac53d58d107f0a47ec8f5d263f51819c085827c055a63bb"
field_registry=read(field_path)
assert field_registry["Version"]=="opt1-certificate-fields-v3"
assert field_registry["FieldCount"]==len(field_registry["Fields"])==39
fields=field_registry["Fields"]
ids=["A01-UNCHANGED","A02-COMMENT"]+[f"{k}{i:02d}-{f['Name']}" for i,f in enumerate(fields,1) for k in "DW"]
executed=read(run/"executed.json")
assert len(ids)==80 and executed["Version"]=="opt1-certificate-replay-v3"
assert executed["Executed"]==ids==executed["Expected"]
assert not executed["PrepareOnly"]
summary=read(run/"summary.json")
assert summary["Version"]=="opt1-certificate-replay-v3"
assert summary["ExitCode"]==0 and not summary["PrepareOnly"] and not summary["LibrarySelfTestOnly"]
assert summary["TrackedSourceMutations"]==0
expected_stages=[i+"-"+m for i in ids for m in ["Certificate","Capstone","Consumers"]]
actual_stages=[s["Name"] for s in summary["Stages"] if s["Name"] in expected_stages]
assert actual_stages==expected_stages
for key in ["original","imports","tracked-status"]:
 assert read(run/(key+"-before.json"))==read(run/(key+"-after.json")),key
consumer=Path("RMQ/Core/WordRAM/Optimization/Consumers.lean").read_text()
lines=consumer.splitlines()
ranges={}
for f in fields:
 name=f["Name"]
 starts=[i+1 for i,x in enumerate(lines) if x.startswith("theorem "+name+"_expectedType ") or x.startswith("theorem "+name+"_expectedType")]
 assert len(starts)==1
 start=starts[0]
 end=next((i+1 for i in range(start,len(lines)) if lines[i].startswith("theorem ")),len(lines)+1)
 ranges[name]=(start,end)
rows=[]
for case_id in ids:
 case=read(run/case_id/"case.json")
 assert case["Id"]==case_id and case["Mode"]=="LEAN_REPLAY" and case["ProducersCompiled"]
 expected="ACCEPT" if case_id.startswith("A") else "REJECT"
 assert case["Expected"]==case["ConsumerVerdict"]==expected
 assert case["OriginalHashes"]==case["RestoredHashes"]
 assert case["DependencyLibrary"]["LinkedCount"]==259 and not case["DependencyLibrary"]["CacheAliased"]
 assert len(case["PrivateOutputHashes"])==2
 for path,digest in case["PrivateOutputHashes"].items():
  assert hashlib.sha256((run/case_id/"lib"/path).read_bytes()).hexdigest()==digest
 for path,digest in case["RestoredHashes"].items():
  assert hashlib.sha256((run/case_id/"source"/path).read_bytes()).hexdigest()==digest
  assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest
 for module in ["Certificate","Capstone"]:
  rec=read(run/(case_id+"-"+module+".json"))
  result=rec["Result"]
  assert Path(rec["Executable"]).as_posix().lower()=="c:/users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe"
  assert rec["Directory"]==str(run/case_id/"source")
  assert rec["Arguments"]==["-j1","-o",str(run/case_id/"lib"/f"RMQ/Core/WordRAM/Optimization/{module}.olean"),f"RMQ/Core/WordRAM/Optimization/{module}.lean"]
  assert result["ExitCode"]==0 and not result["StandardError"]
  assert not result["TimedOut"] and not result["OutputLimitExceeded"]
  assert list(rec["Environment"])==["LEAN_PATH"] and rec["Environment"]["LEAN_PATH"]==str(run/case_id/"lib")
  assert result["Output"]==result["StandardOutput"]
 rec=read(run/(case_id+"-Consumers.json"));result=rec["Result"]
 assert Path(rec["Executable"]).as_posix().lower()=="c:/users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe"
 assert rec["Directory"]==str(run/case_id/"source")
 assert rec["Arguments"]==["-j1","RMQ/Core/WordRAM/Optimization/Consumers.lean"]
 assert rec["Environment"]=={"LEAN_PATH":str(run/case_id/"lib")}
 assert not result["TimedOut"] and not result["OutputLimitExceeded"]
 headers=[]
 if expected=="ACCEPT":
  assert result["ExitCode"]==0 and not result["StandardError"]
 else:
  assert result["ExitCode"]==1 and not result["StandardError"],case_id
  output="\n".join(result["StandardOutput"])
  assert not re.search(r"(?m)^(error:|uncaught exception:)",output)
  headers=re.findall(r"(?m)^(.+):(\d+):(\d+): error: (.*)$",output)
  assert headers,case_id
  start,end=ranges[case["Field"]]
  for file,line,column,message in headers:
   assert file.replace("\\","/").endswith("RMQ/Core/WordRAM/Optimization/Consumers.lean")
   assert start<=int(line)<end,(case_id,line,start,end)
   assert message.lower().startswith("invalid field") if case_id.startswith("D") else message.lower().startswith(("type mismatch","application type mismatch"))
  assert case["Field"] in output
 rows.append({"Id":case_id,"Verdict":expected,"ProducersCompiled":True,"Diagnostics":headers,"Restored":True})
manifest=read(run/"dependency-snapshot.json")
assert len(manifest)==259
for entry in manifest:
 assert hashlib.sha256(Path(entry["Snapshot"]).read_bytes()).hexdigest()==entry["SHA256"]
record={"SourceFreeze":"bbbe652fa41fa40bf2530b5e2f09c4c225c0e896","ArtifactDirectory":str(run),"Expected":80,"Executed":len(rows),"Accepts":2,"Rejects":78,"AllProducerExitsZero":True,"AllActualConsumerDiagnosticsMatched":True,"AllRestored":True,"Rows":rows}
out.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({k:v for k,v in record.items() if k!="Rows"}))
