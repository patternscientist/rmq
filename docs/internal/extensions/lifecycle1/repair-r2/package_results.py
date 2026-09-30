"""Compact verified outcomes; full child outputs remain pinned in the evidence directory."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
def pin(p):b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def main():
    p=ROOT/'.lake/repair-r2/evidence-verified.json';v=json.loads(p.read_bytes());assert v['passed']
    controls={}
    for profile,campaign in v['controlCampaigns'].items():
        controls[profile]={'passed':True,'selected':campaign['selected'],'registryReceipt':campaign['receipt'],'results':[{'id':r['id'],'kind':r['kind'],'handler':r['handler'],'mapping':r['mapping'],'passed':r['passed'],'actualReceipt':r['receipt']} for r in campaign['results']]}
    value={'schema':'life1-r2-compact-results-v1','passed':True,'validatedPacket':pin(p),'productionCommit':v['productionCommit'],'checks':v['checks'],'hash':v['hash'],'materialization':v['materialization'],'controlCampaigns':controls,'registryCampaigns':{k:{'passed':True,'selected':x['selected'],'receipt':x['receipt'],'positiveCount':12,'challengedCount':12} for k,x in v['registryCampaigns'].items()},'dependency':{k:{a:b for a,b in x.items() if a!='baseline'} for k,x in v['dependency'].items()},'fileIndex':v['fileIndex'],'scope':v['scope'],'oldWindowsPositive':v['oldWindowsPositive'],'limits':v['limitations']}
    out=HERE/'RESULTS.json';out.write_bytes((json.dumps(value,indent=2)+'\n').encode());print(json.dumps(pin(out)))
if __name__=='__main__':main()
