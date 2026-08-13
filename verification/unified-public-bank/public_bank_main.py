#!/usr/bin/env python3
import argparse,json,os,pathlib
from public_core import inventory,lean_environment,compile_candidates,joint_closure,theorem_names,run
from public_master import make_master

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',action='append',required=True)
    parser.add_argument('--out',type=pathlib.Path,required=True)
    args=parser.parse_args()
    candidates,rejected,sources,build,generated=inventory(args.root,args.out)
    environment=lean_environment(os.environ['BANK_BASE_LEAN_PATH'],build,sources)
    compiled=compile_candidates(candidates,rejected,sources,build,environment)
    accepted=joint_closure(compiled,rejected,generated,build,environment)
    baseline=theorem_names([],"Baseline",generated,environment)
    aggregate=theorem_names([item['module'] for item in accepted],"Aggregate",generated,environment)
    if not baseline or not aggregate:
        raise SystemExit(3)
    imported=sorted(aggregate-baseline)
    master=make_master([item['module'] for item in accepted],len(rejected),
        sum(item['declarations'] for item in accepted),
        sum(item['theorems'] for item in accepted),len(imported))
    master_path=generated/'UnifiedMillenniumBraidAll.lean'
    master_path.write_text(master)
    code,log=run(['lean','-o',str(build/'UnifiedMillenniumBraidAll.olean'),str(master_path)],str(generated),environment)
    (generated/'unified.log').write_text(log)
    if code:
        raise SystemExit(4)
    summary={'candidates':len(candidates),'joint_modules':len(accepted),
        'rejected':len(rejected),'declaration_syntax':sum(item['declarations'] for item in accepted),
        'theorem_syntax':sum(item['theorems'] for item in accepted),
        'imported_theorems':len(imported),'baseline_theorems':len(baseline)}
    (generated/'summary.json').write_text(json.dumps(summary,indent=2))
    (generated/'accepted.json').write_text(json.dumps(accepted,indent=2))
    (generated/'rejected.json').write_text(json.dumps(rejected,indent=2))
    (generated/'theorem-names.txt').write_text('\n'.join(imported)+'\n')
    (generated/'summary.env').write_text('\n'.join(f'{key}={value}' for key,value in summary.items())+'\n')
    print(summary)

if __name__=='__main__':
    main()
