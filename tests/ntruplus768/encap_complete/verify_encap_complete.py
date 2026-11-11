#!/usr/bin/env python3
"""Replay deterministic/randomized Encaps, conditional agreement and six kernels."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode = True
import check_encap_complete as policy
import prepare_reference as reference
ROOT,TEST=policy.ROOT,policy.TEST
PROOF=ROOT/'ntruplus/proof/768/ref/encap_complete'
GENERATED_EOF='\nlemma __encap_generated_eof : true. proof. trivial. qed.\n'


def timestamp():return datetime.now(timezone.utc).isoformat()
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def include_arguments():
    args,dirs,seen=[],[],set()
    for project in (PROOF/'easycrypt.project',PROOF.parent/'kem_agreement/easycrypt.project'):
        for raw in project.read_text().splitlines():
            line=raw.strip()
            if not line or line.startswith(('#','[')):continue
            key,separator,value=line.partition('=');key,value=key.strip(),value.strip()
            policy.require(separator and key in ('rdirs','idirs','timeout'),'unsupported project setting')
            if key=='timeout':continue
            namespace,colon,directory=value.partition(':')
            if not colon:namespace,directory='',value
            path=(project.parent/directory).resolve();policy.require(path.is_dir(),'missing include directory: '+str(path))
            flag='-R' if key=='rdirs' else '-I';value=namespace+':'+str(path) if colon else str(path)
            if (flag,value) not in seen:seen.add((flag,value));dirs.append(path);args+=[flag,value]
    return args,dirs


def snapshot(directories,native_only):
    paths=policy.source_dependencies()|{ROOT/'scripts/verify-ntruplus768-encap-complete.sh',
          TEST.parent/'toolchain/check_model_compatibility.py',reference.GUARD/'reference-manifest.json',
          reference.GUARD/'prepare_reference.py',TEST.parent/'poly_frombytes_checked/check_poly_frombytes_checked.py',
          TEST.parent/'decap_r2_comp/audit_compatibility.py',TEST.parent/'decap_r2_comp/audit_ntt_bounds.py',
          TEST.parent/'decap_candidate/audit_compatibility.py'}
    paths.update(p for p in TEST.rglob('*') if p.is_file() and p.suffix not in ('.pyc','.eco') and (not native_only or p.name!='eof_sentinels.py'))
    paths.update(p for p in reference.REFERENCE.rglob('*') if p.is_file())
    paths.update(ROOT/'NTRU+/NTRU+768'/name for name in ('ntt.c','poly.c','params.h'))
    if native_only:
        for name in policy.NEW_KERNELS:paths.update((PROOF.parent/name/'extracted').glob('*.ec'))
    else:
        for name in policy.PROOF_DIRS:
            for filename in ('Makefile','easycrypt.project'):
                p=PROOF.parent/name/filename
                if p.is_file():paths.add(p)
        for directory in directories:paths.update(directory.rglob('*.ec'))
    return {str(p.relative_to(ROOT)):digest(p) for p in sorted(paths) if p.is_file()}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-only',action='store_true',help='never reports full proof PASS')
    parser.add_argument('--defer-safety',action='store_true',help='omit safety; explicitly partial status')
    parser.add_argument('--output',type=Path,help='new/empty evidence directory outside checkout')
    args=parser.parse_args()
    output=(args.output or Path(tempfile.mkdtemp(prefix='ntruplus-encap-complete-'))).resolve()
    policy.require(not output.is_relative_to(ROOT),'evidence must be outside checkout')
    output.mkdir(parents=True,exist_ok=True);policy.require(not any(output.iterdir()),'output must be empty')
    summary=output/'summary.json'
    report={'status':'RUNNING','started_at':timestamp(),'output':str(output),'commands':[],'tools':{},
      'reference_commit':'3991b2ae08d6f0008d37e41b8aceaaab27b4ec89','platform':platform.platform(),
      'scope':'Deterministic/randomized mixed C/Jasmin Encaps and conditional KEM agreement. Six new Jasmin kernels, modeled composition under SHAKE/RNG contracts, official API and Decaps roundtrip regression. Conditional no-wrap/key hypotheses are not a decryption-failure probability bound. Not full KEM security/IND-CCA, all-Jasmin, C-AST equivalence or whole-API CT/SCT.',
      'buffer_contract':'Deterministic entry has disjoint ct1152,ss32,pk1152,coins96 regions; pk and coins readable. Randomized wrapper samples96 bytes before checking pk, then clears its96-byte coin array. Statically laid-out13634-byte workspace is cleared after every deterministic-core path. Source contracts, value proofs and default checker initialization assumptions remain distinct.',
      'ct_sct_scope':'Only six new kernels checked here. All secret data remain secret; no new declassification. C orchestration, SHAKE/RNG, whole-API CT/SCT and register/spill erasure remain outside these checks.',
      'native_scope':'Immutable official API with an appended wrapper exposing its actual static deterministic entry. Independent production Encaps source, actual primitives through trace hooks, pinned C SHAKE, same KAT DRBG. New Decaps linked unchanged for roundtrips. Fused official multiply-add compared by modular congruence/ranges/canonical bytes, not raw word equality. Cleanup read only after real clear; UBSan covers C only.',
      'proof_scope':'Only files listed in proof_mains are replayed as fresh mains. Other imported theories are bound by source hashes and retain their prior evidence; their inclusion does not constitute a fresh main replay of every imported theorem.',
      'safety_replayed':False,'safety_deferred':args.defer_safety,
      'python':{'path':sys.executable,'version':sys.version,'sha256':digest(Path(sys.executable))},
      'environment':{'EC_TIMEOUT':os.environ.get('EC_TIMEOUT','60'),'OCAMLRUNPARAM':os.environ.get('OCAMLRUNPARAM','o=20'),'max_provers':1,'prover':'Z3'}}
    def save():
        temporary=summary.with_suffix('.tmp');temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(summary)
    def run(label,argv,cwd=ROOT,expected_failure=False,overrides=None):
        log=output/(label+'.log');record={'label':label,'argv':[str(a) for a in argv],'cwd':str(cwd),
            'started_at':timestamp(),'log':str(log),'environment_overrides':overrides or {}}
        report['commands'].append(record);save();start=time.monotonic()
        with log.open('w') as stream:
            process=subprocess.run(record['argv'],cwd=cwd,env={**os.environ,**(overrides or {})},stdout=stream,stderr=subprocess.STDOUT)
        okay=process.returncode!=0 if expected_failure else process.returncode==0
        record.update(exit_code=process.returncode,seconds=round(time.monotonic()-start,3),completed_at=timestamp(),
            log_sha256=digest(log),expected_failure=expected_failure,result='EXPECTED_REJECTION' if okay and expected_failure else 'PASS' if okay else 'FAIL')
        save();print(record['result'],label,record['seconds'],flush=True)
        if not okay:
            print('\n'.join(log.read_text(errors='replace').replace('\r','\n').splitlines()[-25:]))
            raise RuntimeError('command failed: '+label)
        return log
    def tool(variable,name,version):
        argv=shlex.split(os.environ.get(variable,name));path=shutil.which(argv[0]);policy.require(path,'missing tool: '+argv[0])
        argv[0]=str(Path(path).resolve());log=run('tool-'+name,argv+version)
        report['tools'][name]={'argv_prefix':argv,'binary_sha256':digest(Path(argv[0])),'version':log.read_text(errors='replace')}
        return argv
    directories=[];save()
    try:
        include,directories=([],[]) if args.native_only else include_arguments()
        report['source_hashes_before']=snapshot(directories,args.native_only)
        policy.check()
        run('source-model-compatibility',[sys.executable,TEST.parent/'toolchain/check_model_compatibility.py','--source-only'])
        run('source-policy-check',[sys.executable,TEST/'check_encap_complete.py'])
        run('mutation-gate-selfcheck',[sys.executable,TEST/'test_gates.py'])
        for label,filename in [('official-arithmetic-compatibility','audit_compatibility.py'),('official-ntt-interval-certificate','audit_ntt_bounds.py')]:
            log=run(label,[sys.executable,TEST.parent/'decap_r2_comp'/filename,'--root',ROOT])
            report[label]=json.loads(log.read_text())
        audit_file=output/'fused-basemul-add-audit.json'
        run('fused-basemul-add-audit',[sys.executable,TEST/'audit_fused_basemul_add.py','--repo',ROOT,'--output',audit_file])
        report['fused_arithmetic_audit']=json.loads(audit_file.read_text())
        policy.require(report['fused_arithmetic_audit'].get('status')=='PASS','fused arithmetic audit failed')
        jasmin=tool('JASMINC','jasminc',['-version']);extractor=tool('JASMIN2EC','jasmin2ec',['--version'])
        safety=tool('JASMIN_CHECKSAFETY','jasmin-checksafety',['--version'])
        ct=tool('JASMINCT' if 'JASMINCT' in os.environ else 'JASMIN_CT','jasmin-ct',['--version'])
        cc=tool('CC','cc',['--version']);run('compiler-target',cc+['-dumpmachine'])
        easycrypt=tool('EASYCRYPT','easycrypt',['config']) if not args.native_only else []
        if not args.native_only:tool('WHY3','why3',['--version'])
        report['fresh_extractions']={}
        for name,(label,stem,mainfile,expected) in policy.NEW_KERNELS.items():
            fresh=output/('fresh-'+name);fresh.mkdir();source=policy.JASMIN/(stem+'.jazz');slice_name=policy.PREFIX+stem
            run('extract-'+name,extractor+['--array-model=old','--arch=x86-64','--cc=linux','--output-array='+str(fresh),
                '-o',fresh/mainfile,'-f',slice_name,source])
            report['fresh_extractions'][name]={'result':'PASS','comparison':'whole inventory and raw bytes',
                'files':policy.check_extraction(PROOF.parent/name/'extracted',fresh,expected)}
        stages=policy.STAGES
        for name,source,slice_name in stages:
            run('compile-'+name,jasmin+['-arch','x86-64','-call-conv','linux','-system','linux','-slice',slice_name,
                '-o',output/(name+'.s'),source])
        if not args.native_only:
            import eof_sentinels as eof
            new={str(p.relative_to(ROOT)) for name in policy.PROOF_DIRS for p in (PROOF.parent/name).glob('*.ec')}
            policy.require(new==set(eof.PROOF_PINS)==set(eof.SENTINELS),'new proof inventory drift')
            targets=[(p,GENERATED_EOF,None) for name in policy.NEW_KERNELS for p in sorted((PROOF.parent/name/'extracted').glob('*.ec'))]
            targets += [(ROOT/p,v['sentinel'],v['sha256']) for p,v in eof.REUSED.items()]
            targets += [(ROOT/p,eof.SENTINELS[p],pin) for p,pin in eof.PROOF_PINS.items()]
            timeout=int(report['environment']['EC_TIMEOUT']);policy.require(timeout>0,'positive EC timeout required')
            server=[]
            if os.environ.get('WHY3_SERVER_SOCKET'):
                socket=Path(os.environ['WHY3_SERVER_SOCKET']);policy.require(socket.is_socket(),'invalid Why3 socket');server=['-server',str(socket)]
            def proof_command(path):
                return easycrypt+['compile','-no-eco','-pragmas','Proofs:check','-p','Z3','-timeout',str(timeout),'-max-provers','1',*server,*include,str(path)]
            report['proof_mains']=[]
            for index,(path,sentinel,pin) in enumerate(targets):
                original=path.read_bytes();relative=str(path.relative_to(ROOT))
                policy.require(policy.sha(original)==report['source_hashes_before'][relative],'proof changed before replay')
                if pin:
                    policy.require(policy.sha(original)==pin,'reviewed proof pin drift: '+relative);policy.check_proof_text(original.decode())
                directory=output/'proof-inputs'/str(index);directory.mkdir(parents=True)
                copied=directory/path.name;copied.write_bytes(original+sentinel.encode());copied_hash=digest(copied)
                log=run('proof-'+path.stem,proof_command(copied),cwd=PROOF,overrides={'OCAMLRUNPARAM':report['environment']['OCAMLRUNPARAM']})
                policy.require(digest(copied)==copied_hash,'proof copy mutated during replay')
                report['proof_mains'].append({'source':relative,'source_sha256':policy.sha(original),'checked_copy':str(copied),
                    'checked_copy_sha256':copied_hash,'sentinel_sha256':policy.sha(sentinel.encode()),'result':'PASS','log':str(log)})
            for relative in eof.NEGATIVE_PROOFS:
                path=ROOT/relative;original=path.read_text();cut=original.rfind('qed.')
                policy.require(cut>=0 and not original[cut+4:].strip(),'unexpected final proof structure')
                negative=output/'open-proof'/path.name;negative.parent.mkdir(exist_ok=True)
                negative.write_text(original[:cut]+eof.SENTINELS[relative])
                log=run('eof-open-proof-'+path.stem,proof_command(negative),cwd=PROOF,expected_failure=True,
                    overrides={'OCAMLRUNPARAM':report['environment']['OCAMLRUNPARAM']})
                policy.require('inside a proof script' in log.read_text(errors='replace'),'EOF rejection reason changed')
        report['safety']={}
        for name,source,slice_name in stages[-6:]:
            command=safety+['--arch=x86-64','--call-conv=linux','--slice='+slice_name,source]
            evidence={'status':'DEFERRED' if args.defer_safety else 'RUNNING','argv':[str(x) for x in command],
                'source_hashes':{str(p.relative_to(ROOT)):digest(p) for p in sorted(policy.dependencies(source))},
                'checker_sha256':report['tools']['jasmin-checksafety']['binary_sha256'],
                'model_note':'Source annotation asks for no initial output bytes; default checker exported-array model may still assume initialization. This run alone does not eliminate that default-model premise.'}
            report['safety'][name]=evidence
            if not args.defer_safety:
                log=run(name+'-safety',command)
                policy.require('No Safety Violation' in log.read_text(),'missing positive safety diagnostic')
                evidence.update(status='PASS',log=str(log),log_sha256=digest(log))
            run(name+'-ct',ct+['--after=inline','--slice='+slice_name,source])
            run(name+'-sct',ct+['--sct','--after=inline','--slice='+slice_name,source])
        report['safety_replayed']=not args.defer_safety
        generated=output/'generated-c';run('prepare-official-reference',[sys.executable,TEST/'prepare_reference.py','--output',generated])
        report['official_reference']=json.loads((generated/'reference.json').read_text())
        sources=[TEST/'encap_complete_test.c',TEST/'trace.c',generated/'official_kem.c']
        sources += [reference.REFERENCE/name for name in ('poly.c','ntt.c','symmetric.c','fips202/fips202.c','kat/rng.c','kat/aes.c')]
        sources += [policy.C_SOURCE,policy.DECAP_C,policy.MESSAGE_C]+[output/(name+'.s') for name,_,_ in stages]
        report['native_compiled_sources']={str(p):digest(p) for p in sources};report['differential']={};report['independent_oracle']={}
        for variant in ('normal','ubsan'):
            directory=output/('native-'+variant);directory.mkdir()
            flags=['-std=c11','-O2','-g','-Wall','-Wextra','-Wpedantic','-fPIC','-ffunction-sections','-fdata-sections',
                '-I'+str(TEST),'-I'+str(reference.REFERENCE)]
            sanitizer=['-O1','-fsanitize=undefined','-fno-sanitize-recover=undefined','-fno-omit-frame-pointer'] if variant=='ubsan' else []
            objects=[]
            for index,path in enumerate(sources):
                obj=directory/(str(index)+'.o');extra=['-Werror'] if path.parent==TEST or path in (policy.C_SOURCE,policy.DECAP_C,policy.MESSAGE_C) else []
                if path.name=='rng.c':extra+=['-Drandombytes=kat_randombytes','-include','stdlib.h']
                if path==policy.C_SOURCE:
                    hooks={'encap_guard':'guard','encap_hash_f_prepare':'prepare_f','decap_hash_h_prepare':'prepare_h',
                           'poly_cbd1':'cbd','ntt':'ntt','decap_message_prepare':'prepare_g','poly_sotp_encode':'encode',
                           'poly_basemul':'basemul','poly_centered_add':'centered_add','poly_tobytes':'tobytes',
                           'encap_copy_key':'copy_key','encap_clear':'clear','encap_clear_coins':'clear_coins'}
                    extra+=['-D'+policy.PREFIX+stem+'=e_'+label for stem,label in hooks.items()]
                    extra+=['-Dshake256=e_shake256','-Drandombytes=e_randombytes']
                run('native-'+variant+'-compile-'+str(index),cc+flags+sanitizer+extra+['-c',path,'-o',obj]);objects.append(str(obj))
            binary=directory/'encap-complete-test';library=directory/'libencap-complete.so'
            run('native-'+variant+'-link',cc+objects+sanitizer+['-Wl,--gc-sections','-Wl,-z,noexecstack','-o',binary])
            run('native-'+variant+'-shared',cc+objects+sanitizer+['-shared','-Wl,-z,noexecstack','-o',library])
            overrides={'UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1'} if variant=='ubsan' else {}
            log=run('native-'+variant+'-run',[binary,reference.REFERENCE/'PQCkemKAT_2336.rsp'],overrides=overrides)
            counts=json.loads(log.read_text());expected={'status':'PASS','kat_vectors':100,'kat_randomized_runs':200,'derand_cases':1800,'random_cases':1700,'encap_calls':28200,'workspace_clear_calls':14100,'coin_clear_calls':6900,'roundtrips':1512,'output_initial_patterns':4}
            policy.require(all(counts.get(k)==v for k,v in expected.items()),'incomplete Encaps API coverage')
            counts['binary_sha256']=digest(binary);report['differential'][variant]=counts
            log=run('oracle-'+variant,[sys.executable,TEST/'independent_oracle.py',library,reference.REFERENCE/'PQCkemKAT_2336.rsp'],overrides=overrides)
            counts=json.loads(log.read_text());expected={'status':'PASS','encode_cases':3243,'centered_add_cases':5197,'fused_cases':256,'hash_f_cases':2560,'copy_cases':256,'workspace_clear_cases':14,'coin_clear_cases':14,'full_api_cases':264,'full_hash_triples':200}
            policy.require(all(counts.get(k)==v for k,v in expected.items()),'incomplete independent oracle')
            counts['library_sha256']=digest(library);report['independent_oracle'][variant]=counts
        report['native_compiled_sources_after']={str(p):digest(p) for p in sources}
        policy.require(report['native_compiled_sources']==report['native_compiled_sources_after'],'native inputs changed during replay')
        status='NATIVE_PASS' if args.native_only else 'PASS'
        if args.defer_safety:status+='_EXCEPT_SAFETY'
        report.update(status=status,proofs_replayed=not args.native_only)
    except Exception as error:report.update(status='FAIL',error_type=type(error).__name__,error=str(error))
    finally:
        if 'source_hashes_before' in report:
            try:
                report['source_hashes_after']=snapshot(directories,args.native_only)
                report['inputs_unchanged']=report['source_hashes_before']==report['source_hashes_after']
                if not report['inputs_unchanged']:report.update(status='FAIL',error='source inputs changed during replay')
            except (OSError,ValueError) as error:report.update(status='FAIL',inputs_unchanged=False,error='source snapshot failed: '+str(error))
        report['completed_at']=timestamp();save()
    print('RESULT',report['status'],str(summary),flush=True)
    return 0 if report['status'] in ('PASS','NATIVE_PASS','PASS_EXCEPT_SAFETY','NATIVE_PASS_EXCEPT_SAFETY') else 1


if __name__=='__main__':sys.exit(main())
