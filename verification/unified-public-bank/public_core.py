from __future__ import annotations
import hashlib, os, pathlib, re, shutil, subprocess

TRUST_PATTERNS = [
    r"\bsorry\b", r"\badmit\b", r"\bsorryAx\b",
    r"(?m)^\s*axiom\b", r"(?m)^\s*opaque\b",
    r"(?m)^\s*unsafe\b", r"\bnative_decide\b",
    r"\bLean\.ofReduceBool\b",
]
THEOREM_RE = re.compile(r"(?m)^\s*(?:protected\s+|private\s+)?(?:theorem|lemma)\s+")
DECL_RE = re.compile(r"(?m)^\s*(?:protected\s+|private\s+|noncomputable\s+)*(?:theorem|lemma|example|def|abbrev|structure|inductive|class|instance)\s+")

def run(command, cwd=None, env=None, timeout=2400):
    try:
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
        return result.returncode, result.stdout
    except subprocess.TimeoutExpired as error:
        return 124, f"timeout: {error}"

def strip_comments_and_strings(text):
    out=[]; i=0; block=0; line=False; string=False; escaped=False
    while i < len(text):
        char=text[i]; nxt=text[i+1] if i+1 < len(text) else ""
        if line:
            out.append("\n" if char=="\n" else " "); line=char!="\n"; i+=1; continue
        if block:
            if char=="/" and nxt=="-": block+=1; out.extend("  "); i+=2
            elif char=="-" and nxt=="/": block-=1; out.extend("  "); i+=2
            else: out.append("\n" if char=="\n" else " "); i+=1
            continue
        if string:
            out.append("\n" if char=="\n" else " ")
            if escaped: escaped=False
            elif char=="\\": escaped=True
            elif char=='"': string=False
            i+=1; continue
        if char=="-" and nxt=="-": line=True; out.extend("  "); i+=2
        elif char=="/" and nxt=="-": block=1; out.extend("  "); i+=2
        elif char=='"': string=True; out.append(" "); i+=1
        else: out.append(char); i+=1
    return "".join(out)

def lean_environment(base_path, build, sources):
    environment=os.environ.copy()
    environment["LEAN_PATH"]=os.pathsep.join((str(build),str(sources),base_path))
    return environment

def inventory(roots, out):
    sources=out/"Sources"; build=out/"Build"; generated=out/"generated"
    shutil.rmtree(out, ignore_errors=True); sources.mkdir(parents=True); build.mkdir(); generated.mkdir()
    candidates=[]; rejected=[]; seen=set()
    for root_spec in roots:
        label, raw_path=root_spec.split("=",1); root=pathlib.Path(raw_path)
        for source_file in sorted(root.rglob("*.lean")):
            text=source_file.read_text(errors="replace")
            digest=hashlib.sha256(text.encode()).hexdigest()
            if digest in seen: continue
            seen.add(digest); clean=strip_comments_and_strings(text)
            violations=[pattern for pattern in TRUST_PATTERNS if re.search(pattern,clean)]
            if violations:
                rejected.append({"path":str(source_file),"sha256":digest,"reason":"trust","detail":violations}); continue
            safe_label=re.sub(r"[^A-Za-z0-9_]","_",label)
            module=f"UnifiedPublicBank.{safe_label}.M_{digest[:16]}"
            staged=sources/pathlib.Path(*module.split(".")).with_suffix(".lean")
            staged.parent.mkdir(parents=True,exist_ok=True); staged.write_text(text)
            candidates.append({"label":label,"path":str(source_file),"sha256":digest,
                "module":module,"source":str(staged),"theorems":len(THEOREM_RE.findall(clean)),
                "declarations":len(DECL_RE.findall(clean))})
    return candidates,rejected,sources,build,generated

def compile_candidates(candidates,rejected,sources,build,environment):
    compiled=[]
    for candidate in candidates:
        output=build/pathlib.Path(*candidate["module"].split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True,exist_ok=True)
        code,log=run(["lean","-o",str(output),candidate["source"]],str(sources),environment,240)
        if code: rejected.append(candidate|{"reason":"compile","detail":log[-10000:]})
        else: compiled.append(candidate)
    return compiled

def joint_closure(compiled,rejected,generated,build,environment):
    accepted=[]
    for candidate in compiled:
        probe=generated/"Probe.lean"
        probe.write_text("import Mathlib\n"+"\n".join("import "+x["module"] for x in accepted+[candidate])+"\n")
        code,log=run(["lean","-o",str(build/"Probe.olean"),str(probe)],str(generated),environment)
        if code: rejected.append(candidate|{"reason":"collision","detail":log[-10000:]})
        else: accepted.append(candidate)
    return accepted

def theorem_names(modules,name,generated,environment):
    source=generated/f"{name}.lean"
    source.write_text("import Mathlib\n"+"\n".join("import "+m for m in modules)+'''\nopen Lean Elab Command
elab "#dumpBank" : command => do
  let environment ← getEnv
  for (constantName, constantInfo) in environment.constants.toList do
    match constantInfo with
    | .thmInfo _ => logInfo m!"BANK_THEOREM_NAME={constantName}"
    | _ => pure ()
#dumpBank
''')
    code,log=run(["lean",str(source)],str(generated),environment)
    (generated/f"{name}.log").write_text(log)
    return set(re.findall(r"BANK_THEOREM_NAME=([^\s]+)",log)) if code==0 else set()
