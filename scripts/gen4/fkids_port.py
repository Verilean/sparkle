import re,os,sys
mods="Helpers Diag Env LegacyH1 LegacyH2 LegacyH3 LegacyH4 LegacyH5 LegacyH6 LegacyH7 LegacyH8a LegacyH8 LegacyH8d LegacyH9 LegacyH10a LegacyH10b LegacyH11 LegacyRules LegacyTail LegacyCached Entry EntryArms EntryCore Child Depth DepthArms DepthEntry DepthInduct DepthTop LegacyArm LegacyInduct LegacyInduct2 LegacyFinal".split()
ported_before="Prims Tac Tele Translate Emit Inst ProjField Canon Fallback".split()
allm=set(mods)|set(ported_before)
only=sys.argv[1:] or mods
src={m:open(f"Tools/ShippingGen4KWalk{m}.lean").read() for m in mods}
declre=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|def|abbrev|lemma)\s+([A-Za-z_][A-Za-z_0-9'.]*)",re.M)
# decl names that get converted
rename={}
for m in mods:
    s=src[m]
    if 'KeepsCP' in s or 'kwalk' in s:
        for d in declre.findall(s):
            if d.endswith('K') and not d.endswith('KS'): rename[d]=d+'S'
            elif re.search(r'K\d?$',d): rename[d]=d+'S'
            else: rename[d]=d+'S'
# names from already-ported modules: K->KS / PK->PS
fk=""
for m in ported_before:
    fk+=open(f"Tools/ShippingGen4FKids{m}.lean").read()
fkdecl=set(declre.findall(fk))
kw=""
for m in ported_before+["Prims"]:
    p=f"Tools/ShippingGen4KWalk{m}.lean"
    if os.path.exists(p): kw+=open(p).read()
for d in declre.findall(kw):
    for cand in (d+'S', re.sub(r'K$','S',d), re.sub(r'PK$','PS',d)):
        if cand in fkdecl and cand!=d: rename[d]=cand;break
def port(m):
    s=src[m]
    for x in allm:
        s=re.sub(rf"^(open|import) Tools\.ShippingGen4KWalk{x}$",lambda mo:f"{mo.group(0)}\n{mo.group(1)} Tools.ShippingGen4FKids{x}",s,flags=re.M)
    s=re.sub(r"^(namespace|end|#print axioms) Tools\.ShippingGen4KWalk(\w*)",lambda mo:f"{mo.group(1)} Tools.ShippingGen4FKids{mo.group(2)}",s,flags=re.M)
    s=s.replace("emitAssignP ","emitAssignPS ").replace("withVarMappingP ","withVarMappingPS ")
    for k in ("kwalkM","kwalkN","kwalk"):
        s=re.sub(rf"\b{k}\b","swalkN",s)
    s=s.replace("kwalkS","swalkS")
    s=s.replace("KeepsCP","KeepsCS")
    for d in sorted(rename,key=len,reverse=True):
        s=re.sub(rf"(?<![A-Za-z0-9_'.]){re.escape(d)}(?![A-Za-z0-9_'])",rename[d],s)
    s=re.sub(r"fuelFixM_keepsCP\s+(\w+)\s*\(fun rec hrec mctx cctx hA a => (\w+) (.*?) rec \(hrec mctx cctx hA\) a\) _ mctx cctx hA e",
             lambda mo:f"Tools.ShippingGen4FKidsCanon.KeepsCS.fuelFixM {mo.group(1)} (fun rec hrec a => {mo.group(2)} {mo.group(3)} rec hrec a) _ e",s,flags=re.S)
    # opens
    hdr="open Tools.ShippingGen4FKids\nopen Tools.ShippingGen4FKidsCalc\nopen Tools.ShippingGen4FKidsPrims\nopen Tools.ShippingGen4FKidsTac\nopen Tools.ShippingGen4FKidsTele\n"
    s=s.replace("\nvariable",f"\n{hdr}\nvariable",1) if "\nvariable" in s else s
    imp="import Tools.ShippingGen4FKidsTac\nimport Tools.ShippingGen4FKidsTele\nimport Tools.ShippingGen4FKidsCanon\n"
    if "import Tools.ShippingGen4FKidsTac\n" not in s: s=imp+s
    # K-walk still imported for non-ported ancestors; keep.
    return s
for m in only:
    open(f"Tools/ShippingGen4FKids{m}.lean","w").write(port(m))
print(len(rename))
