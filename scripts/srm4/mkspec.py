import json,sys
def mk(out,ns,imports,extra_opens,sources,prior):
    # prior: list of (name,new,lacks) ; sources: list of (file, [names])
    allx=[{'name':n,'new':new,'lacks':lk,'done':True,'ns':nsq} for (n,new,lk,nsq) in prior]
    for f,names in sources:
        for n in names: allx.append({'name':n,'file':f,'ns':ns})
    return {'out':out,'imports':imports,'header':'-- GENERATED','namespace':ns,'extra_opens':extra_opens,
            'sources':[{'file':f,'names':names} for f,names in sources],'all':allx}
