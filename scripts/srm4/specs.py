import sys,json
sys.path.insert(0,'scripts/srm4')
from mkspec import mk
S3='Tools.ShippingSrm3Iface'
C1='Tools.ShippingSrm4Core1'
C2='Tools.ShippingSrm4Core2'
P3=[('core_kids_facts_ranA','core_kids_facts_ranAM',True,S3),('core_outsIn_ranA','core_outsIn_ranAM',True,S3),('core_calls_portsG_ranA','core_calls_portsG_ranAM',False,S3),('core_inPorts_ranA','core_inPorts_ranAM',False,S3)]
P1=[('core_linkedWF_ranA','core_linkedWF_ranAM',True,C1),('core_instOuts_not_assigned_ranA','core_instOuts_not_assigned_ranAM',True,C1),('core_closed_typedIn_ranA','core_closed_typedIn_ranAM',True,C1)]
C3='Tools.ShippingSrm4Core3'
C4='Tools.ShippingSrm4Core4'
C5='Tools.ShippingSrm4Core5'
P2=[('core_hierGate_anyA','core_hierGate_anyAM',True,C2),('core_kids_self_ranA','core_kids_self_ranAM',True,C2),('core_raw_facts_ranA','core_raw_facts_ranAM',False,C2),
    ('core_outsExtracted_ranA','core_outsExtracted_ranAM',False,C2),('core_callPorts_ranA','core_callPorts_ranAM',False,C2),('core_instOutWidthsOk_ranA','core_instOutWidthsOk_ranAM',False,C2),('core_runFacts_ranA','core_runFacts_ranAM',False,C2)]
P3b=[('core_conn_refsG_ranA','core_conn_refsG_ranAM',False,C3)]
P4=[('core_portsMatch_raw_ranA','core_portsMatch_raw_ranAM',False,C4),('core_clk_ranA','core_clk_ranAM',True,C4)]
P5=[("deepChild_ifaceA'","deepChild_ifaceA'M",True,C5),('deepChild_ranA','deepChild_ranAM',True,C5),('deepChild_outsMaskedA','deepChild_outsMaskedAM',False,C5)]
