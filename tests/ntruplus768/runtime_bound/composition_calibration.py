"""Bind the cost interpretation to actual counters and the closed composed price.

These checks supplement kernel-checked arithmetic. A proof of an unchanged
inequality is insufficient if its charge operation was silently replaced by zero.
"""
import re
import policy

KERNEL_FIELDS = ('scale','unit','encode','recover','encrypt','trit',
                 'poly_compare','cipher_compare','psi_draw','adversary')
PROFILE_FIELDS = ('h','size','d','g','q','b','put_v','put_c','dec_v','dec_c',
                  'enc','alloc','xcalls','xvisits')


def expected_operations():
    model={
      'rt_zero': 'op rt_zero : rt_profile = {|'+ ';'.join('rp_'+x+'=0' for x in PROFILE_FIELDS)+'|}.',
      'rt_call': '''op rt_call(p:rt_profile)(is_g:bool)(bytes:int)=
        {|p with rp_q=p.`rp_q+1;rp_g=p.`rp_g+b2i is_g;rp_b=p.`rp_b+bytes|}.''',
      'rt_record': '''op rt_record(p:rt_profile)(visits comparisons:int)=
        {|p with rp_h=p.`rp_h+1;rp_size=1+visits-p.`rp_size;
        rp_put_v=p.`rp_put_v+visits;rp_put_c=p.`rp_put_c+comparisons;
        rp_alloc=p.`rp_alloc+2*(visits-p.`rp_size)+1|}.''',
      'rt_decap': '''op rt_decap(p:rt_profile)(visits encryptions comparisons:int)=
        {|p with rp_d=p.`rp_d+1;rp_dec_v=p.`rp_dec_v+visits;
        rp_enc=p.`rp_enc+encryptions;rp_dec_c=p.`rp_dec_c+comparisons|}.''',
      'rt_extract': '''op rt_extract(p:rt_profile)(visits:int)=
        {|p with rp_xcalls=p.`rp_xcalls+1;rp_xvisits=p.`rp_xvisits+visits|}.''',
      'rt_visits': 'op rt_visits(p:rt_profile)=p.`rp_put_v+p.`rp_dec_v+p.`rp_xvisits.',
      'rt_comparisons': 'op rt_comparisons(p:rt_profile)=p.`rp_put_c+p.`rp_dec_c.',
      'rt_g_length': 'op rt_g_length(p:rt_profile)=p.`rp_g+p.`rp_enc.'}
    letters='s u e r p t q c d a'.split()
    kernels={
      'rtk_profile': 'op rtk_profile '+' '.join(letters)+' : rt_kernel_profile={|'+
          ';'.join('rtk_'+field+'='+arg for field,arg in zip(KERNEL_FIELDS,letters))+'|}.',
      'rtk_add': 'op rtk_add(x y:rt_kernel_profile)=rtk_profile '+
          ' '.join('(x.`rtk_'+f+'+y.`rtk_'+f+')' for f in KERNEL_FIELDS)+'.',
      'rtk_le': 'op rtk_le(x y:rt_kernel_profile)='+
          '/\\'.join('0<=x.`rtk_'+f+'<=y.`rtk_'+f for f in KERNEL_FIELDS)+'.'}
    bounds={'rtk_charge':'op rtk_charge c k='+
            '+'.join('c.`rtk_'+f+'*k.`rtk_'+f for f in KERNEL_FIELDS)+'.'}
    complete={}
    for label in ('di','do','co'):
        complete['rt_complete_'+label+'_charge']='op rt_complete_'+label+'_charge tA p k='+\
            'rt_run_'+label+'_overhead+rt_outer_'+label+'_charge tA k+rt_phase_charge rt_concrete_phase_prices p.'
        complete['rt_complete_'+label+'_bound']='op rt_complete_'+label+'_bound tA q b='+\
            'rt_run_'+label+'_overhead+rt_outer_'+label+'_bound tA+rt_q_envelope rt_concrete_phase_prices q b.'
    return {'RTModel':model,'RTKernelTypes':kernels,'RTBounds':bounds,'RTCompleteCost':complete}


def check(sources=None):
    expected=expected_operations()
    if sources is None:
        sources={name:(policy.PROOF/('NTRUPlus768'+name+'.ec')).read_text() for name in expected}
    records=[]
    for source,operations in expected.items():
        text=policy.without_comments(sources[source])
        for name,declaration in operations.items():
            matches=re.findall(r'\bop\s+'+re.escape(name)+r'\b.*?\.\s*(?=\n|$)',text,re.S)
            policy.require(len(matches)==1 and policy.compact(matches[0])==policy.compact(declaration),
                           'actual counter or closed-cost composition drift: '+name)
            records.append(source+'.'+name)
    return {'status':'CLOSED_COST_COMPOSITION_CHECKED','operations':records,
            'scope':'Actual callback/history/kernel counts and their concrete total charge; no arbitrary price replacement.'}
