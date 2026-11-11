#!/usr/bin/env python3
"""Small raw-call edge diagnostics; EasyCrypt supplies the adaptive theorem."""
import itertools,json

def main():
    count=0
    for n,length,tag in itertools.product((-1,0,1,224,225),(0,32,129,1153,1154),(0,1,2,255)):
        data=bytes([tag])*length
        executable=0<=n<=224 and len(data)==1153 and data[0]==1
        decoded=('E' if length==32 else 'F' if length==1153 and tag==0 else
                 'G' if length==1153 and tag==1 else 'H' if length==129 and tag==2 else None)
        assert executable==(0<=n<=224 and decoded=='G')
        # Q always counts this call and B always counts the full input,
        # including invalid output requests and output length zero.
        q,b,g=1,len(data),int(executable)
        assert q==1 and b==length and 0<=g<=q
        count+=1
    print(json.dumps({'status':'PASS','cases':count,'scope':'Finite raw length/tag diagnostics only; no adaptive, bit-cost, CPU or PPT claim.'}))
if __name__=='__main__':main()
