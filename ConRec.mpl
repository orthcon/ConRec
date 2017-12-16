lprint("ConRec(P,Q,n,k,x,t,Ls,shift,Pindex,Qindex), ConRecq(P,Q,n,k,x,t,Ls,shift,Pindex,Qindex,q)");

## Compute the recurrence relations of the connection coefficients
## Input:
##   P,Q: two hypergeometric terms in k, degree index by n,
##        variable in x=x(t)
##
##   shift: belonds to {`shiftP`,`shiftQ`},
##            recurrence relation involving shifts of the index of P or Q.
##	    
##   Pindex, Qindex: the indices of P and Q
##
## Output:
##   ls: list of the coefficients of the recurrence relations
##   if length is 3, then
##   ls[1]c[m+1,n]+ls[2]c[m,n]+ls[3]c[m-1,n] = 0.
##   if length is 5, then
##   ls[1]c[m+2,n]+ls[2]c[m+1,n]+ls[3]c[m,n]+ls[4]c[m-1,n]+ls[5]c[m-2,n]=0.
##
## Example
##   P:=poch([la,2 la],n)/2^n*hyperterm([-n,n+2 la],[la+1/2],(1-s*x)/2,k);
##   Q:=2^(-n)*hyperterm([-n,n],[1/2],(1-x)/2,k);
##   L:=proc(f,x) diff(f,x); end proc:
##   ConRec(P,Q,n,k,x,x,L,`shiftP`,n,m); 

ConRec:=proc(P,Q,n,k,x,t,Ls,shift,varm,varn)
local L,Lp,lsp,lsq,lspp,lsqp,lsps,lsqs,re;

  ## Ls is either an operator L,
  ## or it is the list of two operators [L, Lp]
  
  if type(Ls,list) then
    L:=Ls[1]; Lp:=Ls[2];
  else
    L:=Ls; Lp:=0;
  fi;

  ## the 3-term recurrences of P and Q
  lsp:=tr_coe(P,x,n,k,t);
  lsq:=tr_coe(Q,x,n,k,t);

  ## the 3-term recurrences of LP and LQ
  lspp:=tr_coe(L(P,t),x,n,k,t);
  lsqp:=tr_coe(L(Q,t),x,n,k,t);

  if shift=`shiftP` then
    if Lp<>0 then
      re:=Ext_Zeil([Lp(P,t),subs(n=n+1,P),P,subs(n=n-1,P)],k,[t]);
      lsps:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];
    
      re:=Ext_Zeil([Lp(Q,t),subs(n=n+1,Q),Q,subs(n=n-1,Q)],k,[t]);
      lsqs:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

      return(recgenM(lsp,lsq,lspp,lsqp,n,varm,varn,lsps,lsqs));
    else
      return(recgenM(lsp,lsq,lspp,lsqp,n,varm,varn));
    fi;
  else
    if Lp<>0 then
      re:=Ext_Zeil([Lp(P,t),subs(n=n+1,P),P,subs(n=n-1,P)],k,[t]);
      lsps:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];
    
      re:=Ext_Zeil([Lp(Q,t),subs(n=n+1,Q),Q,subs(n=n-1,Q)],k,[t]);
      lsqs:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

      return(recgenN(lsp,lsq,lspp,lsqp,n,varm,varn,lsps,lsqs));
    else
      return(recgenN(lsp,lsq,lspp,lsqp,n,varm,varn));
    fi;
  fi; 

end proc:
    



## Compute the recurrence relations of the connection coefficients / q-case
## Input:
##   P,Q: two hypergeometric terms in k, degree index by n,
##        variable in x=x(t)
##
##   shift: belonds to {`shiftP`,`shiftQ`},
##            recurrence relation involving shifts of the index of P or Q.
##	    
##   Pindex, Qindex: the indices of P and Q
##
## Output:
##   ls: list of the coefficients of the recurrence relations
##   if length is 3, then
##   ls[1]c[m+1,n]+ls[2]c[m,n]+ls[3]c[m-1,n] = 0.
##   if length is 5, then
##   ls[1]c[m+2,n]+ls[2]c[m+1,n]+ls[3]c[m,n]+ls[4]c[m-1,n]+ls[5]c[m-2,n]=0.
##
## Example
##   P:=poch([la,2 la],n)/2^n*hyperterm([-n,n+2 la],[la+1/2],(1-s*x)/2,k);
##   Q:=2^(-n)*hyperterm([-n,n],[1/2],(1-x)/2,k);
##   L:=proc(f,x) diff(f,x); end proc:
##   ConRec(P,Q,n,k,x,x,L,`shiftP`,n,m); 

ConRecq:=proc(P,Q,qn,k,x,t,Ls,shift,varm,varn,q)
local L,Lp,lsp,lsq,lspp,lsqp,lsps,lsqs,re,R;

  ## Ls is either an operator L,
  ## or it is the list of two operators [L, Lp]
  
  if type(Ls,list) then
    L:=Ls[1]; Lp:=Ls[2];
  else
    L:=Ls; Lp:=0;
  fi;

  ## the 3-term recurrences of P and Q
  re:=qExt_Zeil([x*P,subs(qn=qn*q,P),P,subs(qn=qn/q,P)],k,q,[t]);
  lsp:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

  re:=qExt_Zeil([x*Q,subs(qn=qn*q,Q),Q,subs(qn=qn/q,Q)],k,q,[t]);
  lsq:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

  ## the 3-term recurrences of LP and LQ
  R:=qhyper_simp(L(P,t));
  re:=qExt_Zeil([x*R,subs(qn=qn*q,R),R,subs(qn=qn/q,R)],k,q,[t]);
  lspp:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

  R:=qhyper_simp(L(Q,t));
  re:=qExt_Zeil([x*R,subs(qn=qn*q,R),R,subs(qn=qn/q,R)],k,q,[t]);
  lsqp:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

  if shift=`shiftP` then
    if Lp<>0 then
      re:=qExt_Zeil([qhyper_simp(Lp(P,t)),subs(qn=qn*q,P),P,subs(qn=qn/q,P)],k,q,[t]);
      lsps:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];
    
      re:=qExt_Zeil([qhyper_simp(Lp(Q,t)),subs(qn=qn*q,Q),Q,subs(qn=qn/q,Q)],k,q,[t]);
      lsqs:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

      return(recgenMq(lsp,lsq,lspp,lsqp,qn,varm,varn,lsps,lsqs,q));
    else
      return(recgenMq(lsp,lsq,lspp,lsqp,qn,varm,varn,q));
    fi;
  else
    if Lp<>0 then
      re:=qExt_Zeil([qhyper_simp(Lp(P,t)),subs(qn=qn*q,P),P,subs(qn=qn/q,P)],k,q,[t]);
      lsps:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];
    
      re:=qExt_Zeil([qhyper_simp(Lp(Q,t)),subs(qn=qn*q,Q),Q,subs(qn=qn/q,Q)],k,q,[t]);
      lsqs:=[-re[2]/re[1],-re[3]/re[1],-re[4]/re[1]];

      return(recgenNq(lsp,lsq,lspp,lsqp,qn,varm,varn,lsps,lsqs,q));
    else
      return(recgenNq(lsp,lsq,lspp,lsqp,qn,varm,varn,q));
    fi;
  fi; 

end proc:
    





## compute the coefficients in the three-term relations
## The input:
## hypergeometric term 'P' on variable 'la' which is a polynomial in 'x'
## the order of the polynomial is 'n', the summation index is 'k'
## returen the recurrence
## la*P_n(la) = c[1]*P_{n+1}(la) + c[2]*P_n(la) + c[3]*P_{n-1}(la)
## 
tr_coe:=proc(P,la,n,k,x)
local re;

     re:=Ext_Zeil([la*P, subs(n=n+1,P), P, subs(n=n-1, P)], k, [x]);
     return([-re[2]/re[1], -re[3]/re[1], -re[4]/re[1]]);
end proc:


recgenM:=proc(recp,recq,recpp,recqp,var,m,n)

  local c11,c12,b1,c21,c22,b2,res,u,v,
        delta,xi,eta,deltap,xip,etap,detc,
  recps,recqs,c31,c32,b3;

  c11:=subs(var=n-1,recq[1]): # u_{n-1}
  c12:=subs(var=n+1,recq[3]): # w_{n+1}
  b1:=[subs(var=m,recp[1]), 
        subs(var=m,recp[2])-subs(var=n,recq[2]),
        subs(var=m,recp[3])]; # right hand side of (2.3)

  c21:=subs(var=n-1,recqp[1]): # u'_{n-1}
  c22:=subs(var=n+1,recqp[3]): # w'_{n+1}
  b2:=[subs(var=m,recpp[1]), 
        subs(var=m,recpp[2])-subs(var=n,recqp[2]),
        subs(var=m,recpp[3])]; # right hand side of (2.4)

  
  detc:=factor(c11*c22-c12*c21);
  if detc=0 then
    return([seq(c11*b2[k]-c21*b1[k],k=1..3)]);
  else
    u:=map(factor, [seq((c22*b1[k]-c12*b2[k])/detc,k=1..3)]);  # (2.5)
    v:=map(factor, [seq((-c21*b1[k]+c11*b2[k])/detc,k=1..3)]); # (2.6)
      
    if nargs=7 then  # no sigma(x)

      delta:=factor(u[1]): xi:=factor(u[2]):
      eta:=factor(u[3]):

      deltap:=factor(v[1]): xip:=factor(v[2]):
      etap:=factor(v[3]):

      return(map(factor,[subs(n=n+1,delta)*subs(m=m+1,deltap),
          subs(n=n+1,delta)*subs(m=m+1,xip)+subs(n=n+1,xi)*deltap,
          subs(n=n+1,delta)*subs(m=m+1,etap)+subs(n=n+1,xi)*xip
             +subs(n=n+1,eta)*subs(m=m-1,deltap)-1,
          subs(n=n+1,xi)*etap+subs(n=n+1,eta)*subs(m=m-1,xip),
          subs(n=n+1,eta)*subs(m=m-1,etap)]));
	  
    elif nargs=9 then # with sigma(x)
    
      recps:=args[8]: recqs:=args[9]:
      c31:=subs(var=n-1,recqs[1]): # u''_{n-1}
      c32:=subs(var=n+1,recqs[3]): # w''_{n+1}
      b3:=[subs(var=m,recps[1]),
             subs(var=m,recps[2])-subs(var=n,recqs[2]),
             subs(var=m,recps[3])]; # right hand side of (2.8)
	     
      return(map(factor,[seq(c31*u[k]+c32*v[k]-b3[k],k=1..3)]));
    fi;
  fi;

end proc:


recgenN:=proc(recp,recq,recpp,recqp,var,m,n)

  local c11,c12,b1,c21,c22,b2,res,u,v,
        delta,xi,eta,deltap,xip,etap,detc,
  recps,recqs,c31,c32,b3;

  c11:=subs(var=m,recp[1]):
  c12:=subs(var=m,recp[3]):
  b1:=[subs(var=n-1,recq[1]),
        subs(var=n,recq[2])-subs(var=m,recp[2]),
        subs(var=n+1,recq[3])];

  c21:=subs(var=m,recpp[1]):
  c22:=subs(var=m,recpp[3]):
  b2:=[subs(var=n-1,recqp[1]),
        subs(var=n,recqp[2])-subs(var=m,recpp[2]),
        subs(var=n+1,recqp[3])];

  detc:=factor(c11*c22-c12*c21);
  if detc=0 then
    return([seq(c11*b2[k]-c21*b1[k],k=1..3)]);
  else
    u:=[seq((c22*b1[k]-c12*b2[k])/detc,k=1..3)];
    v:=[seq((-c21*b1[k]+c11*b2[k])/detc,k=1..3)];
      
    if nargs=7 then

      delta:=factor(u[1]): xi:=factor(u[2]):
      eta:=factor(u[3]):

      deltap:=factor(v[1]): xip:=factor(v[2]):
      etap:=factor(v[3]):

      return(map(factor,[subs(m=m-1,eta)*subs(n=n+1,etap),
          subs(m=m-1,xi)*etap+subs(m=m-1,eta)*subs(n=n+1,xip),
          subs(m=m-1,delta)*subs(n=n-1,etap)+subs(m=m-1,xi)*xip
             +subs(m=m-1,eta)*subs(n=n+1,deltap)-1,
          subs(m=m-1,delta)*subs(n=n-1,xip)+subs(m=m-1,xi)*deltap,
          subs(m=m-1,delta)*subs(n=n-1,deltap)]));
  
    elif nargs=9 then

      recps:=args[8]: recqs:=args[9]:

      c31:=subs(var=m,recps[1]):
      c32:=subs(var=m,recps[3]):
      b3:=[subs(var=n-1,recqs[1]),
             subs(var=n,recqs[2])-subs(var=m,recps[2]),
             subs(var=n+1,recqs[3])];

      return(map(factor,[seq(c31*u[4-k]+c32*v[4-k]-b3[4-k],k=1..3)]));
    fi;
  fi;

end proc:


recgenMq:=proc(recp,recq,recpp,recqp,var,qm,qn,q)

  local c11,c12,b1,c21,c22,b2,res,u,v,
        delta,xi,eta,deltap,xip,etap,detc,
  recps,recqs,c31,c32,b3;

  c11:=subs(var=qn/q,recq[1]): # u_{n-1}
  c12:=subs(var=qn*q,recq[3]): # w_{n+1}
  b1:=[subs(var=qm,recp[1]), 
        subs(var=qm,recp[2])-subs(var=qn,recq[2]),
        subs(var=qm,recp[3])]; # right hand side of (2.3)

  c21:=subs(var=qn/q,recqp[1]): # u'_{n-1}
  c22:=subs(var=qn*q,recqp[3]): # w'_{n+1}
  b2:=[subs(var=qm,recpp[1]), 
        subs(var=qm,recpp[2])-subs(var=qn,recqp[2]),
        subs(var=qm,recpp[3])]; # right hand side of (2.4)

  
  detc:=factor(c11*c22-c12*c21);
  if detc=0 then
    print("D=0");
    return([seq(c11*b2[k]-c21*b1[k],k=1..3)]);
  else
    u:=map(factor, [seq((c22*b1[k]-c12*b2[k])/detc,k=1..3)]);  # (2.5)
    v:=map(factor, [seq((-c21*b1[k]+c11*b2[k])/detc,k=1..3)]); # (2.6)
      
    if nargs=8 then  # no sigma(x)

      delta:=factor(u[1]): xi:=factor(u[2]):
      eta:=factor(u[3]):

      deltap:=factor(v[1]): xip:=factor(v[2]):
      etap:=factor(v[3]):

      return(map(factor,[subs(qn=qn*q,delta)*subs(qm=qm*q,deltap),
          subs(qn=qn*q,delta)*subs(qm=qm*q,xip)+subs(qn=qn*q,xi)*deltap,
          subs(qn=qn*q,delta)*subs(qm=qm*q,etap)+subs(qn=qn*q,xi)*xip
             +subs(qn=qn*q,eta)*subs(qm=qm/q,deltap)-1,
          subs(qn=qn*q,xi)*etap+subs(qn=qn*q,eta)*subs(qm=qm/q,xip),
          subs(qn=qn*q,eta)*subs(qm=qm/q,etap)]));
	  
    elif nargs=10 then # with sigma(x)
    
      recps:=args[9]: recqs:=args[10]:
      c31:=subs(var=qn/q,recqs[1]): # u''_{n-1}
      c32:=subs(var=qn*q,recqs[3]): # w''_{n+1}
      b3:=[subs(var=qm,recps[1]),
             subs(var=qm,recps[2])-subs(var=qn,recqs[2]),
             subs(var=qm,recps[3])]; # right hand side of (2.8)
	     
      return(map(factor,[seq(c31*u[k]+c32*v[k]-b3[k],k=1..3)]));
    fi;
  fi;

end proc:


recgenNq:=proc(recp,recq,recpp,recqp,var,qm,qn,q)

  local c11,c12,b1,c21,c22,b2,res,u,v,
        delta,xi,eta,deltap,xip,etap,detc,
  recps,recqs,c31,c32,b3;

  c11:=subs(var=qm,recp[1]):
  c12:=subs(var=qm,recp[3]):
  b1:=[subs(var=qn/q,recq[1]),
        subs(var=qn,recq[2])-subs(var=qm,recp[2]),
        subs(var=qn*q,recq[3])];

  c21:=subs(var=qm,recpp[1]):
  c22:=subs(var=qm,recpp[3]):
  b2:=[subs(var=qn/q,recqp[1]),
        subs(var=qn,recqp[2])-subs(var=qm,recpp[2]),
        subs(var=qn*q,recqp[3])];

  detc:=factor(c11*c22-c12*c21);
  if detc=0 then
    return([seq(c11*b2[k]-c21*b1[k],k=1..3)]);
  else
    u:=[seq((c22*b1[k]-c12*b2[k])/detc,k=1..3)];
    v:=[seq((-c21*b1[k]+c11*b2[k])/detc,k=1..3)];
      
    if nargs=8 then

      delta:=factor(u[1]): xi:=factor(u[2]):
      eta:=factor(u[3]):

      deltap:=factor(v[1]): xip:=factor(v[2]):
      etap:=factor(v[3]):

      return(map(factor,[subs(qm=qm/q,eta)*subs(qn=qn*q,etap),
          subs(qm=qm/q,xi)*etap+subs(qm=qm/q,eta)*subs(qn=qn*q,xip),
          subs(qm=qm/q,delta)*subs(qn=qn/q,etap)+subs(qm=qm/q,xi)*xip
             +subs(qm=qm/q,eta)*subs(qn=qn*q,deltap)-1,
          subs(qm=qm/q,delta)*subs(qn=qn/q,xip)+subs(qm=qm/q,xi)*deltap,
          subs(qm=qm/q,delta)*subs(qn=qn/q,deltap)]));
  
    elif nargs=10 then

      recps:=args[9]: recqs:=args[10]:

      c31:=subs(var=qm,recps[1]):
      c32:=subs(var=qm,recps[3]):
      b3:=[subs(var=qn/q,recqs[1]),
             subs(var=qn,recqs[2])-subs(var=qm,recps[2]),
             subs(var=qn*q,recqs[3])];

      return(map(factor,[seq(c31*u[4-k]+c32*v[4-k]-b3[4-k],k=1..3)]));
    fi;
  fi;

end proc:
