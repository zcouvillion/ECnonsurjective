
_<t>:=PolynomialRing(Rationals());
Qbar:=AlgebraicClosure(Rationals());


AbsoluteCharacterBound := function(K,K_units,units_map, embeddings, weights)
    
    gens:=Generators(K_units);
    
    gen_list:=[a : a in gens];
    
    norm_list:=[];
    
    for u in [1..#gen_list] do
    
        alpha:=units_map(gen_list[u]);
        
        charVal:=1;
        for i in [1..#embeddings] do
            charVal := charVal * (embeddings[i](alpha)^weights[i]);
        end for;
        
        norm_list[u]:=Integers()! Norm(charVal - 1);
        //norm_list[u];
        
    end for;
    
    return Gcd(norm_list);
    
end function;

AlgCharacters := function(K)

    rr:=Roots(DefiningPolynomial(K), Qbar);
    embeddings := [*hom<K -> Qbar | r[1]>: r in rr *];

    d:= Degree(K);
    K_units,units_map:=UnitGroup(K);

    L:=CartesianProduct([{0,1} : i in [1..d]]);
    chars:=[b : b in L];
    
    alglist:=[[0]];
    alg_count:=0;
    M:=1;
    
    for char in chars do

        char12:= [12*b: b in char];
        M_char12:=AbsoluteCharacterBound(K,K_units,units_map, embeddings, char12);
        
        if M_char12 eq 0 then
            alg_count:=alg_count+1;
            alglist[alg_count]:=[a: a in char];
            //print char;
        else
            M:=M*M_char12;
            //print M_char12;
        end if;
        
    end for;
    
    return alglist, M;

end function;

TestCharacter := function(p,frob,h_K,embeddings, Cn_sign)
    
    truth, gen:= IsPrincipal(p^h_K);
    
    charVal:=Qbar!1;
    for i in [1..#Cn_sign] do
        charVal := charVal * (Qbar!embeddings[i](gen)^Cn_sign[i]);
    end for;
    
    rts:=Roots(frob,Qbar);
    j:=#rts;
    
    r1:=rts[1][1];
    r2:=rts[j][1];
    
    val:= ( r1^(12*h_K) - charVal^12)*( r2^(12*h_K) - charVal^12);
    //val:= ( r1^(12*h_K) - charVal^12);
    
    //print Norm(val);
    return Integers()!Norm(val);

end function;

AuxiliaryPrimes := function(E,B,O_K)

    //bad := PrimeDivisors(Integers()! Norm(Discriminant(E)));
   
    list:=[];
    
    //print E, O_K;
    
    c:=1;
    for p in PrimesUpTo(B) do
        //print p;
        if Integers()! Norm(Discriminant(E)) mod p eq 0 then
            continue;
        end if;
        
        I:=ideal<O_K | p>;
        f:=Factorization(I);
            
        for q in f do
            list[c]:=q[1];
            //print q[1];
            c:=c+1;
        end for;
        
    end for;
    
    return list;

end function;



FrobPoly:=function(E,p)
    K:=BaseRing(E);

    coeffs:=Coefficients(E);
    O_K:=MaximalOrder(K);

    F,phi:=ResidueClassField(p);
    
    coeffsp:=[];
        
        
    for j in [1..#coeffs] do
        
            coeffsp[j]:= phi(( (O_K ! coeffs[j]) mod p));
       
        
    end for;
    
    
    
    Ep:=EllipticCurve(coeffsp);
        
    a_p:=TraceOfFrobenius(Ep);
    return t^2 - a_p*t + Norm(p), a_p;

end function;

ComputeFrobs := function(E,aux_primes)
    frobs:=[];
    traces:=[];

    for c in [1..#aux_primes] do
        frobs[c],traces[c]:=FrobPoly(E,aux_primes[c]);
    end for;
    
    return frobs, traces;

end function;


ReducibleTest := function(primes,frobs, K, h_K: stat:=false,algebraic_chars:=[], unbal:=-1)

    rr:=Roots(DefiningPolynomial(K), Qbar);
    embeddings := [*hom<K -> Qbar | r[1]>: r in rr *];

    d:= Degree(K);

    sigs:=[];
    
    if unbal eq -1 then
        L:=CartesianProduct([{0,1} : i in [1..d]]);
        sigs:=[b : b in L];
    else
        sigs:=algebraic_chars;
    end if;

    sigvals := [];
    
    for index in [1..#sigs] do
    
        signature:=sigs[index];
        
        vals:=[];
        
        for p_0 in [1..#primes] do
            p:=primes[p_0];
            frob:=frobs[p_0];
            
          vals[p_0]:=p_0*TestCharacter(p,frob,h_K,embeddings, signature);
          
        end for;
        
        sigvals[index]:=Gcd(vals);
        
        if stat eq true then
              print "Character: ", signature, " checked.";
              print sigvals[index];
        end if;
        
        
    
    end for;


    return sigvals;
end function;



ComputeFiniteConductor := function(E,O_K);

    K:=BaseRing(E);
    
    D:=Discriminant(E);
    
    C:=ideal<O_K|1>;
    
    I:=ideal<O_K|D>;
    
    fact:=Factorization(I);
    for f in fact do
        
         s:=KodairaSymbol(E,f[1]);
         //print Norm(f[1]), s;
         if s ne KodairaSymbol("I0") and s ne KodairaSymbol("In") then
             I_p:=f[1];
             if Norm(I_p) mod 2 eq 0 then
                 I_p := I_p * I_p;
             end if;
             
             C:=C* I_p;
         end if;
    end for;
        
    return C;

end function;


NormalizerCartan := function(primes, traces, r , fin_conductor)

    T:=[ i : i in [1..r] ];
    
    G,map:=RayClassGroup(fin_conductor,T);
    
    H:=sub<G|Id(G)>;
    
    //print fin_conductor, G;

    M:=1;
    
    for i in [1..#primes] do
    
        if H eq G then
            return M;
        end if;
    
       // print traces[i];
    
        if traces[i] eq 0 then
            continue;
        end if;
    
        p := primes[i];
        g:=p @@ map;
        
        if g in H or traces[i] eq 0 then
            continue;
        end if;
        
        p_char:=PrimeDivisors(Integers()!Norm(p))[1];
        M:=traces[i] * M * p_char;
       
        H:=sub<G|H,g>;
        
        
    end for;

return 0;

end function;

ReduciblePrimes := function(E, B);

    K:=BaseRing(E);
    
    E:=IntegralModel(E);
    
    r,s:=Signature(K);
    h_K:=ClassNumber(K);
    O_K:=MaximalOrder(K);
    primes:=AuxiliaryPrimes(E,B,O_K);
    frobs, traces:=ComputeFrobs(E,primes);
     
    susdivisor := 2 * 3 * 5;
    
    D:=Integers()! Norm(Discriminant(E))* Integers()!Numerator(Discriminant(K));
   
    
    for p in PrimeDivisors(D) do
        susdivisor := susdivisor * p;
    end for;
 
    
    alg :=[[0]];
    unbalanced:=-1;
    
    CharList:=ReducibleTest(primes,frobs,K,h_K: unbal:=unbalanced);
    
    for char in CharList do
        susdivisor:=susdivisor * char;
    end for;
    
    if susdivisor eq 0 then
        return -1, [];
    end if;
    
    susprimes := PrimeDivisors(susdivisor);
    
    return 0, susprimes;


end function;


NonsurjectivePrimes := function(E, B: verb:=false, alg_chars:=false)

    K:=BaseRing(E);
    
    E:=IntegralModel(E);
    
    r,s:=Signature(K);
    h_K:=ClassNumber(K);
    O_K:=MaximalOrder(K);
    primes:=AuxiliaryPrimes(E,B,O_K);
    frobs, traces:=ComputeFrobs(E,primes);
     
    susdivisor := 2 * 3 * 5;
    
    D:=Integers()! Norm(Discriminant(E))* Integers()!Numerator(Discriminant(K));
   
   
    for p in PrimeDivisors(D) do
         susdivisor := susdivisor * p;
    end for;
   
    
    alg :=[[0]];
    unbalanced:=-1;
    
    if alg_chars eq true then
        alg,unbalanced := AlgCharacters(K);
        susdivisors := susdivisor*unbalanced;
    end if;
    
    CharList:=ReducibleTest(primes,frobs,K,h_K:stat:=verb, algebraic_chars:=alg, unbal:=unbalanced);
    
    if verb eq true then
        print "Characters checked.";
    end if;
    
    for char in CharList do
        susdivisor:=susdivisor * char;
    end for;
    
    normalizer:=NormalizerCartan(primes, traces, r,ComputeFiniteConductor(E,O_K));
    
    if verb eq true then
        print "Normalizer considered.";
        print normalizer;
    end if;
    
    
    susdivisor := normalizer * susdivisor;
    if susdivisor eq 0 then
        print "Error: could not rule out any primes.";
        return -1,[];
    end if;
    
    susprimes:=PrimeDivisors(susdivisor);

    return 0, susprimes;

end function;


