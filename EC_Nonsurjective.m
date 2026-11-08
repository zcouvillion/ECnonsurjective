
_<t>:=PolynomialRing(Rationals());
Qbar:=AlgebraicClosure(Rationals());



/*
    Input: Elliptic curve E, integer bound B, maximal order O_K
    Output: a list of primes of characteristic up to B where the given model of E has good reduction
*/

AuxiliaryPrimes := function(E,B,O_K)

    //bad := PrimeDivisors(Integers()! Norm(Discriminant(E)));
   
    list:=[];
    
    //print E, O_K;
    
    D:=Integers()!Norm(Discriminant(E));
    
    c:=1;
    for p in PrimesUpTo(B) do
        //print p;
        if D mod p eq 0 then
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


/*
    Input: an elliptic curve E, a prime ideal p, optional: maximal order max_ord
    Output: The Frobenius polynomial for the elliptic curve at the given prime ideal, the trace of Frobenius
*/

FrobPoly:=function(E,p:max_ord:=-1)
    K:=BaseRing(E);

    coeffs:=Coefficients(E);
    O_K := max_ord;
    if Type(O_K) eq RngIntElt then
        O_K:=MaximalOrder(K);
    end if;

    F,phi:=ResidueClassField(p);
    
    coeffsp:=[];
        
        
    for j in [1..#coeffs] do
        
            coeffsp[j]:= phi(( (O_K ! coeffs[j]) mod p));
       
        
    end for;
    
    
    
    Ep:=EllipticCurve(coeffsp);
        
    a_p:=TraceOfFrobenius(Ep);
    return t^2 - a_p*t + Norm(p), a_p;

end function;

/* 
    Input: Elliptic curve E, auxiliary list of primes aux_primes, optional: maximal order max_o
    Output: list of Frobenius polynomials, list of Frobenius traces for E at the given primes
*/


ComputeFrobs := function(E,aux_primes:max_o:=-1)
    frobs:=[];
    traces:=[];

    for c in [1..#aux_primes] do
        frobs[c],traces[c]:=FrobPoly(E,aux_primes[c]:max_ord:=max_o);
    end for;
    
    return frobs, traces;

end function;


/*
Input: Elliptic curve E
Output: set of primes where E has additive reduction, set of primes where E has bad reduction
*/

AdditivePrimes := function(E)

    N:=Conductor(E);
    fact:=Factorization(N);
    
    p_set := {};
    bad_set := {};
    
    for f in fact do
        bad_set := bad_set join {PrimeDivisors(Integers()!Norm(f[1]))[1]};
        if f[2] gt 1 then
            p_set := p_set join {f[1]};
        end if;
    end for;
    
    if #p_set eq 0 then
        if #fact ne 0 then
            p_set := {fact[1][1]};
            p_set := p_set diff p_set;
        else
            O_K:=MaximalOrder(BaseRing(E));
            p_set := {Factorization(ideal<O_K|2>)[1][1]};
            p_set := p_set diff p_set;
        end if;
    end if;
    
    return p_set, bad_set;

end function;

/*
Input: a list of prime ideals, a list of Frobenius traces, a list of the additive primes of E, maximal order O_K
Output: a set of primes containing all primes ell where the mod ell representation is geometrically imprimitive, not counting the places where E has bad reduction or are ramified in K, or 2, 3, or 5
*/

ImprimitivePrimes := function(primes, traces, additive_primes, O_K)
    
    G,m:= pSelmerGroup(2,additive_primes);
    
    //print #G;
    
    gens := Generators(G);
    gen_list:= [Inverse(m)(g) : g in gens];
    
    d:=#gen_list;
    
    V:=VectorSpace(GF(2), d);
    basis := [];
    W:= sub<V|basis>;
    
    trace_list:=[];
    trace_count:=0;
    
    for i in [1..#primes] do
    
        if PrimeDivisors(Integers()!Norm(primes[i]))[1] eq 2 then
            continue;
        end if;
        
        //print Norm(primes[i]), traces[i];
        
        if traces[i] eq 0 then
            continue;
        end if;
    
        vec := [];
        next_one := false;
        for j in [1..#gen_list] do
        
            l := LegendreSymbol(O_K!gen_list[j], primes[i]);

            if l eq 0 then
                next_one := true;
                break;
            end if;

            if l eq 1 then
                vec[j] := 0;
            else
                vec[j] := 1;
            end if;
        
        end for;
        
        if next_one eq true then
            continue;
        end if;
        
        v := V ! vec;
        
        if v notin W then
        
            W:=sub<V | W,v>;
            trace_count:=trace_count + 1;
            trace_list[trace_count]:=traces[i];
            
            if W eq V then
                break;
            end if;
        
        end if;
        
    end for;
    
    if W ne V then
        return {0};
    end if;
    
    sus_primes := {};
    for tr in trace_list do
        sus_primes := sus_primes join {ell: ell in PrimeDivisors(tr)};
    end for;
    
    return sus_primes;
    
end function;

/*
Input: Elliptic curve E, an integer bound B, Optional: the set additive_prime_set of places where E has additive reduction, the set bad_prime_set of places where E has bad reduction, a list prime_list of prime ideals and a list trace_list of Frobenius traces to use
Output: the set of primes ell where E may be geometrically imprimitive ({0} if failure), the set of bad primes of E
*/

ComputeImprimitivePrimes:=function(E,B:additive_prime_set:={},bad_primes_set:={}, prime_list := [], trace_list :=[])
     K:=BaseRing(E);
   
     O_K := MaximalOrder(K);
  
    
    primes:=prime_list;
    traces := trace_list;
    
    if #trace_list eq 0 then
        primes:=AuxiliaryPrimes(E,B,O_K);
        frobs, traces:=ComputeFrobs(E,primes : max_o:=O_K);
    end if;
    additive_primes:=additive_prime_set;
    bad_set:=bad_primes_set;
    
    if #bad_primes_set eq 0 or #additive_prime_set eq 0 then
        additive_primes, bad_set := AdditivePrimes(E);
    end if;
    //print additive_primes;
    
     D:=Integers()!Numerator(Discriminant(K));
    bad_set := bad_set join {p: p in PrimeDivisors(D)};
    bad_set := bad_set join {2,3, 5};
    
    return ImprimitivePrimes(primes,traces,additive_primes,O_K), bad_set;
    
end function;



/*

    Input: Elliptic curve E, an integer bound B
    Optional: embeddings of K into Qbar (embeddings), maximal order of K (max_order), some auxiliary data computed in ReduciblePrimes meant for recycling information (prime_data), optional extra printed text (verb), the set of primes where E has bad reduction (bad_primes), a list prime_list of primes and a list frob_list of Frobenius polynomials to use instead of computing Frobenius polynomials up to the bound B
    Output: an integer success flag, set of primes containing those where rho_{E,ell} is geometrically reducible ({0} if failed), subset of aformentioned primes not necessarily including the primes of bad reduction or primes where K is ramified, embeddings of K into Qbar, auxiliary prime data meant to be recycled, maximal order of K meant to be recycled.
    
*/

ReduciblePrimes := function(E, B: embeddings:=[* *],max_order:=-1,prime_data:=[* *], v:=false, bad_primes:={}, prime_list :=[], frob_list :=[]);

   
    K:=BaseRing(E);
     d:=Degree(K);
    
       
    O_K := max_order;
    if Type(O_K) eq RngIntElt then
        O_K:=MaximalOrder(K);    
    end if;
    
    new_embeddings:=embeddings;
    prime_data_new:=prime_data;
    
    if O_K ne MaximalOrder(K) then
        new_embeddings := [* *];
        prime_data_new:= [* *];
        O_K:=MaximalOrder(K);
    end if;
    
    
    
    if #new_embeddings eq 0 then
        rr:=Roots(DefiningPolynomial(K), Qbar);
        new_embeddings := [*hom<K -> Qbar | r[1]>: r in rr *];
    end if;
    
    bad_set:=bad_primes;
    
    if #bad_primes eq 0 then
    
        additive_primes, bad_set := AdditivePrimes(E);
    end if;
    
    primes:=prime_list;
    frobs:=frob_list;
    
    if #frobs eq 0 then  
        primes:=AuxiliaryPrimes(E,B,O_K);
        frobs, traces:=ComputeFrobs(E,primes : max_o:=O_K);
    end if;
     
    susdivisor := 2 * 3 * 5;
    
    susdivisor:= susdivisor*(Integers()!Numerator(Discriminant(K)));
    for p in bad_set do
        susdivisor:=susdivisor*p;
    end for;
    

    
    L:=CartesianProduct([{0,1} : i in [1..d]]);
    sigs:=[b : b in L];
   
    sig_vals := [];
    
    for p_ind in [1..#primes] do
        p:=primes[p_ind];
        if IsPrincipal(p) eq false then
            continue;
        end if;
        
        res_char:=PrimeDivisors(Integers()!Norm(p))[1];
        frob:=frobs[p_ind];
        
        if IsDefined(prime_data_new, res_char) eq false then
            for j in [1..res_char] do
                if IsDefined(prime_data_new,j) eq false then
                    prime_data_new[j]:=[* *];
                end if;
            end for;
        end if;
        
        p_data_ind:=0;
        
        poly_list :=[];
        
        new_p_data_ind := -1;

        
        for i in [1..#prime_data_new[res_char]] do
            if IsDefined(prime_data_new[res_char][i],1) eq false then
                
                break;
            end if;
                        
            if prime_data_new[res_char][i][1] eq p then
                
                p_data_ind := i;
                new_p_data_ind := i;
                break;
            end if;
        end for;
        
        if new_p_data_ind eq -1 then
               new_p_data_ind := #prime_data_new[res_char]+1;
        end if;
        
        for sig_ind in [1..#sigs] do
            if IsDefined(sig_vals, sig_ind) eq false then
                sig_vals[sig_ind]:=0;
            end if;
            
            signature:=sigs[sig_ind];
            sig_key:=0;
            for i in [1..#signature] do
                sig_key:=sig_key + 2^(i-1)*signature[i];
            end for;
            sig_key:=Integers()! (sig_key + 1);
            
            pol_p:=0;
            
            if p_data_ind ne 0 then
                //res_char, p_data_ind, sig_key;
            
                pol_p := prime_data_new[res_char][p_data_ind][2][sig_key];
            
            else 
                 truth, gen:= IsPrincipal(p);

                 charVal:=Qbar!1;
                 for i in [1..#signature] do
                    charVal := charVal * (Qbar!new_embeddings[i](gen)^(12*signature[i]));
                 end for;
            
                 pol_p:=MinimalPolynomial(charVal);
                 
                
                 prime_data_new[res_char][new_p_data_ind] := [* *];
                 
            end if;
            
            poly_list[sig_key] := pol_p;

             
            coeffs:=Coefficients(frob);
            b:=coeffs[1];
            a:=coeffs[2];
            
            b2:=b^12;
            a2:=(-a^12 + 12*a^10*b - 54*a^8*b^2 + 112*a^6*b^3 - 105*a^4*b^4 + 36*a^2*b^5 - 2*b^6);
           
            
            frob_12:=t^2 +a2*t + b2;
           
            
            sig_vals[sig_ind]:=Gcd(sig_vals[sig_ind], Integers()!(res_char*Resultant(pol_p,frob_12)));
        
        
        end for;
       
        
         
         prime_data_new[res_char][new_p_data_ind][1] := p;
         prime_data_new[res_char][new_p_data_ind][2] := poly_list;
        

    
    end for;
   
   char_div:=1;
   for i in [1..#sig_vals] do
        char := sig_vals[i];
        susdivisor:=susdivisor * char;
        char_div:=char_div*char;
        if v eq true then
            print "Character with key",i,"has value",char;
        end if;
   end for;
   
   if susdivisor eq 0 then
       return 1, {0},-1, new_embeddings, prime_data_new, O_K;
   end if;
   
    susprimes:=PrimeDivisors(susdivisor);
    charprimes:=PrimeDivisors(char_div);
    
    sus_set := {p : p in susprimes};
    char_set := {p : p in charprimes};
    
    D:=Integers()!Numerator(Discriminant(K));
    sus_set:=sus_set join {p: p in PrimeDivisors(D)};
   
    return 0, sus_set, char_set, new_embeddings, prime_data_new, O_K;

    

end function;

/*
    Input: Elliptic curve E, bound B, Optional: set verb := true for additional printed information
    Output: integer success flag, finite list of primes containing all nonsurjective primes. If unsuccessful, try increasing B.
*/

NonsurjectivePrimes := function(E, B: verb:=false)

    K:=BaseRing(E);
    
    E:=IntegralModel(E);
    
    O_K:=MaximalOrder(K);
    primes:=AuxiliaryPrimes(E,B,O_K);
    frobs, traces:=ComputeFrobs(E,primes);
     
    sus_set :=  {2,3,5};
    
    additive_primes, bad_prime_set :=AdditivePrimes(E);
    
   flag, sus_reducible, sus_without_bad_primes, embs, p_data, O_K := ReduciblePrimes(E,100: v:=verb, bad_primes := bad_prime_set, frob_list := frobs, prime_list := primes);
    
    
    sus_set := sus_set join sus_reducible;
    
    if flag eq 1 then
        print "Unable to rule out the reducible case.";
        return 1, _, embs,p_data,O_K;
    end if;    
    
    sus_im,bad := ComputeImprimitivePrimes(E,200:additive_prime_set := additive_primes,bad_primes_set:=bad_prime_set, prime_list := primes, trace_list := traces);
    
    if verb eq true then
        print "Reducible case ruled out for primes not in", (sus_set join bad);
    end if;
    
    if sus_im eq {0} then
        print "Unable to rule out the imprimitive case.";
        return 1, _, embs, p_data,O_K;
    end if;
    
    sus_set := sus_set join sus_im;
    
    if verb eq true then
        print "Imprimitive case ruled out for primes not in", (sus_im join bad);
    end if;

    sus_set := sus_set join bad;
    
    return 0, sus_set;

end function;


