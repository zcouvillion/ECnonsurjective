
_<t>:=PolynomialRing(Rationals());
Qbar:=AlgebraicClosure(Rationals());

/*
Input: a number field K
Output: the set \mathcal{X} and integer C_K from Section 4.2 of "COMPUTING THE NONSURJECTIVE PRIMES FOR ELLIPTIC CURVES OVER NUMBER FIELDS" 
*/

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

/*
    Input: prime ideal p, Frobenius polynomial at p, class number of K, embeddings of K into Qbar, a list of exponents
    Output: an integer supported at primes ell where the mod ell representation could be reducible and have a character with given exponents
*/

TestCharacter := function(p,frob,h_K,embeddings, Cn_sign )
    
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
        
    //print Norm(val);
    return Integers()!Norm(val);

end function;

/*
    Input: Elliptic curve, integer bound, maximal order of K
    Output: a set of primes of characteristic up to B where the given model of E has good reduction
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
    Input: Elliptic curve, a prime ideal, optional: maximal order of K
    Output: The Frobenius polynomial for the elliptic curve at the given prime ideal
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
    Input: Elliptic curve, auxiliary primes, optional: maximal order of K
    Output: list of Frobenius polynomials and list of Frobenius traces for E at the given primes
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
    Input: list of prime ideals, list of Frobenius polynomials, field K, class number of K
    Output: list of integers, one for each possible character describing a hypothetical one-dimensional subrepresentation. Primes dividing these integers are candidates for the mod ell representations being reducible.
*/

ReducibleTest := function(primes,frobs, K, h_K: stat:=false,algebraic_chars:=[], unbal:=-1, embeds :=[* *],prime_dat:=[* *])
    embeddings:=embeds;

    if #embeds eq 0 then
        rr:=Roots(DefiningPolynomial(K), Qbar);
        embeddings := [*hom<K -> Qbar | r[1]>: r in rr *];
    end if;
    
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

/*
    Input: Elliptic curve, maximal order of K
    Output: A modulus describing the ramification of a quadratic character for a normalizer of a Cartan image
*/

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

/*
    Input: primes, Frobenius traces, number of real places of K, output of ComputeFiniteConductor
    Output: Integer divisible by all primes ell where the mod ell representation may be in a normalizer of a Cartan but not in the Cartan
*/

NormalizerCartan := function(primes, traces, r , fin_conductor: v:=false)

    T:=[ i : i in [1..r] ];
    
    G,map:=RayClassGroup(fin_conductor,T);
    
    if v eq true then
        print G;
    end if;
    
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


/*

    Input: Elliptic curve E, an integer bound B
    Optional: embeddings of K into Qbar (embeddings), maximal order of K (max_ord), some auxiliary data computed in ReduciblePrimes meant for recycling information (prime_data), optional extra text (verb)
    Output: Success flag, set of primes containing those where rho_{E,ell} is geometrically reducible, set of aformentioned primes not necessarily including the primes of bad reduction or primes where K is ramified, embeddings of K into Qbar, auxiliary prime data meant to be recycled, maximal order of K.
    
*/

ReduciblePrimes := function(E, B: embeddings:=[* *],max_order:=-1,prime_data:=[* *], verb:=false);

   
    K:=BaseRing(E);
     d:=Degree(K);
    
    E:=IntegralModel(E);
       
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
    
    primes:=AuxiliaryPrimes(E,B,O_K);
    frobs, traces:=ComputeFrobs(E,primes : max_o:=O_K);
     
    susdivisor := 2 * 3 * 5;
    
    D:=Integers()! Norm(Discriminant(E))* Integers()!Numerator(Discriminant(K));
   
    
    for p in PrimeDivisors(D) do
        susdivisor := susdivisor * p;
    end for;
 
    
    alg :=[[0]];
    unbalanced:=-1;
    
    
    
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
   for char in sig_vals do
        susdivisor:=susdivisor * char;
        char_div:=char_div*char;
        if verb eq true then
            print char;
        end if;
   end for;
   
   if susdivisor eq 0 then
       return 0, -1,-1, new_embeddings, prime_data_new, O_K;
   end if;
   
    susprimes:=PrimeDivisors(susdivisor);
    charprimes:=PrimeDivisors(char_div);
   
   
   

    
   
    return 0, susprimes, charprimes, new_embeddings, prime_data_new, O_K;

    

end function;

/*
    Input: Elliptic curve E, bound B
    Output: success flag, finite list of primes containing all nonsurjective primes (if successful), or -1, [] if unsuccessful
*/

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
    
    normalizer:=NormalizerCartan(primes, traces, r,ComputeFiniteConductor(E,O_K): v:=verb);
    
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


