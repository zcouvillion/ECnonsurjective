load "EC_Nonsurjective.m";

_<T>:= PolynomialRing(Rationals());

/*
Running example of "Computing the nonsurjective primes for elliptic curves over number fields."
*/

_<i>:= NumberField(T^2+1);
E:= EllipticCurve([i+1,-i,0,7,6*i]);
flag, primes := NonsurjectivePrimes(E,100);
print primes;

/*
Elliptic curve with LMFDB label 6.6.485125.1-81.2-b3
*/

K<a> := NumberField(Parent(T)![1, -5, 2, 8, -4, -2, 1]);
E := EllipticCurve([K![-2,2,4,-4,-1,1],K![3,-7,-7,5,2,-1],K![1,-5,-3,5,1,-1],K![6,-12,-3,25,0,-7],K![26,-113,-11,195,-4,-52]]);
flag, primes := NonsurjectivePrimes(E,100);
print primes;
