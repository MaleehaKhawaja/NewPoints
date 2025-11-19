X:=SimplifiedModel(SmallModularCurve(23));
J:=Jacobian(X);
MordellWeilGroup(J); //We know J(Q)=Z/11Z by Bruin--Najman
ptsX:=Points(X: Bound:=10);
ptsX;

P1:=X![1,-1,0];
P2:=X![1,1,0]; 

assert Order(P1-P2) eq 11; //P1-P2 generates J(Q)

D0:=Place(X![1,1,0]);
D1:=Place(X![1,-1,0])-D0;

for a in [-5..5]
    do D := 3*D0 + a*D1;
    L, phi := RiemannRochSpace(D);
    dim := Dimension(L);
    assert dim eq 2;
end for;

Qu<u>:=FunctionField(Rationals());
Qux<x>:=PolynomialRing(Qu);

X:=HyperellipticCurve(x^6 - 8*x^5 + 2*x^4 + 2*x^3 - 11*x^2 + 10*x- 7);

D0:=Place(X![1,1,0]);
D1:=Place(X![1,-1,0])-D0;

for a in [-5..5] do	
    D:=a*D1+3*D0;
    L,phi:=RiemannRochSpace(D);
    if Dimension(L) eq 2 then
        if #Decomposition(D+Divisor(phi(u*L.1+L.2))) eq 1 then
            E := Decomposition(D+Divisor(phi(u*L.1+L.2)))[1,1];
            F := ResidueClassField(E);
            f := MinimalPolynomial(F.1);
            assert Degree(f) eq 3;
            disc := Discriminant(f);
            f1 := Numerator(disc);
            f2 := Denominator(disc);
            facts1:=Factorisation(f1);
            facts2:=Factorisation(f2);
            facts1:=[ <pr[1],(Integers()!pr[2]) mod 2>  : pr in facts1];
            facts2:=[ <pr[1],(Integers()!pr[2]) mod 2>  : pr in facts2];
            facts:=facts1 cat facts2;
            g:=&*[pr[1]^Integers()!pr[2] : pr in facts];
            c1:=LeadingCoefficient(f1);
            c2:=LeadingCoefficient(f2);
            p:=c1*c2;
            p:=p*Denominator(p)^2;
            p:=Squarefree(Integers()!p);
            g:=p*g;
            d:=LCM([ Denominator(r)  : r in Coefficients(g)]);
            s,t:=Squarefree(d);
            //g is the squarefree part of the discriminant of the number field.
            g:=s^2*t^2*g;
            print "The squarefree part of the discriminant is", g;
            assert IsSquare(disc/g);
            assert IsEven(Degree(g));
            G:=GaloisGroup(g);
            print "a = ", a;
            print "The Galois group of g is", G;
            cycles:=[CycleDecomposition(g) : g in G];
            //Want to check if all elements of the Galois group contain a 1-cycle.
            //If this is true then no element of the Galois group G acts freely on the roots of g.
            if forall(g){c : c in cycles | exists(i){j : j in [1..#c] | #c[j] eq 1}}
                then print "Every element of Galois group has a 1-cycle";
            else print "There is an element of the Galois group acting freely on the roots of g.";
            end if;
            print "+++++++++++++++++++++++++++++++++++++++++++++++";
        end if;
    end if;
end for;
