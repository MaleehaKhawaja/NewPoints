X:=SimplifiedModel(SmallModularCurve(29));
J:=Jacobian(X);
MordellWeilGroup(J); //We know J(Q)=Z/7Z by Bruin--Najman
ptsX:=Points(X: Bound:=10);
ptsX;

assert Order(X![1,-1,0] - X![1,1,0]) eq 7;

D0:=Place(X![1,1,0]);
D1:=Place(X![1,-1,0]);

for a in [0..6]
    do D := 3*D0 + a*(D1-D0);
    L, phi := RiemannRochSpace(D);
    dim := Dimension(L);
    assert dim eq 2;
end for;

Qu<u>:=FunctionField(Rationals());
Qux<x>:=PolynomialRing(Qu);

X:=HyperellipticCurve(x^6 - 4*x^5 - 12*x^4 + 2*x^3 + 8*x^2 + 8*x - 7);

D0:=Place(X![1,1,0]);
D1:=Place(X![1,-1,0]);

for a in [0..6] do	
    D:=a*(D1-D0)+3*D0;
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
            g:=s^2*t^2*g;
            assert IsSquare(disc/g);
            print "a=", a;
            print "The squarefree part of the discriminant is g =", g;
            if Degree(g) eq 0 then
                print "The discriminant is constant.";
            else
                G:=GaloisGroup(g);
	    	    print "The Galois Group of g is", G;
            	cycles:=[CycleDecomposition(g) : g in G];
            	//Want to check if all elements of the Galois group contain a 1-cycle.
            	if forall(g){c : c in cycles | exists(i){j : j in [1..#c] | #c[j] eq 1}}
                	then print "Every element of Galois group has a 1-cycle";
                else print "There is an element of the Galois group acting freely on the roots of g.";
            	end if;
            end if;
            print "++++++++++++++++++++";
        end if;
    end if;
end for;
