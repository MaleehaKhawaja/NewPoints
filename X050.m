X:=SmallModularCurve(50);
X:=SimplifiedModel(X);
J:=Jacobian(X);
assert #MordellWeilGroup(J) eq 15;

ptsJ:=Points(J:Bound:=10);
ptsX:=Points(X:Bound:=10);

P:=X![1,-1,0];
P0:=X![1,1,0];

assert Order(P-P0) eq 15;

D1:=Place(X![1,-1,0])-Place(X![1,1,0]);
infdiv:=Place(X![1,1,0]);

for a in [0..14]
    do D := 3*infdiv + a*D1;
    L, phi := RiemannRochSpace(D);
    dim := Dimension(L);
    assert dim eq 2;
end for;

Qu<u> := FunctionField(Rationals());
Qux<x> := PolynomialRing(Qu);

X:=HyperellipticCurve(x^6 - 4*x^5 - 10*x^3 - 4*x + 1);

D1:=Place(X![1,-1,0])-Place(X![1,1,0]);
infdiv:=Place(X![1,1,0]);

for a in [0..14] do	
    D:=a*D1+3*infdiv;
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
            if Degree(g) eq 0 then
                if g eq 1 then
                    print "discriminant is a square";
                    pts:=[ [u1,0,v1] : u1,v1 in [-5..5] | {u1,v1} ne {0} and GCD(u1,v1) eq 1];
                    else
                    print "discriminant is never a square";
                    pts:=[];
                end if;
            else
                H:=HyperellipticCurve(g);
                pts:=Points(H : Bound:=10);
            end if;
            print a, Genus(H),pts;
            if Genus(H) eq 1
                then assert (IsLocallySoluble(H,3) eq false or IsLocallySoluble(H, 5) eq false); //There are no points on the 
                                                                                                 //genus 1 curves.
                else assert Genus(H) eq 3;
            end if;
            print "++++++++++++++++++++";
        end if;
    end if;
end for;
