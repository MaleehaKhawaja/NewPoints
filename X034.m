load 'timo_models_and_maps.m';
load 'rank_0_auxiliary.m';

print "We compute a model for X0(34) using the code given in the paper by
//Adzaga, Keller, Michaud-Jacobs, Najman, Ozman, and Vukorepa";
//source: https://github.com/TimoKellerMath/QuadraticPoints

time X34, ws, pairs, NB, cusp := eqs_quos(34,[]);

time j, num_denom := jmap(X34, 34);

//We need the cusps of X34 to compute the torsion subgroup of J34(Q)

cusps := compute_cusps(X34, 34, ws, cusp, num_denom: use_jmap := false);

findGenerators(X34,34,cusps,cusps[1],5);

//We know J(Q)=Z/4Z x Z/12Z by Ozman and Siksek

D1:=Place(X34![-1,1,1])-Place(X34![1,-1,1]);
D2:=Place(X34![1,1,1])-Place(X34![1,-1,1]);

infdiv:=Place(X34![1,-1,1]);

for a in [0..3]
    do for b in [0..11]
        do D := 3*infdiv + a*D1 + b*D2;
        L, phi := RiemannRochSpace(D);
        dim := Dimension(L);
        assert dim le 2;
    end for;
end for;

Qu<u>:=FunctionField(Rationals());
Qux<w,x,y>:=ProjectiveSpace((Qu), 2);

X34:=Curve(Qux,w^4 + 6*w^2*x^2 + 8*w^2*y^2 - 8*x^4 - 6*x^2*y^2 - y^4);

D1:=Place(X34![-1,1,1])-Place(X34![1,-1,1]);
D2:=Place(X34![1,1,1])-Place(X34![1,-1,1]);

infdiv:=Place(X34![1,-1,1]);

for a in [0..3] do	
    for b in [-6..5] do
            D:=a*D1+b*D2+3*infdiv;
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
                    print a, b, Genus(H),pts;
                    print "++++++++++++++++++++";
                end if;
            end if;
    end for;
end for;
