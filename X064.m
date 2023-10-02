load 'models_and_maps.m';
load 'rank_0_auxiliary.m';

print "We compute a model for X0(64) using the code given in the paper by
//Adzaga, Keller, Michaud-Jacobs, Najman, Ozman, and Vukorepa";
//source: https://github.com/TimoKellerMath/QuadraticPoints

time X64, ws, pairs, NB, cusp := eqs_quos(64,[]);

time j, num_denom := jmap(X64, 64);

//We need the cusps of X64 to compute the torsion subgroup of J64(Q)

cusps := compute_cusps(X64, 64, ws, cusp, num_denom: use_jmap := false);

P1 := cusps[1];
P2 := cusps[2];
P3 := cusps[3];
P4 := cusps[4];
P5 := cusps[5];
P6 := cusps[6];
P7 := cusps[7];

findGenerators(X64,64,cusps,P2,3);
//We know J(Q)=Z/2Z x Z/4Z x Z/4Z by Ozman and Siksek

D1 := Place(X64![-1,-1,1])-Place(X64![1,-1,1]);
D2 := Place(X64![1,1,0])-Place(X64![1,-1,1]);
D3 := Place(X64![-1,1,0])-Place(X64![1,-1,1]);
infdiv := Place(X64![1,-1,1]);

for a in [0..1]
    do for b in [0..3]
        do for c in [0..3]
            do D := 3*infdiv + a*D1 + b*D2 + c*D3;
            L, phi := RiemannRochSpace(D);
            dim := Dimension(L);
            assert dim le 2; 
        end for;
    end for;
end for;

Qu<u>:=FunctionField(Rationals());
Qux<w,x,y>:=ProjectiveSpace((Qu), 2);

X64 := Curve(Qux, w^4 + 6*w^2*x^2 - 7*x^4 + 24*w^2*x*y + 8*x^3*y + 24*w^2*y^2 + 24*x^2*y^2 + 32*x*y^3 + 16*y^4);

D1 := Place(X64![-1,-1,1])-Place(X64![1,-1,1]);
D2 := Place(X64![1,1,0])-Place(X64![1,-1,1]);
D3 := Place(X64![-1,1,0])-Place(X64![1,-1,1]);
infdiv := Place(X64![1,-1,1]);

for a in [0..1] do	
    for b in [0..3] do
        for c in [0..3] do
            D:=a*D1+b*D2+c*D3+3*infdiv;
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
                        print H;
                    end if;
                    print a, b, c, Genus(H),pts;
                    print "++++++++++++++++++++";
                end if;
            end if;
        end for;
    end for;
end for;
