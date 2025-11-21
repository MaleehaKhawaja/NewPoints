Qu<u>:=FunctionField(Rationals());
Pr<x,y,z>:=ProjectiveSpace(Qu,2);

X:=Curve(Pr, x^3*z + 4*x*z^3 - y^4);
M<xx,yy>:=FunctionField(X);

p1:=Place(X![0,0,1]);
p2:=Place(X![2,2,1]);
p3:=Place(X![2,-2,1]);
p4:=Place(X![1,0,0]);

basis:=[ -p1+3*p2-3*p3+p4  , -p1+2*p2-2*p3+p4 , 2*p1-2*p2+p3-p4 ];

for a in [0,1] do
    for b,c in [-1..2] do
        D:=a*basis[1]+b*basis[2]+c*basis[3]+3*p1;
        L,phi:=RiemannRochSpace(D);
        print [a,b,c];
        print "l(D)=", Dimension(L);
        if Dimension(L) eq 2 then
            decomnum:=#Decomposition(D+Divisor(phi(-u*L.1+L.2)));
            print "number of components", decomnum;
            print phi(L.1), phi(L.2);
            if decomnum eq 1 then
                E := Decomposition(D+Divisor(phi(-u*L.1+L.2)))[1,1];
                F := ResidueClassField(E);
                f := MinimalPolynomial(F.1);
                print "F=", f;
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
                assert IsEven(Degree(g));
                print "Degree of g is", Degree(g);
                print Factorisation(g);
                G:=GaloisGroup(g);
                print G;
                print disc;
                print "The discriminant is ", g;
                cycles:=[CycleDecomposition(g) : g in G];
                //Want to check if all elements of the Galois group contain a 1-cycle.
                if forall(g){c : c in cycles | exists(i){j : j in [1..#c] | #c[j] eq 1}}
                    then print "Every element of Galois group has a 1-cycle";
                end if;
                print "++++++++++++++++++++";
            else
                    print "reducible divisor";
            end if;
        end if;
    end for;
end for;
