S:=[22,23,26,28,29,30,31,33,35,39,40,41,48,50,47,46,59,71];       //These are the 18 values of N for which X_0(N) is hyperelliptic of rank 0.
assert #S eq 18;
assert #Set(S) eq 18;

for N in S do
  X:=SmallModularCurve(N);
  assert IsHyperelliptic(X);
  g:=HyperellipticPolynomials(SimplifiedModel(X));
  assert IsEven(Degree(g));
  G:=GaloisGroup(g);
  print G;
  cycles:=[CycleDecomposition(g) : g in G];
  //Want to check if all elements of the Galois group contain a 1-cycle.
  assert forall(g){c : c in cycles | exists(i){j : j in [1..#c] | #c[j] eq 1}} eq false;
  print "++++++++++++++++++++++++++++++++++++++++++++++";
end for;

