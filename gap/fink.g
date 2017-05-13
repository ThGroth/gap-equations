# solve question by Fink: how many conjugacy classes does one need to generate the Grigorchuk gp?

# G' = a^g1...a^g4
# ? 8
# 26 7
# 20 6 
# 18 5
# 15 4 
# 14 3

# G' = uvw/u/v/w
# 23 8
# 20 7
# 19 6
# 16 5

level := 10;
bigradius := 16;
smallradius := 5;
recompute := false;

if recompute then
  g := PermGroup(GrigorchukGroup,level);
  dg := DerivedSubgroup(g);
  ab := NaturalHomomorphismByNormalSubgroup(g,dg);
  id := x->Position(AsList(Image(ab)),x^ab);
  rep := List([1..8],i->First(g,x->id(x)=i));
fi;

ball := Ball(g,smallradius);

B := List([1..8],i->[]);
for x in Ball(g,bigradius) do
  Add(B[id(x)],x);
od;
B := List(B,Set);;

C := List(GeneratorsOfGroup(g),s->Set(ball,g->s^g));

A0 := List(B,S->BlistList(S,[One(g)]));

for u in ball do for v in ball do for w in ball do
  p := Position(B[1],u*v*w/u/v/w);
  if p<>fail then A0[1][p] := true; fi;
od; od; od;

expand := function(A,C)
  local new_A, c, i, j, k;

  new_A := List(A,ShallowCopy);

  for i in [1..8] do
    for c in C do
      k := id(rep[i]*Representative(c));
      for j in [1..Length(A[i])] do if A[i][j] then
        UniteBlist(new_A[k],BlistList(B[k],B[i][j]*c));
      fi; od;
    od;
  od;
  return new_A;
end;

sat := function(B,C)
  local A, oldA, n, i, h;
  B := Set(B);
  A := BlistList(B,C);
  n := 1;
  while false in A do
    oldA := ShallowCopy(A);
    for i in [1..Length(B)] do if oldA[i] then
      UniteBlist(A,BlistList(B,B[i]*C));
    fi; od;
    n := n+1;
  od;
  return n;
end;

# C till 4: B till 19
# C till 5: B till 22
# C till 6: B till 24?

xsat := function(B,C,p)
  local A, n;
  A := Intersection(B,C[1]);
  for n in p do
    UniteSet(A,Intersection(ListX(A,C[n],\*),B));
  od;
  return Size(A);
end;
