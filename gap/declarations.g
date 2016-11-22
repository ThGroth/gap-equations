Read(Concatenation(dirRep,"gap/grpwords/grpwords.gd"));
Read(Concatenation(dirRep,"gap/grpwords/grpwords.gi"));

#Set up all Branchstructure, quotients etc.
#Working with L presentation
#All groups with LP in the name means that they are subgroups of the 
#L-Presented Grigorchuk group.

DeclareInfoClass("InfoCW");
SetInfoLevel(InfoCW,2);
SetInfoHandler(InfoCW,function( infoclass, level, list )
  local cl, out, fun, s;
  cl := InfoData.LastClass![1];
  if IsBound(InfoData.Output[cl]) then
    out := InfoData.Output[cl];
  else
    out := DefaultInfoOutput;
  fi;
  if out = "*Print*" then
    if IsBoundGlobal( "PrintFormattedString" ) then
      fun := function(s)
        if (IsString(s) and Length(s) > 0) or IsStringRep(s) and
          #XXX this is a temporary hack, we would need a
          # IsInstalledGlobal instead of IsBoundGlobal here
                 NARG_FUNC(ValueGlobal("PrintFormattedString")) <> -1 then
          ValueGlobal( "PrintFormattedString" )(s);
        else
          Print(s);
        fi;
      end;
    else
      fun := Print;
    fi;
    fun("#I  ");
    for s in list do
      fun(s);
    od;
    #fun("\n"); No newlines. Otherwise progress information is not printed.
  else
    AppendTo(out, "#I  ");
    for s in list do
      AppendTo(out, s);
    od;
    #AppendTo(out, "\n");
  fi;
end);
G := GrigorchukGroup;
a := G.1; b := G.2; c := G.3; d:=G.4;
isoGtoGLP := IsomorphismLpGroup(G);
isoGPLtoG := InverseGeneralMapping(isoGtoGLP);
GLP := Image(isoGtoGLP);
# G'
aL := GLP.1; bL := GLP.2; cL := GLP.3; dL:=GLP.4;
k1 := (aL*bL)^2; k2 := (aL*bL*aL*dL)^2; k3 := (bL*aL*dL*aL)^2;
GPGen := [k1,k3,k2,(aL*dL)^2];
GpLP := Subgroup(GLP,GPGen); 
Gp := Group((a*b)^2,(a*b*a*d)^2,(b*a*d*a)^2,(a*d)^2);
LGen := [k2,k3,bL,aL*bL*aL];
LLP := Subgroup(GLP,LGen);
# K
KGen := [k1,k3,k2];
KLP := Subgroup(GLP,KGen);
# K×K
KxKGen := [k2,k3,Comm(k2^-1,k1),Comm(k2,k1^-1),Comm(k2^-1,k1)^aL,Comm(k2,k1^-1)^aL];
KxKLP := Subgroup(GLP,KxKGen);
# K'
GenKPLP := [(dL*aL*cL*aL*bL*aL*cL*aL)^2*(bL*aL*cL*aL)^4,((cL*aL)^2*bL*aL*cL*aL)^2,(dL*aL*cL*aL*bL*aL*cL*aL)^2*cL*(aL*cL*aL*bL)^3*aL*cL*aL*dL,((aL*cL)^3*aL*bL)^2, (bL*aL*cL*aL)*dL*aL*cL*aL*bL*(aL*cL)^2*(aL*cL*aL*bL)^3, (aL*cL*aL*dL*aL*cL*aL*bL)^2*(aL*cL*aL*bL)^4];
AllGenKPLP := [];
for h in GenKPLP do
	Add(AllGenKPLP,h);
	Add(AllGenKPLP,h^aL);
od;
KPLP := Subgroup(GLP,AllGenKPLP);
# G/K
piLP := NaturalHomomorphismByNormalSubgroup(GLP,KLP);
GmodK := Image(piLP);;
# G/K'
tauLP := NaturalHomomorphismByNormalSubgroup(GLP,KPLP);
homGtoGmodKxK := NaturalHomomorphismByNormalSubgroup(GLP,KxKLP);;
GmodKP := Image(tauLP);;
# G'/K'
GPmodKP := Group(List(GPGen,g->g^tauLP));;
# K/K'
KmodKP := Group(List(KGen,g->g^tauLP));;
# (K×K)/K'
KxKmodKP := Group(List(KxKGen,g->g^tauLP));;
# G/(K×K)
GmodKxK := Image(homGtoGmodKxK);
# G'/(K×K)
varpiLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KmodKP);;
varpiLP := varpiLP*IsomorphismGroups(Image(varpiLP),GmodK) ;; 
varpiPrimeLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KxKmodKP);;
varpiPrimeLP := varpiPrimeLP*IsomorphismGroups(Image(varpiPrimeLP),GmodKxK);; 

# The non L-Presented pendant to the groups before
BS := BranchStructure(G);
Q := BS.group; #G/K
w := BS.epi;
pi := BS.quo;

f4:= Q.1; # = a^π
f2 := Q.2; # = b^π
f1 := Q.3; # = c^π
f3 := f1*f2*f4*f1*f2; # = (dad)^π
A := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=(1,2));
AC := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=());

#Needed for the ReduceConstraint function. 
#This is the polycylcic decomposition of G
C1 := Group(a^pi,d^pi);
C2 := Group((a*d)^pi);

#This leads to problem, becaus it's the wrong isomorphism
#isoQtoGmodK := IsomorphismGroups(Q,GmodK);
#isoGmodKtoQ := IsomorphismGroups(GmodK,Q);

isoQtoGmodK :=GroupHomomorphismByImages(Q,GmodK,[f1,f2,f4],List([c,b,a],x->(x^isoGtoGLP)^piLP));
isoGmodKtoQ :=GroupHomomorphismByImages(GmodK,Q,List([c,b,a],x->(x^isoGtoGLP)^piLP),[f1,f2,f4]);


DeclarationsLoaded := true;