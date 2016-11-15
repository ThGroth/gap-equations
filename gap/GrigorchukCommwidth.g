#
# Directory for Saved results. Needs a trailing /
#
#Change dirRep acordingly
dirRep := "~/Repositories/GrigorchukCommutatorWidth/"
#
dir := Concatenation(dirRep,"gap/90orbs/");

Read(Concatenation(dirRep,"gap/grpwords/grpwords.gd"));
Read(Concatenation(dirRep,"gap/grpwords/grpwords.gi"));



###########################################################################################
# Setup all the involved groups in L-Presented form and fix the generators
###########################################################################################
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
F := BS.wreath;

f4:= Q.1; # = ā 
f2 := Q.2; # = b
f1 := Q.3; # = c̄
f3 := f1*f2*f4*f1*f2; # = dād
A := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=(1,2));
AC := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=());

C1 := Group(a^pi,d^pi);
C2 := Group((a*d)^pi);
#This leads to problem, becaus it's the wrong isomorphism
#isoQtoGmodK := IsomorphismGroups(Q,GmodK);
#isoGmodKtoQ := IsomorphismGroups(GmodK,Q);
isoQtoGmodK :=GroupHomomorphismByImages(Q,GmodK,[f1,f2,f4],List([c,b,a],x->(x^isoGtoGLP)^piLP));
isoGmodKtoQ :=GroupHomomorphismByImages(GmodK,Q,List([c,b,a],x->(x^isoGtoGLP)^piLP),[f1,f2,f4]);

###########################################################################################
# Load the precomputed data
###########################################################################################
##Load the orbits of Q⁶/Stab(R₃) and a representative system for these orbits
orbitReps := ReadAsFunction(Concatenation(dir,"orbitReps.go"))();;
orbitTable := ReadAsFunction(Concatenation(dir,"orbitTable.go"))();;

#Load the table of good pairs.
# AGP[i] is the list of all q∈G'/K' s.t. (q,orbitReps[i]) is a good pair.
AllGoodPairsFile := Concatenation(dir,"AllGoodPairs.go");
AGP := List(ReadAsFunction(AllGoodPairsFile)(),L->List(L,i->List(GPmodKP)[i]));;

# Load the table of real good pairs (q,γ) with the property that they fullfill the
# features of Prop. 2.16 that is
# 
# L∈ RGP is L=[q,γ,[γ',x]] where 
# ̇ γ' has nontrivial activity
# ̇ forall g with g^τ=q 
# 	the sattisfiabillity of (R₂ₙ-₁ (g@2)^x ⋅ g@1 ,γ') implies the 
# 	sattisfiabillity of Rₙg,γ
# ̇ (γ',(g@2)^x ⋅ g@1) is a good pair 
RealGoodPairsFile := Concatenation(dir,"RealGoodPairs.go");
RGP := List(ReadAsFunction(RealGoodPairsFile)(),L->[List(GPmodKP)[L[1]],L[2],L[3]]);;

###########################################################################################
# Get the constraints with nontrivial activity 
###########################################################################################
ActivityGamma := function(gamma)
	return List(gamma,x->Activity(PreImagesRepresentative(pi,x)));
end;
HasNontrivialActivity := function(gamma)
	return not ForAll(ActivityGamma(gamma),IsOne);
end;
# Rₐₜ active representatives
nontrivialGammas := Filtered(orbitReps,HasNontrivialActivity);;
AGPnontrivial := AGP{Filtered([1..Size(AGP)],i->HasNontrivialActivity(orbitReps[i]))};;

###########################################################################################
# Read some functions:
###########################################################################################
#
# GammaSimplify(γ,F)
# Function to compute an element φ in the mcg wich transorm a given γ:F₂ₙ → Q to γ': F₅→Q
# and reduces this further to an element in orbitReps
# Input:
# 	γ as List or homorphism F₂ₙ → Q 
# 	F a free group on n generators where n is the length of the list
# Output:
#   γ' ∈ orbitReps such that γ and γ' are equivalent modulo Stab(F)
#-------------------------------------------------------------------------------------------
# IsGoodPair(g,γ)
# Test whether a given pair is a good pair.
# Input:
#    g ∈ G, GLP, or G/K'
#    γ ∈ Q^n for some n≥5
# Output:
#    true or false depending if (g,γ) is a good pair or not.
#-------------------------------------------------------------------------------------------
# GetAllGoodGammas(q)
# Returns list of all γ ∈ orbitReps such that (q,γ) are good pairs
# Input: 
#    q ∈ G/K'
# Output: 
# 	 L ⊂ orbitReps 
#-------------------------------------------------------------------------------------------
# FindGoodGamma(g)
# Return some active γ ∈ orbitReps such that (g,γ) is a good pair
# fails if g is not in G'
# Input: 
#    g ∈ G,GLP 
# Output:
# 	 γ ∈ orbitReps sucht that (g,γ) is a good pair
# 	   or
# 	 fail if g∉G'
#-------------------------------------------------------------------------------------------
# GetNext(g,γ)
# Returns the next good pair (g',γ') such that (Rₙg,γ) is solvable if 
# (R₂ₙ-₁ h ,γ') is solvable.
# Input: 
#    g ∈ G,GLP 
#    γ ∈ Q^n for some n≥5 with activity in some component
# Output:
# 	 [g',γ'] ∈ G,GLP × orbitReps  accordingly to the input
#------------------------------------------------------------------------------------------- 	  
# findCycle(g)
# Returns a finite list [p₁,p₂,…,pₘ] such that GetNext(pₘ[1],pₘ[2])=[p₁[1],p₁[2]] and
# GetNext(pₖ[1],pₖ[2])=[pₖ₊₁[1],p₁₊₁[2]] ∀k<m 
# This proves that g is a product of three commutators. It may be that this method does not
# terminate but I had not found any example.
# Input:
#    g ∈ G'P',GpLP 
# Output:
#    [p₁,p₂,…,pₘ] with pᵢ ∈ G' × orbitReps
Read(Concatenation(dirRep,"gap/functions.g"));
###########################################################################################
# Some tests
###########################################################################################

#Show that for all q there is a active good pair:
Assert(0,ForAll(GPmodKP,q->ForAny(GetAllGoodGammas(q),gam->HasNontrivialActivity(gam))));
#Show that for each good active pair (q,γ) there is a succecor
Assert(0,ForAll(GPmodKP,
			q->ForAll(Filtered(GetAllGoodGammas(q),HasNontrivialActivity),
				gamma->ForAny(RGP,
					P->P[1]=q and P[2]=gamma)
				)
			)
		);
#Find some random cycles
AnGpLPElement := function()
	local n,g;
	g := One(GpLP);
	for n in [1..Random([1..100])] do
		g := g*Random(GPGen);
	od;
	return g;
end;
for n in [1..200] do
	testg:= AnGpLPElement()^isoGPLtoG;
	Cy := findCycle(testg);
	Print(Size(Cy),"\n");
od;

#Find problematic elements for the R₂ case
nontrivialGammasInQ4 := Filtered(nontrivialGammas,gamma->IsOne(gamma[5]));;
ProblematicCases := Filtered(GPmodKP,q->not ForAny(nontrivialGammasInQ4,gamma->IsGoodPair(q,gamma)));;
Print("There are ",Size(ProblematicCases)," problematic cases.\n");
List(ProblematicCases,q->PreImagesRepresentative(tauLP,q));