
#Load fr and equation package
if not IsExistingFile("./examples/init.g") then
    Error("Please start this script in the main directory.");
fi;
dir := Directory("examples");
Read(Filename(dir,"init.g"));

####
#
# For an equation of signature (g,l) E = ∏ᵢ₌₁ᵍ[X₂ᵢ₋₁,Xᵢ] ∏ᵢ₌₁ˡ⁻¹ gᵢ^Yᵢ gₗ 
# compute the signature of the equations nf(Φ_γ(E)) under all 
# possible activities of g₁,…,gₗ and constraints γ:⟨Xᵢ,Yⱼ|i,j⟩→S₂
#
PossibleDerivedSignaturesOriented := function(g,l)
	local FG,F,EqG,eqword,i,eq,p1,DEqG,perm,deq,neq,Signats;
	FG := FreeGroup(l,"g"); SetName(FG,"FG");
	F := FreeGroup(2*g+l-1,"X"); SetName(F,"F");
	EqG := EquationGroup(FG,F);
	eqword := [];
	for i in [1..g] do
		Add(eqword,Comm(F.(2*i-1),F.(2*i)));
	od;
	for i in [1..l-1] do
		Append(eqword,[F.(2*g+i)^-1,FG.(i),F.(2*g+i)]);
	od;
	Add(eqword,FG.(l));
	eq := Equation(EqG,eqword);
	Info(InfoExamples,2,eq,"\n");
	for p1 in Cartesian(ListWithIdenticalEntries(l-1,Group((1,2)))) do
		Add(p1,());
		Info(InfoExamples,1,"Signatures for act(g_i)=",p1,": ");
		DEqG := DecompositionEquationGroup(EqG,2,p1);
		Signats := [];
		for perm in Cartesian(ListWithIdenticalEntries(2*g+l-1,Group((1,2)))) do
			deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,eq,perm)).eq;
			neq := EquationNormalForm(EquationComponent(deq,1)).nf; 
			Add(Signats,EquationSignature(neq));
		od;
		Info(InfoExamples,1,Collected(Signats),"\n");
	od;
end;
####
#
# For an equation of signature (g,l) E = ∏ᵢ₌₁ᵍXᵢ² ∏ᵢ₌₁ˡ⁻¹ gᵢ^Yᵢ gₗ 
# compute the signature of the equations nf(Φ_γ(E)) under all 
# possible activities of g₁,…,gₗ and constraints γ:⟨Xᵢ,Yⱼ|i,j⟩→S₂
#
PossibleDerivedSignaturesUnoriented := function(g,l)
	local FG,F,EqG,eqword,i,eq,p1,DEqG,perm,deq,neq,Signats,sig;
	FG := FreeGroup(l,"g"); SetName(FG,"FG");
	F := FreeGroup(g+l-1,"X"); SetName(F,"F");
	EqG := EquationGroup(FG,F);
	eqword := [];
	for i in [1..g] do
		Add(eqword,F.(i)^2);
	od;
	for i in [1..l-1] do
		Append(eqword,[F.(g+i)^-1,FG.(i),F.(g+i)]);
	od;
	Add(eqword,FG.(l));
	eq := Equation(EqG,eqword);
	Info(InfoExamples,2,eq,"\n");
	Signats := [];
	for p1 in Cartesian(ListWithIdenticalEntries(l-1,Group((1,2)))) do
		Add(p1,());
		Info(InfoExamples,1,"Signatures for act(g_i)=",p1,":\n");
		DEqG := DecompositionEquationGroup(EqG,2,p1);
		for perm in Cartesian(ListWithIdenticalEntries(g+l-1,Group((1,2)))) do
			deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,eq,perm)).eq;
			neq := EquationNormalForm(EquationComponent(deq,1)).nf; 
			Add(Signats,[IsOrientedEquation(neq),EquationSignature(neq)]);
		od;
		for sig in Collected(Signats) do
			if sig[1][1] then
				Info(InfoExamples,1,"O:",sig[1][2],", ",sig[2],"\n");
			else
				Info(InfoExamples,1,"U:",sig[1][2],", ",sig[2],"\n");
			fi;
		od;
	od;
end;