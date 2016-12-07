######################################################################


##################################################################
#````````````````````````````````````````````````````````````````#
#```````````````````  MEALY_FROM_STATES@  ```````````````````````#
#````````````````                            ````````````````````#
#`````````````````  Computes a mealy machine ````````````````````#
#````````````````     with Statesset L and   ````````````````````#
#````````````````        activity act        ````````````````````#
#````````````````````````````````````````````````````````````````#
##################################################################
#Computes a mealy machine with stateset L and given activity act.
BindGlobal("MEALY_FROM_STATES@", function(L,act)
		local m,tran,out,i,j;
		#Force L to contain elements and not lists of elements.
		for i in [1..Size(L)] do
			if IsList(L[i]) then
				L[i] := Product(L[i]);
			fi;
		od;
		#Force act to be a list of output symbols.
		if IsPerm(act) then
			act := List(AlphabetOfFRObject(L[1]),x->x^act);
		fi;
		
		tran := [[]];
		out := [act];
		i := 1;
		j := 2;
		for m in L do
		  Add(tran[1],i+1);
		  Append(tran,List(m!.transitions,x->List(x,y->y+i)));
		  Append(out,m!.output);
		  i := i + Length(m!.transitions);
		  j := j+1;
		od;
		return MealyElement(tran,out,1);
	end);
#################################################################################
####                                                                         ####
####	                 Free Products of Free groups                        ####
####                                                                         ####
#################################################################################

InstallMethod(FreeProductOp, "for f.g. free groups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,names,genInList,FP,last,i;
		if not ForAll(L,IsFreeGroup) then 
			TryNextMethod();
		fi;
		if not ForAll(L,IsFinitelyGeneratedGroup) then 
			TryNextMethod();
		fi;
		genInList  := List(L, H->Length(GeneratorsOfGroup(H)));
		embeddings :=[];
		names := Concatenation(List([1..Length(L)],
				i->List([1..genInList[i]],
				j->Concatenation(String(L[i].(j)),String(i)) )));
		#FP := FreeGroup(Sum(genInList));
		FP:=FreeGroup(names);
		if ForAll(L,HasName) then
			SetName(FP,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;

    	last := 0;
    	for i in [1..Length(L)] do
    		Add(embeddings,GroupHomomorphismByImages(
    				L[i],
    				FP,
    				GeneratorsOfGroup(FP){[last+1..last+genInList[i]]}));
    		last := last+genInList[i];
    	od;
        SetFreeProductInfo( FP, 
        rec( groups := L,
             embeddings := embeddings ) );
    	return FP;   
	end);

InstallMethod(FreeProductOp, "for infinitely generated free groups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,FP,i,names;
		if not ForAll(L,IsFreeGroup) then 
			TryNextMethod();
		fi;
		if ForAny(L,IsFinitelyGeneratedGroup) then 
			TryNextMethod();
		fi;
		embeddings :=[];
		#Take the init part of each list of names
		names := Concatenation(List([1..Length(L)],
				i->List(FamilyObj(Representative(L[i]))!.names![2],
				j->Concatenation(j,String(i)) )));	
		FP := FreeGroup(infinity,"yn",names);
		if ForAll(L,HasName) then
			SetName(FP,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;
    	for i in [1..Length(L)] do
    		Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				FP,
    				w-> AssocWordByLetterRep(FamilyObj(Representative(FP)),
    					List(LetterRepAssocWord(w),k->(Length(L)-1)*k+i))));
    	od;
        SetFreeProductInfo( FP, 
        rec( groups := L,
             embeddings := embeddings ) );
    	return FP;   
	end);

#################################################################################
####                                                                         ####
####	                          EquationGroup                              ####
####                                                                         ####
#################################################################################

EQUATION_GROUP_FAMILIES := [];
InstallMethod(EquationGroup, "for two groups",
	[IsGroup,IsFreeGroup],
	function(G,Free)
		local Ob;
		Ob := First(EQUATION_GROUP_FAMILIES,f->f[1]=G and f[2]=Free);
		if Ob = fail then
			Ob := Objectify(NewType(
					CollectionsFamily(NewFamily("Equation Group(..)")), IsEquationGroup),
    				rec(group := G,
       					free := Free));
			Add(EQUATION_GROUP_FAMILIES,[G,Free,Ob]);
			SetIsWholeFamily(Ob,true);
		else
			Ob := Ob[3];
		fi;
		SetKnowsHowToDecompose(Ob,false);
		return Ob;
	end);

InstallMethod(GeneratorsOfGroup, "for an EquationGroup",
	[IsEquationGroup],
	function(G)
		return [GeneratorsOfGroup(G!.free),GeneratorsOfGroup(G!.group)];
	end);
InstallMethod( PrintObj,   "for EquationGroups)",
   [ IsEquationGroup],
    function( G )
		local s;
		Print("EqGroup(",G!.free,"*",G!.group,")");
	   end 
);
InstallMethod( ViewObj,   "for EquationGroups)",
   [ IsEquationGroup],
    function( G )
		local s;
		View("EqGroup(",G!.free,"*",G!.group,")");
	   end 
);
InstallMethod( \in,   "for Equation in EquationGroup)",
   [IsEquation, IsEquationGroup],
    function( eq, G )
    	Print("blub");
		return eq!.eqG = G;
	   end 
);
InstallMethod( \=,  "for two EquationGroups",
    [ IsEquationGroup, IsEquationGroup],
    function( x, y )
			return x!.free=y!.free and y!.group=x!.group; 
		end 
);

InstallMethod(DecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	function(eqG)
		local DG,alph,DEqG;
		if not IsFRGroup(eqG!.group) then
			TryNextMethod();
		fi; 
		if not IsFinitelyGeneratedGroup(eqG!.group) then
			TryNextMethod();
		fi; 
		alph := AlphabetOfFRSemigroup(eqG!.group);
		if IsStateClosed(eqG!.group) then
			DG := eqG!.group;
		else
			DG := Group(List(alph,a->Concatenation(
					List(GeneratorsOfGroup(eqG!.group),gen->State(gen,a))) ));
		fi;
		DEqG := EquationGroup(DG,FreeProduct(ListWithIdenticalEntries(Size(alph),eqG!.free)));
		SetIsDecompositionEquationGroup(DEqG,true);
		return DEqG;
	end);
InstallMethod(IsDecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	EqG->HasFreeProductInfo(EqG!.free));
#################################################################################
####                                                                         ####
####	                          Equations                                  ####
####                                                                         ####
#################################################################################
InstallMethod(Equation, "(Equation) for a list of group elements and unknowns and boolean",
	[IsList,IsEquationGroup,IsBool],
	function(elms,eqG,reduced)
		local Ob;
		if not ForAll(elms,e->e in eqG!.free or e in eqG!.group) then
			Error("All group elements must be either a variable or a group constant.");
		fi;
		Ob := Objectify(NewType(ElementsFamily(FamilyObj(eqG)), IsEquation and IsEquationRep),
    		rec(word := elms,
       			group := eqG!.group,
       			free := eqG!.free,
       			eqG := eqG));
		if reduced then
			return EquationReducedForm(Ob);
		fi;
		return Ob;
	end);

InstallOtherMethod(Equation, "(Equation) for a list of group elements and unknowns",
	[IsList,IsEquationGroup],
	function(elms,eqG)
		return Equation(elms,eqG,true);
	end);


InstallOtherMethod(Equation, "(Equation) for a list of group elements and unknowns",
	[IsList,IsGroup,IsFreeGroup],
	function(elms,G,Free)
		return Equation(elms,EquationGroup(G,Free));
	end);

InstallMethod(EquationVariables, "for a Equation",
	[IsEquation and IsEquationRep],
	function(x)
		return List(Set(List(Concatenation(
			List(Filtered(x!.word,e->e in x!.free),	fw -> LetterRepAssocWord(fw))
			),i->AbsInt(i))),
			v->AssocWordByLetterRep(FamilyObj(One(x!.free)),[v]));
	end
);

InstallMethod( PrintObj,   "for Equations)",
   [ IsEquation and IsEquationRep ],
    function( x )
		local s;
		Print("Equation in ",EquationVariables(x));
	   end 
);

InstallMethod(EquationReducedForm, "for an Equation in Equation representation",
	[IsEquation and IsEquationRep],
	function(x)
		local last,lastfree,newword,e,Eq;
		last := One(x!.group);
		lastfree := One(x!.free);
		newword := [];
		for e in x!.word do
			if e in x!.free then
				if not IsOne(last) then
					Add(newword,last);
					last := One(x!.group);
				fi;
				# Add all letters of e in case e is not only a generator
				lastfree := lastfree * e;
			else # e ∈ G
				if not IsOne(lastfree) then
					Add(newword,lastfree);
					lastfree := One(x!.free);
				fi;
				last := last*e;
			fi;
		od;
		if not IsOne(lastfree) then
			Add(newword,lastfree);
		fi;
		#Cyclic reduction: No group constant in the first position
		if newword[1] in x!.group then
			last := last*newword[1];
			newword := newword{[2..Size(newword)]};
		fi;
		if not IsOne(last) then
			Add(newword,last);
		fi;
		Eq :=Equation(newword,x!.eqG,false);
		SetIsReducedEquation(Eq,true);
		return 	Eq;
	end);
InstallMethod( \=,  "for two Equations",
		IsIdenticalObj,
    [ IsEquation and IsEquationRep, IsEquation and IsEquationRep ],
    function( x, y )
			x := EquationReducedForm(x);
			y := EquationReducedForm(y);
			return x!.word = y!.word; 
		end 
);

InstallMethod(OneOp, "for an Equation",
	[IsEquation and IsEquationRep],
	x -> Equation([],x!.group,x!.free) 
);
InstallOtherMethod( One,"for an EquationGroup",
    [ IsEquationGroup ],
    eqG -> Equation([],eqG) 
);
InstallOtherMethod(\[\], "for an Equation",
	[IsEquation and IsEquationRep,IsInt],
	function(w,i) 
		return Equation([w!.word[i]],w!.group,w!.free);
	end);

InstallOtherMethod(\[\], "for an Equation",
	[IsEquation and IsEquationRep,IsList],
	function(w,i) 
		return Equation(w!.word{i},w!.group,w!.free);
	end);

InstallMethod( \*,   "for two Equations",
    [ IsEquation and IsEquationRep, IsEquation and IsEquationRep ],
    function( x, y )
    	if x!.group = y!.group and x!.free = y!.free then
    		return Equation(Concatenation(x!.word,y!.word),x!.group,x!.free);
    	fi;
    	Error("Groups must be compatible");
    end 
);

InstallMethod(EquationLetterRep, "for an Equation",
	[IsEquation],
	function(eq)
		local nw,elm,i,Eq;
		nw := [];
		for elm in eq!.word do
			if elm in eq!.group then
				Add(nw,elm); 
			else
				for i in LetterRepAssocWord(elm) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm),[i]));
				od;
			fi;
		od;
		Eq:= Equation(nw,eq!.eqG,false);
		SetIsEquationLetterRep(Eq,true);
		return Eq;
	end);

InstallMethod(InverseOp, "for a Equation",
	[IsEquation and IsEquationRep],
	function(x)
		return Equation(Reversed(List(x!.word,InverseOp)),x!.group,x!.free);
	end
);

InstallMethod(IsQuadraticEquation, "for a Equation",
		[IsEquation],
		function(x)
			local i,Val;
			Val := rec();
			for i in Concatenation(List(
					Filtered(x!.word,e->e in x!.free),
					fw -> LetterRepAssocWord(fw)
					)) do
				i := AbsInt(i);
				if IsBound(Val.(i)) then
					if Val.(i) > 1 then
						return false;
					fi;
					Val.(i) := 2;	
				else
					Val.(i) := 1;
				fi;
			od;
			return true;
		end
);

InstallMethod(IsOrientedEquation, "for a square Equation",
		[IsQuadraticEquation],
		function(x)
			local LetterRep;
			LetterRep := Concatenation(List(
						Filtered(x!.word,e->e in x!.free),
						fw -> LetterRepAssocWord(fw)
						));
			return ForAll(LetterRep,i->-i in LetterRep);
		end
);

InstallMethod(DecompositionEquation, "for an Equation a group homomorphism and an DecompositionEquationGroup",
		[IsEquation,IsGroupHomomorphism,IsDecompositionEquationGroup],
		function(eq,acts,DEqG)
			local alph,vars,DecompEq,lastperm,x,i;
			if not IsFRGroup(eq!.group) then
				TryNextMethod();
			fi;
			alph := AlphabetOfFRSemigroup(eq!.group);
			if not ForAll([1..Size(alph)],i->Source(Embedding(DEqG!.free,i))=eq!.free) then
				Error("DecompositionEquationGroup doesn't correspond to EquationGroup.");
			fi;
			vars := EquationVariables(eq);
			if not Group(vars)=Source(acts) then
				Error("acts needs to be defined on the variables.");
			fi;
			if not IsPermGroup(Range(acts)) then
				TryNextMethod();
			fi;
			eq := EquationLetterRep(eq);
			DecompEq := ListWithIdenticalEntries(Size(alph),[]);
			lastperm := ();
			for x in eq!.word do
				if x in eq!.group then
					for i in [1..Size(alph)] do
						Add(DecompEq[i^lastperm],State(x,alph[i]));
					od;
					lastperm := lastperm*Activity(x);
				else
					for i in [1..Size(alph)] do
						if LetterRepAssocWord(x)[1]<0 then
							#eq is in LetterRep so this is the inverse of a gen.
							lastperm := lastperm*x^acts;
							Add(DecompEq[i^lastperm],x^Embedding(DEqG!.free,i));
						else
							Add(DecompEq[i^lastperm],x^Embedding(DEqG!.free,i));
							lastperm := lastperm*x^acts;
						fi;
					od;
				fi;
			od;
			return [List(DecompEq,L->Equation(L,DEqG)),lastperm];
			#return List(DecompEq,L->Equation(L,DEqG))

		end);
#################################################################################
####                                                                         ####
####	                     EquationsHomomorphism                           ####
####                                                                         ####
#################################################################################

InstallMethod(EquationHomomorphism ,"For an an EquationGroup and two group Homomorphisms",
	[IsEquationGroup, IsGroupHomomorphism, IsGroupHomomorphism],
	function(SourceEqG,mapFree,mapGroup)
		local fam,RangeEqG;
		if not IsFreeGroup(Source(mapFree)) then
			Error("1. Argument need to be a homomorphism from a free group");
		fi;
		
		if IsFreeGroup(Range(mapFree)) then
			RangeEqG := EquationGroup(Range(mapGroup),Range(mapFree));
		else
			RangeEqG := Range(mapGroup);
		fi;
		fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(SourceEqG)),
									 ElementsFamily(FamilyObj(RangeEqG)) );
		return Objectify(NewType(fam,IsEquationHomomorphism),
							rec(	mapFree := mapFree, 
									mapGroup := mapGroup,
									SourceEqG := SourceEqG,
									Range := RangeEqG));
	end);

InstallMethod(Source ,"For an EquationHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		return hom!.SourceEqG;
	end);

InstallMethod(Range ,"For an EquationHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		return hom!.Range;
	end);


InstallMethod(ImageElm ,"For an EquationHomomorphism and an Equation",
	[IsEquationHomomorphism,IsEquation],
	function(hom,eq)
		local res;
		res := List(eq!.word,function(elm)	
								if elm in eq!.group then
									return elm^hom!.mapGroup;
								fi;
								return elm^hom!.mapFree; end);
		if IsEquationGroup(Range(hom)) then
			return Equation(res,Range(hom));
		else 
			return Product(res);
		fi;
	end);

InstallMethod(ViewObj, "For an EquationsHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		View(Source(hom),"->",Range(hom));
	end);

InstallMethod(IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsEquationHomomorphism, IsEquation],
	function(hom,eq)
		if IsOne(hom!.mapGroup) then
			return IsOne(eq^hom); 
		fi;
	end);

InstallMethod(EquationEvaluation, "For an Equation and a list of images",
	[IsEquation, IsList],
	function(eq,L)
		local var;
		if not ForAll(L,elm->elm in eq!.group) then
			Error("All images need to be in the group of constants.");
		fi;
		var := EquationVariables(eq);
		if not Length(var)=Length(L) then
			Error("There must be as many images as variables.");
		fi;
		return EquationHomomorphism(eq!.eqG,
					GroupHomomorphismByImages(Group(var),eq!.group,L),
					IdentityMapping(eq!.group));
	end);

#Example
G := GrigorchukGroup;
BS := BranchStructure(G);
pi := BS.quo;
AssignGeneratorVariables(G);
F := FreeGroup(infinity,"x");
SetName(F,"F_X");
EqG := EquationGroup(G,F);
Eq := Equation([Comm(F.1,F.2),(a*b)^2],EqG);
id := IdentityMapping(G);

h := GroupHomomorphismByImages(Group(EquationVariables(Eq)),F,[F.2,F.5]);
eqhom2 := EquationHomomorphism(EqG,h,id);
ev := EquationEvaluation(Eq,[a,b*a]);

Image(ev,Eq);
Eq^eqhom2;

eqhom2*ev;

DEqG := DecompositionEquationGroup(EqG);
constr := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),[(),()]);
DEq:=DecompositionEquation(Eq,constr,DEqG);
#
#
#
#TODO Continue here.



InstallMethod(EquationDecomposable, "for a groupWord",
	[IsEquation],
	function(w)
	local M,i,d,G,Hom,Hom_inv;
		G := w!.group;
		if not IsFRGroup(G) then
			TryNextMethod();
		fi;
		d := Length(AlphabetOfFRSemigroup(G));
		Hom := [];
		Hom_inv := [];
		for i in UnknownsOfEquation(w) do
			Hom_inv[(d+1)*AbsInt(i)] := Equation([AbsInt(i)],G);
			Hom[AbsInt(i)] := Equation([(d+1)*AbsInt(i)],G);
		od;
		Hom := EquationHom(Hom,G);
		Hom_inv := EquationHom(Hom_inv,G);
		M := Objectify(NewType(FamilyObj(G), IsEquation and IsEquationDecomposableRep),
					rec(word := ImageOfEquationHom(Hom,w)!.word,
							group := w!.group,
							hom := Hom));
    return M;
	end
);

#->

InstallMethod(FREquation, "For a list of grpwords, a permutation and an FRGroup",
	[IsList,IsPerm,IsGroup],
	function(L,p,G)
		local M;
		M := Objectify(NewType(FamilyObj(G), IsFREquation and IsFREquationStateRep),
					rec(states := L,
							group := G,
							activity := p));
    return M;	
	end
);

InstallMethod(FREquationUnknown, "For an integer, a permutation and an FRGroup",
	[IsInt, IsPerm, IsFRGroup],
	function(i,p,G)
		local d,L,M;
		d := Length(AlphabetOfFRSemigroup(G));
		if i mod (d+1) <> 0 then
			Error("The first Argument must be a valid decomposable variable");
		fi;
		if i>0 then
			L :=List([i+1..i+d],x->Equation([x],G));
			return FREquation(L,p,G);
		else
			L := List([-i+1..-i+d],x->Equation([-x],G)); 
			return FREquation(Permuted(L,p^-1),p^-1,G);
		fi;
	end
);






Namecount := 0;
ToString := function(L)
	local S,l;
	S:="[";
	if Length(L)=0 then
		return "[]";
	fi;
	for l in L do
		if Length(String(l))<5 then
			S:=Concatenation(S,String(l),",");
		elif HasName(l) then
			S:=Concatenation(S,Name(l),",");
		else
			SetName(l,Concatenation("c_",String(Namecount)));
			Namecount := Namecount +1;
			S:=Concatenation(S,Name(l),",");
		fi;
	od;
	return Concatenation(S{[1..Length(S)-1]},"]");
end;
InstallMethod( \=,  "for two EquationHoms",
		IsIdenticalObj,
    [ IsEquationHom and IsEquationHomRep, IsEquationHom and IsEquationHomRep ],
    function( x, y )
			return x!.rules = y!.rules;
		end 
);
	


InstallMethod( PrintObj,   "for EquationHoms)",
	[ IsEquationHom and IsEquationHomRep ],
	function( x )
		local w;
		w := x!.rules;
		if Number(w)=0 then			
			Print("Trivial Group word Homomorphism");
		else
			Print("Group word Homomorphism on ",String(Number(w))," generators");
		fi;
  end 
);
InstallMethod( PrintObj,   "for FREquations)",
	[ IsFREquation and IsFREquationStateRep ],
	function( x )
		local i,j, res,first;
		first := true;
		Print("<");
		for i in x!.states do
			if not first then
				Print(",");
			else
				first := false;
			fi;
			for j in i!.word do
				if IsInt(j) then
					Print(j);
				elif HasName(j) then
					Print(Name(j));
				else
					Print("gc");
				fi;
			od;
		od;
		Print(">",x!.activity);
  end 
);



InstallMethod( \*,   "for two EquationHoms",
		IsIdenticalObj,
    [ IsEquationHom and IsEquationHomRep, IsEquationHom and IsEquationHomRep ],
    function( x, y )
			local res,i;
			res:= [];
			for i in [1..Maximum(Length(x!.rules),Length(y!.rules))] do
				if IsBound(y!.rules[i]) then
					res[i] := ImageOfEquationHom(x,y!.rules[i]);
				elif IsBound(x!.rules[i]) then
					res[i] := x!.rules[i];
				fi;
			od;
			return EquationHom(res,FamilyObj(x));
    end 
);
InstallMethod( \*,   "for two FREquations",
	 [ IsFREquation and IsFREquationStateRep, IsFREquation and IsFREquationStateRep ],
    function( x, y )
   		local L,i;
			L := [];
			for i in [1..Length(x!.states)] do
				Add(L,x!.states[i]*y!.states[i^(x!.activity)]);
			od;
			return FREquation(L,x!.activity * y!.activity,y!.group);
    end 
);
InstallMethod( \*,   "for an FRElement and a FREquation",
	 [ IsFRElement, IsFREquation and IsFREquationStateRep ],
    function( x, y )
   		local L,i;
			L := DecompositionOfFRElement(x);
			for i in [1..Length(L[1])] do
				L[1][i] := Equation([L[1][i]],y!.group)*y!.states[L[2][i]];
			od;
			return FREquation(L[1],Activity(x) * y!.activity,y!.group);
    end 
);
InstallMethod( \*,   "for an FREquation and an FRElement",
	 [IsFREquation and IsFREquationStateRep, IsFRElement ],
    function( x, y )
   		local L,S,i;
			L := DecompositionOfFRElement(y);
			S := [];
			for i in [1..Length(x!.states)] do
				Add(S, x!.states[i] * Equation([L[1][i^x!.activity]],x!.group));
			od;
			return FREquation(S,x!.activity*Activity(y),x!.group);
    end 
);

InstallMethod(IsOrientedEquation, "for a square Equation",
	[IsSquareEquation],
	function(w)
		local i,Val;
		w := UnknownsOfEquation(w);
		if Length(w) = 0 then
			return true;
		fi;
		Val := ListWithIdenticalEntries( Maximum(-1*Minimum(w),Maximum(w)), 0 );
		for i in w do
			Val[AbsInt(i)] := Val[AbsInt(i)] + i;
		od;
		return ForAll(Val,x->x=0);
	end
);


InstallMethod(EquationAsElement, "for a Equation",
	[IsEquation and IsEquationRep],
	function(w)
		w := EquationReducedForm(w);
		if Length(w!.word) = 0 then
			return One(w!.group);
		elif Length(w!.word) = 1 and not IsInt(w!.word[1]) then
			return w!.word[1];
		else
			Error("This GroupWord still contains Unknowns");
		fi;
	end
);


InstallMethod(ImageOfEquationHom, "for a EquationHom and a Equation",
	[IsEquationHom,IsEquation and IsEquationRep],
	function(H,e)
		local res,x,h;
		res:=[];
		H := H!.rules;
		for x in e!.word do
			if IsPosInt(x) and IsBound(H[x]) then
				Append(res,H[x]!.word);
			elif IsInt(x) and IsPosInt(-x) and IsBound(H[-x]) then
				h := H[-x]^-1;
				Append(res,h!.word);
			else
				Add(res,x);
			fi;
		od;
		#return Equation(res,e!.group);
		return EquationReducedForm(Equation(res,e!.group));
	end
);	
InstallMethod(OneOp, "for a EquationHom",
	[IsEquationHom],
	x -> EquationHom([],x!.group) 
);
InstallMethod(UnknownsOfEquation, "for a Equation",
	[IsEquation and IsEquationRep],
	w -> Filtered(w!.word,IsInt)
);
InstallMethod(LengthOfEquation, "for a Equation",
	[IsEquation and IsEquationRep],
	w -> Length(w!.word)
);
InstallMethod(IsPermEquation,"for a Equation",
	[IsEquation and IsEquationRep],
	x->IsPermGroup(x!.group));
InstallMethod(IsSquareEquation, "for a Equation",
		[IsEquation],
		function(w)
			local i,Val;
			Val := rec();
			for i in UnknownsOfEquation(w) do
				i := AbsInt(i);
				if IsBound(Val.(i)) then
					if Val.(i) > 1 then
						return false;
					fi;
					Val.(i) := 2;	
				else
					Val.(i) := 1;
				fi;
			od;
			return true;
		end
);



InstallMethod(EquationReducedForm, "for a Grpword in FREquation representation",
	[IsEquation and IsFREquationStateRep],
	function(x)
		local s,L;
		L := [];
		for s in x!.states do	
			Add(L,EquationReducedForm(s));
		od;
		return FREquation(L,x!.activity,Representative(x!.states)!.group);		
	end
);
InstallMethod(EquationCyclReducedForm, "for a Grpword",
	[IsEquation],
	function(x)
		local L;
		x := EquationReducedForm(x);
		L := x!.word;
		#Check if word begins with constant
		if Length(L) > 1 and not IsInt(L[1]) then
			if IsInt(L[Length(L)]) then
				Add(L,L[0]);
			else
				L[Length(L)] := L[Length(L)]*L[1];
				if IsOne(L[Length(L)]) then #kill last entry
					L := L{[1..Length(L)-1]};
				fi;
			fi;#kill first entry
			L:= L{[2..Length(L)]};
		else
			return x;
		fi;
		x := Equation(L,x!.group);
		IsSquareEquation(x);
		IsOrientedEquation(x);
		return x;		
	end
);
InstallMethod(EquationNormalForm, "for a Grpword",
	[IsEquation],
	function(x)
		local NormalUnknowns,NormalForm2,N2,N;
		NormalForm2:= function(xx)
			local case10,case11a,case11b,case3,toInvert,vfind,i,j,t,x,vlen,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3,first,Hom,Hom2,y,N;
			Info(InfoFRGW,3,"Call of NormalForm2¸with",xx!.word);
			xx:= EquationReducedForm(xx);
			w:= xx!.word;
			#Functions for Oriented Equations:
			# w = w1·x⁻·v·x·w2
			case10 := function(w1,v,w2,x,G)
				local N,Hom,h,c;
				#Print("Case 10:");
				#View([w1,v,w2,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w1,w2),G));
				h := N[1]!.word;
				Hom := [];
				Hom[x] := Equation([x],G)*Equation(w2,G)^-1;
				if Length(h)=0 then
					return [Equation([-x,v,x],G),EquationHom(Hom)];
				fi;
				#Does N end with a constant?
				if IsInt(h[Length(h)]) then
					return [N[1]*Equation([-x,v,x],G),N[2]*EquationHom(Hom)];
				else
					c:= h[Length(h)];
					Hom := [];
					Hom[x] := Equation([x,c],G)*Equation(w2,G)^-1;
					return [N[1][[1..Length(h)-1]]*Equation([-x,v,x,c],G),N[2]*EquationHom(Hom)];
				fi;
			end;
			# w = w11·v⁻·w12·x⁻·v·x·w2
			case11a := function(w11,w12,v,w2,x,G)
				local N,Hom,h;
				#Print("Case 11a:");
				#View([w11,w12,v,w2,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w11,w12,w2),G));
				Hom := [];
				h := Equation(w11,G);
				Hom[x] := h^-1*Equation(Concatenation([x],w11,w12),G);
				Hom[v] := h^-1*Equation(Concatenation([v],w11),G);
				return [Equation([-v,-x,v,x],G)*N[1],N[2]*EquationHom(Hom)];
			end;
			# w = w1·x⁻·v·x·w21·v⁻·w22
			case11b := function(w1,v,w21,w22,x,G)
				local N,Hom,h;
				#Print("Case 11b:");
				#View([w1,v,w21,w22,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w1,w21,w22),G));
				Hom := [];
				Hom[x] := Equation(Concatenation(w1,w21),G)^-1 *Equation(Concatenation([x],w1),G);
				Hom[v] := Equation(Concatenation(w1,w21),G)^-1 *Equation(Concatenation([-v],w1,w21),G);
				return [Equation([-x,-v,x,v],G)*N[1],N[2]*EquationHom(Hom)];
			end;
			# w = x²·w2
			case3 := function(x,w2,G)
				local N,N2,Hom,y,z;
				#Print("Case 3:");
				#View([x,w2]);
				#Print("\n");
				N := NormalForm2(Equation(w2,G));
				#Check if N start with [y,z]
				if Length(N[1]!.word)<4 or not IsInt(N[1]!.word[2]) or N[1]!.word[1]=N[1]!.word[2] then
					#Print("End is Ok.. leaving Case 3\n");
					return [Equation([x,x],G)*N[1],N[2]];
				else
					#Print("w2 contains commutator...\n");
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := [];
					Hom[x] := Equation([x,y,z],G);
					Hom[y] := Equation([-z,-y,-x,y,z,x,y,z],G);
					Hom[z] := Equation([-z,-y,-x,z],G);
					N2 := case3(z,N[1]!.word{[5..Length(N[1]!.word)]},G);
					return [Equation([x,x,y,y],G)*N2[1],EquationHom(Hom)*N2[2]*N[2]];
				fi;
			end;
			if IsOrientedEquation(xx) then
				if Length(w)<3 then
					return [xx,EquationHom([],xx!.group)];
				fi;
				#Print("Oriented");
				#Find x s.t. w=w1 -x v x w2 with |v| minimal
				t:= rec();
				for i in w do
					if IsInt(i) then
						i:= AbsInt(i);
						if IsBound(t.(i)) then
							t.(i) := -t.(i);
						else
							t.(i) := 0;
						fi;
					fi;
					for j in Set(RecNames(t)) do
						if t.(j)>=0 then
							t.(j) := t.(j) +1;
						fi;
					od;
				od;
				#counting done
				#Print("Counting dict: ",t,"\n");
				x := 0;
				vlen := -Length(w);
			for i in Set(RecNames(t)) do
				if t.(i)>vlen then
					x := i;
					vlen := t.(i);
				fi;
			od;
			x := Int(x);
			#Minimal i found;
			first := true;
			toInvert := false;
			for i in [1..Length(w)] do
				if IsInt(w[i]) and AbsInt(w[i]) = x then
					if first then
						if w[i]>0 then
							toInvert := true;
						fi;
						w1 := w{[1..i-1]};
						first := false;
						j:= i+1;
					else 
						v:= w{[j..i-1]};
						if i<Length(w) then
							w2 := w{[i+1..Length(w)]};
						else
							w2 := [];
						fi;
						break;
					fi;
				fi;
			od;
			Hom := [];
			if toInvert then
				Hom[x] := Equation([-x],xx!.group);
			fi;
			Hom := EquationHom(Hom,xx!.group);
			#Decomposition done
			if Length(v)=1 then #Case 1
				v := v[1];
				if IsInt(v) then #Case 1.1
					if v<0 then
						Hom2 := [];
						Hom2[-v] := Equation([v],xx!.group);
						Hom := EquationHom(Hom2)*Hom;
					fi;
					i := Position(w1,-v);
					if not i = fail then #Case 1.1.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						N := case11a(w11,w12,AbsInt(v),w2,x,xx!.group);
						#Display(N[2]!.rules[1]!.word);
						return [N[1],N[2]*Hom];
					else #Case 1.1.b
						i := Position(w2,-v);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N:= case11b(w1,AbsInt(v),w21,w22,x,xx!.group);
						return [N[1],N[2]*Hom];
					fi;
				else #Case 1.0
					N := case10(w1,v,w2,x,xx!.group);
					return [N[1],N[2]*Hom];
				fi;
			else #Case 2
				#Print("Case2.");
				y := 0;
				for i in v do
					if IsInt(i) then
						y := i;
						if i<0 then
							break;
						fi;
					fi;
				od;
				i := Position(v,y);
				if y>0 then
					Hom2 := [];
					Hom2[y] := Equation([-y],xx!.group);
					Hom := EquationHom(Hom2)*Hom;
					#y := -y;
				fi;
				y := -y;
				v1 := v{[1..i-1]};
				v2 := v{[i+1..Length(v)]};
				i := Position(w1,y);
				if not i = fail then #Case 2.a
					#Print("a. ");
					w11 := w1{[1..i-1]};
					w12 := w1{[i+1..Length(w1)]};
					N := case11a(w11,Concatenation(v2,v1),x,Concatenation(w12,w2),AbsInt(y),xx!.group);
					Hom2 := [];
					Hom2[x] :=Equation(v2,xx!.group)^-1*Equation(Concatenation([x,AbsInt(y)],w12),xx!.group);
					return [N[1],N[2]*EquationHom(Hom2)*Hom];
				else #Case 2.b
					#Print("b. ");
					i := Position(w2,y);
					if i = fail then 
						Error("Strange Error");
					fi;
					w21 := w2{[1..i-1]};
					w22 := w2{[i+1..Length(w2)]};
					N := case11a(Concatenation(w1,w21),Concatenation(v2,v1),x,w22,AbsInt(y),xx!.group);
					Hom2 := [];
					Hom2[x] := Equation(v2,xx!.group)^-1*Equation([x],xx!.group)*Equation(w21,xx!.group)^-1;
					return [N[1],N[2]*EquationHom(Hom2)*Hom];
				fi;
			fi; #End Case 2
			else #so not oriented
				#Print("Nonoriented Case:\n");
				#find x s.t. w = w1·x·w2·x·w3
				t:= rec();
				for i in [1..Length(w)] do
					if IsInt(w[i]) then
						if IsBound(t.(w[i])) then
							x:= w[i];
							w1:= w{[1..t.(w[i])-1]};
							w2:= w{[t.(w[i])+1..i-1]};
							w3:= w{[i+1..Length(w)]};
							break;
						else        
							t.(w[i]) := i;
						fi;
					fi;
				od;
				Hom := [];
				if x<0 then
					Hom[-x] := Equation([x],xx!.group);
					x := -x;
				fi;
				Hom := EquationHom(Hom,xx!.group);
				Hom2 := [];
				v := Equation(w2,xx!.group)^-1;
				Hom2[x] := Equation(w1,xx!.group)^-1 * Equation(Concatenation([x],w1),G) *v;
				Hom := EquationHom(Hom2)*Hom;
				w2 := v!.word;
				N := case3(x,Concatenation(w1,w2,w3),xx!.group);
				return [N[1],N[2]*Hom];
			fi; #End Nonoriented Case	
			Print("Not implemented yet\n");
			return [];
		end;
		NormalUnknowns := function(N)
			local w,i,L,Hom,cur;
			Hom := [];
			cur := 0;
			L := [];
			w := [];
			for i in N!.word do
				if IsInt(i) then
					if IsBound(L[AbsInt(i)]) then
						Add(w,SignInt(i)*L[AbsInt(i)]);
					else
						cur := cur +1;
						L[AbsInt(i)] := cur;
						Hom[AbsInt(i)] := Equation([cur],N!.group);
						Add(w,SignInt(i)*cur);
					fi;
				else
					Add(w,i);
				fi;
			od;
			return [Equation(w,N!.group),EquationHom(Hom,N!.group)];
		end;
		if IsSquareEquation(x) then
			N := NormalForm2(x);
			N2 :=NormalUnknowns(N[1]);
			return [N2[1],N2[2]*N[2]];
		else
			TryNextMethod();
		fi;
	end
);
InstallMethod(EquationNormalFormInverseHom, "for a Grpword",
	[IsEquation],
	function(x)
		local NormalUnknowns,NormalForm2,N2,N;
		NormalForm2:= function(xx)
			local case10,case11a,case11b,case3,toInvert,vfind,i,j,t,x,vlen,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3,first,Hom,Hom2,y,N;
			Info(InfoFRGW,3,"Call of NormalForm2¸with",xx!.word);
			xx:= EquationReducedForm(xx);
			w:= xx!.word;
			#Functions for Oriented Equations:
			# w = w1·x⁻·v·x·w2
			case10 := function(w1,v,w2,x,G)
				local N,Hom,h,c;
				#Print("Case 10:");
				#View([w1,v,w2,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w1,w2),G));
				h := N[1]!.word;
				Hom := [];
				Hom[x] := Equation(Concatenation([x],w2),G); #DONE
				if Length(h)=0 then
					return [Equation([-x,v,x],G),EquationHom(Hom)];
				fi;
				#Does N end with a constant?
				if IsInt(h[Length(h)]) then
					return [N[1]*Equation([-x,v,x],G),EquationHom(Hom)*N[2]]; #DONE
				else
					c:= h[Length(h)];
					Hom := [];
					Hom[x] := Equation(Concatenation([x],w2,[c^-1]),G); #DONE
					return [N[1][[1..Length(h)-1]]*Equation([-x,v,x,c],G),EquationHom(Hom)*N[2]]; #DONE
				fi;
			end;
			# w = w11·v⁻·w12·x⁻·v·x·w2
			case11a := function(w11,w12,v,w2,x,G)
				local N,Hom,h;
				#Print("Case 11a:");
				#View([w11,w12,v,w2,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w11,w12,w2),G));
				Hom := [];
				h := Equation(w11,G)^-1;
				Hom[x] := Equation(Concatenation(w11,[x]),G)*Equation(w12,G)^-1 * h ; #DONE
				Hom[v] := Equation(Concatenation(w11,[v]),G) *h; #DONE
				return [Equation([-v,-x,v,x],G)*N[1],EquationHom(Hom)*N[2]]; #DONE
			end;
			# w = w1·x⁻·v·x·w21·v⁻·w22
			case11b := function(w1,v,w21,w22,x,G)
				local N,Hom,h;
				#Print("Case 11b:");
				#View([w1,v,w21,w22,x]);
				#Print("\n");
				N := NormalForm2(Equation(Concatenation(w1,w21,w22),G));
				Hom := [];
				Hom[x] := Equation(Concatenation(w1,w21,[x]),G) *Equation(w1,G)^-1;#DONE
				Hom[v] := Equation(Concatenation(w1,w21,[-v]),G) *Equation(Concatenation(w1,w21),G)^-1;#DONE
				return [Equation([-x,-v,x,v],G)*N[1],EquationHom(Hom)*N[2]];#DONE
			end;
			# w = x²·w2
			case3 := function(x,w2,G)
				local N,N2,Hom,y,z;
				#Print("Case 3:");
				#View([x,w2]);
				#Print("\n");
				N := NormalForm2(Equation(w2,G));
				#Check if N start with [y,z]
				if Length(N[1]!.word)<4 or not IsInt(N[1]!.word[2]) or N[1]!.word[1]=N[1]!.word[2] then
					#Print("End is Ok.. leaving Case 3\n");
					return [Equation([x,x],G)*N[1],N[2]];
				else
					#Print("w2 contains commutator...\n");
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := [];
					Hom[x] := Equation([x,x,-y,-x],G);#DONE
					Hom[y] := Equation([x,y,-x,-z,-x],G);#DONE
					Hom[z] := Equation([x,z],G);#DONE
					N2 := case3(z,N[1]!.word{[5..Length(N[1]!.word)]},G);
					return [Equation([x,x,y,y],G)*N2[1],N[2]*N2[2]*EquationHom(Hom)];#DONE
				fi;
			end;
			if IsOrientedEquation(xx) then
				if Length(w)<3 then
					return [xx,EquationHom([],xx!.group)];
				fi;
				#Print("Oriented");
				#Find x s.t. w=w1 -x v x w2 with |v| minimal
				t:= rec();
				for i in w do
					if IsInt(i) then
						i:= AbsInt(i);
						if IsBound(t.(i)) then
							t.(i) := -t.(i);
						else
							t.(i) := 0;
						fi;
					fi;
					for j in Set(RecNames(t)) do
						if t.(j)>=0 then
							t.(j) := t.(j) +1;
						fi;
					od;
				od;
				#counting done
				#Print("Counting dict: ",t,"\n");
				x := 0;
				vlen := -Length(w);
			# !!! this leads to different results on
			# differnt machines, because RecNames is machine dependently sorted
			# Set resolves this!					
			for i in Set(RecNames(t)) do
				if t.(i)>vlen then
					x := i;
					vlen := t.(i);
				fi;
			od;
			x := Int(x);
			#Minimal i found; yup
			first := true;
			toInvert := false;
			for i in [1..Length(w)] do
				if IsInt(w[i]) and AbsInt(w[i]) = x then
					if first then
						if w[i]>0 then
							toInvert := true;
						fi;
						w1 := w{[1..i-1]};
						first := false;
						j:= i+1;
					else 
						v:= w{[j..i-1]};
						if i<Length(w) then
							w2 := w{[i+1..Length(w)]};
						else
							w2 := [];
						fi;
						break;
					fi;
				fi;
			od;
			Hom := [];
			if toInvert then
				Hom[x] := Equation([-x],xx!.group);
			fi;
			Hom := EquationHom(Hom,xx!.group);
			#Decomposition done
			if Length(v)=1 then #Case 1
				v := v[1];
				if IsInt(v) then #Case 1.1
					if v<0 then
						Hom2 := [];
						Hom2[-v] := Equation([v],xx!.group);#DONE
						Hom := Hom*EquationHom(Hom2);#DONE
					fi;
					i := Position(w1,-v);
					if not i = fail then #Case 1.1.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						N := case11a(w11,w12,AbsInt(v),w2,x,xx!.group);
						#Display(N[2]!.rules[1]!.word);
						return [N[1],Hom*N[2]];#DONE
					else #Case 1.1.b
						i := Position(w2,-v);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N:= case11b(w1,AbsInt(v),w21,w22,x,xx!.group);
						return [N[1],Hom*N[2]];#DONE
					fi;
				else #Case 1.0
					N := case10(w1,v,w2,x,xx!.group);
					return [N[1],Hom*N[2]];#DONE
				fi;
				else #Case 2
					#Print("Case2.");
					y := 0;
					for i in v do
					if IsInt(i) then
						y := i;
						if i<0 then
							break;
						fi;
					fi;
					od;
					i := Position(v,y);
					if y>0 then
						Hom2 := [];
						Hom2[y] := Equation([-y],xx!.group);
						Hom := Hom*EquationHom(Hom2);#DONE
						#y := -y;
					fi;
					y := -y;
					v1 := v{[1..i-1]};
					v2 := v{[i+1..Length(v)]};
					i := Position(w1,y);
					if not i = fail then #Case 2.a
						#Print("a. ");
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						N := case11a(w11,Concatenation(v2,v1),x,Concatenation(w12,w2),AbsInt(y),xx!.group);
						Hom2 := [];
						Hom2[x] :=Equation(Concatenation(v2,[x]),xx!.group)*Equation(Concatenation([AbsInt(y)],w12),xx!.group)^-1;#DONE
						return [N[1],Hom*EquationHom(Hom2)*N[2]];#DONE
					else #Case 2.b
						#Print("b. ");
						i := Position(w2,y);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N := case11a(Concatenation(w1,w21),Concatenation(v2,v1),x,w22,AbsInt(y),xx!.group);
						Hom2 := [];
						Hom2[x] := Equation(Concatenation(v2,[x],w21),xx!.group); #DONE
						return [N[1],Hom*EquationHom(Hom2)*N[2]];#DONE
					fi;
				fi; #End Case 2
				else #so not oriented
					#Print("Nonoriented Case:\n");
					#find x s.t. w = w1·x·w2·x·w3
					t:= rec();
					for i in [1..Length(w)] do
						if IsInt(w[i]) then
						if IsBound(t.(w[i])) then
							x:= w[i];
							w1:= w{[1..t.(w[i])-1]};
							w2:= w{[t.(w[i])+1..i-1]};
						w3:= w{[i+1..Length(w)]};
						break;
						else        
							t.(w[i]) := i;
						fi;
					fi;
				od;
				Hom := [];
				if x<0 then
					Hom[-x] := Equation([x],xx!.group);
					x := -x;
				fi;
				Hom := EquationHom(Hom,xx!.group);
				Hom2 := [];
				Hom2[x] := Equation(Concatenation(w1,[x],w2),xx!.group) * Equation(w1,G)^-1;#DONE
				Hom := Hom*EquationHom(Hom2);#DONE
				w2 := Equation(w2,G)^-1;
				w2 := w2!.word;
				N := case3(x,Concatenation(w1,w2,w3),xx!.group);
				return [N[1],Hom*N[2]];#DONE
			fi; #End Nonoriented Case	
			Print("Not implemented yet\n");
			return [];
		end;
		NormalUnknowns := function(N)
		local w,i,L,Hom,cur;
			Hom := [];
			cur := 0;
			L := [];
			w := [];
			for i in N!.word do
				if IsInt(i) then
					if IsBound(L[AbsInt(i)]) then
						Add(w,SignInt(i)*L[AbsInt(i)]);
					else
						cur := cur +1;
						L[AbsInt(i)] := cur;
						Hom[cur] := Equation([AbsInt(i)],N!.group);
						Add(w,SignInt(i)*cur);
					fi;
				else
					Add(w,i);
				fi;
			od;
			return [Equation(w,N!.group),EquationHom(Hom,N!.group)];
		end;
		if IsSquareEquation(x) then
			N := NormalForm2(x);
			N2 :=NormalUnknowns(N[1]);
			return [N2[1],N[2]*N2[2]];
		else
			TryNextMethod();
		fi;
	end
);
InstallMethod(EquationDecomposed, "for a Grpword",
	[IsEquation],
	function(w)
		local Perm,A,C,tau,i,Var,L,v;
		if not IsEquationDecomposableRep(w) then
			w := EquationDecomposable(w);
		fi;
		A := AlphabetOfFRSemigroup(w!.group);
		Perm := SymmetricGroup(A);
		C := [];
		Var := Set(List(UnknownsOfEquation(w),AbsInt));
		for tau in Cartesian(ListWithIdenticalEntries(Length(Var),Perm))  do
			L := [];
			v := One(w!.group);
			for i in w!.word do
				if IsInt(i) then
					i := FREquationUnknown(i,tau[Position(Var,AbsInt(i))],w!.group);
				fi;
				v := v *i;
			od;
			Add(C,[EquationReducedForm(v),tau]);
		od;
		return [C,w!.hom];
	end
);
CleanSolution := function(H,w)
	local Var,Hom,i,j;
	Var := Set(List(UnknownsOfEquation(w),AbsInt));
	Hom := [];
	#Free Variale can be set to One
	for i in Var do
		if not IsBound(H!.rules[i]) then
			Hom[i]:= OneOp(w);
		fi;
	od;
	Hom := EquationHom(Hom,w!.group);
	H:= Hom * H;
	#Remove other entries
	Hom := [];
	for i in [1..Length(H!.rules)] do
		if IsBound(H!.rules[i]) and not i in Var then
			Unbind(H!.rules[i]);
		fi;
	od;
	return H;
end;
InstallMethod(EquationHomCompose, "for a List of EquationHom and a list of permutation and a group",
	[IsEquationHom,IsList,IsGroup],
	function(H,L,G)
		local d,Hom,i,j,elm,I;

		d := Length(AlphabetOfFRSemigroup(G));
		Hom := [];
		I := Concatenation(List([1..Length(L)],x->[x*(d+1)+1..x*(d+1)+d]));
		H := CleanSolution(H,Equation(I,G));
		for i in [1..Length(L)] do
			elm := [];
			for j in [1..d] do
				Add(elm,EquationAsElement(H!.rules[i*(d+1)+j]));
			od;
			Hom[i*(d+1)] := Equation([MEALY_FROM_STATES@(elm,L[i])],G);
		od;
		return EquationHom(Hom,G);
	end
);
Uniquify := function(W)
	local L,K,j,i,k,x,w,Hom;
	K := [];
	while true do
		L := [];
		x := 0;
		for i in [1..Length(W)] do
			for j in Set(List(UnknownsOfEquation(W[i]),AbsInt)) do 
				if IsBound(L[j]) then
					x := j; #All indices in W[j] have j as common variable
					break;
				else
					L[j]:=i;
				fi;
			od;
			if x <> 0 then
				break;
			fi;
		od;
		if x = 0 then
			return [W,EquationHom(K,W[i]!.group)];
		fi;
		#bring W[L[x][1]] in form x = w
		k := Position(W[i]!.word,x);
		j := -1;
		if k = fail then
			k := Position(W[i]!.word,-x);
			j:=1;
		fi;
		w :=(W[i][[k+1..Length(W[i]!.word)]] * W[i][[1..k-1]])^j;
		K[x] := w ;
		Hom := [];
		Hom[x] := w;
		Hom:=EquationHom(Hom);
		#Apply Hom on all entries of W
		W := List(W,x->ImageOfEquationHom(Hom,x));
	od;
end;
#Get Equation in S_n
Corresponding_Perm_word := function(w)
	local v;
	v := List(w!.word,function(i) if not IsInt(i) then i:= Activity(i); fi; return i; end);
	return Equation(v,SymmetricGroup(AlphabetOfFRSemigroup(w!.group)));
end;
#Solve equations in S_n
InstallMethod(EquationSolve, "for a PermGroupWord",
	[IsPermEquation],
	function(w)
		local Var, i, N,p,q,v,Hom,Sol;
		N := EquationNormalForm(w);
		Var := Set(List(UnknownsOfEquation(N[1]),AbsInt));
		Sol := [];		
		for p in Cartesian(ListWithIdenticalEntries(Length(Var),w!.group)) do
			#Print("Check ",p,"\n");
			Hom := EquationHom(List(p,x->Equation([x],w!.group)),w!.group);
			v:= ImageOfEquationHom(Hom,N[1]);
			#Print("Results in ",v!.word,"\n");
			q:=[];
			if IsOne(v) then
				Add(Sol,Hom*N[2]);
			fi;
		od;
		return Sol;
	end
);
rule_pr := function(grpwh)
	local N,h,x,y;
	h:= grpwh!.rules;
	for x in [1..Length(h)] do
		if IsBound(h[x]) then
			Print("[");
			for y in h[x]!.word do
				if IsInt(y) then
					Print(y,",");
				else
					#Print(y,",");
					Print("c,");
				fi;
			od;
			Print("],");
		else 
			Print(",");
		fi;
	od;
	Print("\n");
end;
InstallMethod(EquationSolve, "For a FRGroupWord",
	[IsEquation],
	function(w)
		local Var,v,i,j,k,N,Hom,Dec,Perms,Hom2,U,S,compl,ww;
			if not HasFullSCData(w!.group) then
				TryNextMethod();
			fi;
			if not FullSCFilter(w!.group) = IsFinitaryFRElement then
				TryNextMethod();
			fi;
			G := w!.group;
			N := EquationNormalForm(w);
			ww := w;
			Info(InfoFRGW,2,"Unnormalized ",ToString(w!.word));
			Info(InfoFRGW,2,"Call ",ToString(N[1]!.word));
			Var := Set(List(UnknownsOfEquation(N[1]),AbsInt));
			Hom := EquationHom(ListWithIdenticalEntries(Length(Var),OneOp(w)),G);
			if IsOne(ImageOfEquationHom(Hom,N[1])) then
				Info(InfoFRGW,2,"Call ",ToString(N[1]!.word)," Solution found");
				return [CleanSolution(Hom*N[2],w)];
			fi;
			#Perms := EquationSolve(Corresponding_Perm_word(N[1]));
			Dec := EquationDecomposed(N[1]); #TODO Replace with smaller set!.
			for w in Dec[1] do #Solve one of these
				Hom := EquationHom(List(w[2],x->Equation([x],SymmetricGroup(AlphabetOfFRSemigroup(G)))));
				if IsOne(ImageOfEquationHom(Hom,Corresponding_Perm_word(N[1]))) then
					Print("Solve System: ",w[1]);
					U := Uniquify(w[1]!.states); 
					Print("Simplified to", U,"\n");
					Hom2 := U[2];
					compl := true;
				Info(InfoFRGW,2,"Call ",ToString(N[1]!.word)," Try with perm. ",ToString(w[2]));
					for v in U[1] do#Solve all of these
						S := EquationSolve(v);
						Print("Solution for ",ToString(v!.word),":");
						rule_pr(S[1]);
						Print("\n");
						if not IsOne(ImageOfEquationHom(S[1],v)) then
							Error("Not real Solution");
						fi;
						if Length(S) = 0 then
							compl := false;
							break;
						else
							Hom2 := S[1]*Hom2;
						fi;
					od;
					if compl then
						return [CleanSolution(EquationHomCompose(Hom2,w[2],G)*Dec[2]*N[2],ww)];
					fi;
				fi;
			od;
			Info(InfoFRGW,2,"Call ",ToString(N[1]!.word)," No Solution!");
			return [];
	end
);
testfunc := function()
	local elms,e,L,xn,x,F,a,b,c,d,f1,f2,f3,others;
	G := GrigorchukGroup;
	a := G.1;
	b := G.2;
	c := G.3;
	d := G.4;
	elms := [[1,1],[-1,-1],[1,1,2,2],[-2,-1,2,1],[-1,-2,1,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
	F := FreeGroup(5);
	f1 := F.1;
	f2 := F.2;
	f3 := F.3;
	others := [Equation([-9,f1,-10,f2,9,10,f3],F)];
	L := [];

	for e in elms do
		x := Equation(e,G);
		xn := EquationNormalForm(x);
		if ImageOfEquationHom(xn[2],x) <> xn[1] then
			Add(L,e);
		fi;
	od;
	for e in others do
		xn := EquationNormalForm(e);
		if ImageOfEquationHom(xn[2],e) <> xn[1] then
			Add(L,e);
		fi;
	od;
	Print("Errors happened at L: ");
	Display(L);
	Print("\n");
	L := [];
	for e in elms do
		x := Equation(e,G);
		xn := EquationNormalFormInverseHom(x);
		if ImageOfEquationHom(xn[2],xn[1]) <> x then
			Add(L,e);
		fi;
	od;
	for e in others do
		xn := EquationNormalFormInverseHom(e);
		if ImageOfEquationHom(xn[2],xn[1]) <> e then
			Add(L,e);
		fi;
	od;
	Print("Errors happened at L: ");
	Display(L);
	Print("\n");

end;
