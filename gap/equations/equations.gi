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
####	                          EquationGroup                              ####
####                                                                         ####
#################################################################################
InstallMethod( IsEquationGroup,   "for a FreeProduct)",
   [ IsGeneralFreeProduct],
    G->Length(G!.groups)=2 and IsFreeGroup(G!.groups[2])
	);

InstallMethod( EquationGroup, "for two groups",
	[IsGroup,IsFreeGroup],
	function(G,Free)
		local Ob;
		Ob := FreeProduct(G,Free);
		Ob!.free :=Free;
		Ob!.const :=G;
		SetIsEquationGroup(Ob,true);
		return Ob;
	end);


InstallMethod( DecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	function(eqG)
		local DG,alph,DEqG;
		if not IsFRGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		if not IsFinitelyGeneratedGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		alph := AlphabetOfFRSemigroup(eqG!.const);
		if IsStateClosed(eqG!.const) then
			DG := eqG!.const;
		else
			DG := Group(List(alph,a->Concatenation(
					List(GeneratorsOfGroup(eqG!.const),gen->State(gen,a))) ));
		fi;
		DEqG := EquationGroup(DG,FreeProduct(ListWithIdenticalEntries(Size(alph),eqG!.free)));
		DEqG!.alph := alph;
		SetIsDecompositionEquationGroup(DEqG,true);
		return DEqG;
	end);

InstallMethod( IsDecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	EqG->HasFreeProductInfo(EqG!.free));
#################################################################################
####                                                                         ####
####	                          Equations                                  ####
####                                                                         ####
#################################################################################
InstallMethod( Equation, "(Equation) for a list of group elements and unknowns and boolean",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		local eq;
		#always reduce equation cyclicaly 
		if Length(elms)>= 1 and elms[1] in eqG!.const then
			elms := Concatenation(elms{[2..Size(elms)]},[elms[1]]);
		fi;
		eq := FreeProductElm(eqG,elms,List(elms,function(e)
													if e in eqG!.const then
														return 1; 
													fi; return 2;
												 end) );
		eq!.const := eqG!.const;
		eq!.free := eqG!.free;
		SetIsEquation(eq,true);
		return eq;
	end);

InstallMethod(EquationLetterRep, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	function(eq)
		local nw,elm,i,Eq;
		nw := [];
		for elm in eq!.word do
			if elm in eq!.const then
				Add(nw,elm); 
			else
				for i in LetterRepAssocWord(elm) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm),[i]));
				od;
			fi;
		od;
		Eq:= FreeProductElmLetterRep(eq!.group,nw,List(nw,function(e)
													if e in eq!.const then
														return 1;
													fi; return 2;
												 end) );
		Eq!.const := eq!.const;
		Eq!.free := eq!.free;
		SetIsEquation(eq,true);
		return Eq;
	end);

InstallMethod( EquationVariables, "for a Equation",
	[IsEquation and IsFreeProductElmRep],
	function(x)
		return List(Set(List(Concatenation(
			List(Filtered(x!.word,e->e in x!.free),	fw -> LetterRepAssocWord(fw))
			),i->AbsInt(i))),
			v->AssocWordByLetterRep(FamilyObj(One(x!.free)),[v]));
	end);

InstallMethod( ViewObj,   "for Equations)",
   [ IsEquation and IsFreeProductElmRep ],
    function( x )
		local s;
		Print("Equation in ",EquationVariables(x));
	end);

InstallMethod( OneOp, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	x -> Equation(x!.group,[]) 
	);

InstallOtherMethod( One,"for an EquationGroup",
    [ IsEquationGroup ],
    eqG -> Equation(eqG,[]) 
	);



InstallMethod(IsQuadraticEquation, "for a Equation",
		[IsEquation and IsFreeProductElmRep],
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

#################################################################################
####                                                                         ####
####	                     DecomposedEquations                             #### 
####                                                                         ####
#################################################################################
InstallOtherMethod(Equation, "(Equation) for a list of lists, a DecompositionEquationGroup and a permutation",
	[IsEquationGroup,IsList,IsPerm],
	function(G,words,perm)
		local factors,red,Ob;
		if not IsDecompositionEquationGroup(G)then
			TryNextMethod();
		fi;
		factors := List(words,w->List(w,function(e) 
					if e in G!.free then return 2;fi;return 1;end));
		red := List([1..Length(words)],i->FREE_PRODUCTS_REDUCE_WORDS(words[i],factors[i]));
		Ob:= Objectify(
				NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsDecomposedEquationRep),
				rec(words := List(red,r->r.word),
	    			factors := List(red,r->r.factors),
	       			group := G,
	       			const := G!.const,
	       			free := G!.free,
	       			activity := perm));
		SetIsEquation(Ob,true);
		return Ob;
	end);

InstallMethod(DecompositionEquation, "for an Equation a group homomorphism and an DecompositionEquationGroup",
		[IsEquationGroup,IsEquation,IsGroupHomomorphism],
		function(DEqG,eq,acts)
			local alph,vars,DecompEq,lastperm,x,i;
			if not IsDecompositionEquationGroup(DEqG)then
				TryNextMethod();
			fi;
			if not IsFRGroup(eq!.const) then
				TryNextMethod();
			fi;
			alph := AlphabetOfFRSemigroup(eq!.const);
			if not ForAll([1..Size(alph)],i->Source(Embedding(DEqG!.free,i))=eq!.free) then
				Error("DecompositionEquationGroup doesn't correspond to EquationGroup.");
			fi;
			vars := EquationVariables(eq);
			if Length(vars)=0 then
				vars := One(eq!.free);
			fi;
			if not Group(vars)=Source(acts) then
				Error("acts needs to be defined on the variables.");
			fi;
			if not IsPermGroup(Range(acts)) then
				TryNextMethod();
			fi;
			eq := EquationLetterRep(eq);
			DecompEq := List(alph,a->[]);
			lastperm := ();
			for x in eq!.word do
				if x in eq!.const then
					for i in [1..Size(alph)] do
						Add(DecompEq[i^lastperm],State(x,alph[i]));
					od;
					lastperm := lastperm*Activity(x);
				else
					if LetterRepAssocWord(x)[1]<0 then
						#eq is in LetterRep so this is the inverse of a gen.
						lastperm := lastperm*x^acts;
					fi;
					for i in [1..Size(alph)] do
						Add(DecompEq[i^lastperm],x^Embedding(DEqG!.free,i));
					od;
					if not LetterRepAssocWord(x)[1]<0 then
						lastperm := lastperm*x^acts;
					fi;
				fi;
			od;
			return Equation(DEqG,DecompEq,lastperm);
		end);


InstallMethod(EquationComponent, "for an DecomposedEquation and Integer",
	[IsEquation and IsDecomposedEquationRep, IsInt],
	function(eq,comp)
		if Length(eq!.words)<comp then
			Error("This component does not exist.");
		fi;
		return Equation(eq!.group,eq!.words[comp]);
	end);

InstallMethod(EquationComponents, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep ],
	eq->List([1..Length(eq!.words)],
			i->EquationComponent(eq,i) ));

InstallMethod(EquationVariables, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Set(Concatenation(List(EquationComponents(x),EquationVariables)));
	end);

InstallMethod( ViewObj,   "for DecomposedEquations)",
   [ IsEquation and IsDecomposedEquationRep ],
    function( x )
		local s;
		Print("DecomposedEquation in ",EquationVariables(x));
	   end);

InstallMethod( PrintObj,   "for DecomposedEquations)",
   [ IsEquation and IsDecomposedEquationRep ],
    function( x )
		local s;
		Print("Equation(",EquationComponents(x),")");
	   end);

InstallMethod( \=,  "for two DecomposedEquations",
		IsIdenticalObj,
    [ IsEquation and IsDecomposedEquationRep,
      IsEquation and IsDecomposedEquationRep ],
    function( x, y )
			return Size(x!.words) = Size(y!.words) and
					ForAll([1..Size(x!.words)],
						i->EquationComponent(x,i)=EquationComponent(y,i)) and
					x!.activity = y!.activity;
		end);

InstallMethod( OneOp, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
		x->	Equation(x!.group,List(x!.group!.alph,a->[]))
	);

InstallMethod( \*,   "for two DecomposedEquations",
	IsIdenticalObj,
    [ IsEquation and IsDecomposedEquationRep, IsEquation and IsDecomposedEquationRep ],0,
    function( x, y )
    	return Equation(x!.group,
    			List([1..Length(x!.words)],
    				i->Concatenation(x!.words[i],y!.words[i^x!.activity])),
    			x!.activity*y!.activity);
    end);

InstallMethod( InverseOp, "for a DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Equation(x!.group,
				Permuted(List(x!.words,w->Reversed(List(w,Inverse))),x!.activity^-1),
    			x!.activity^-1);
	end);

#################################################################################
####                                                                         ####
####	                     EquationsHomomorphism                           ####
####                                                                         ####
#################################################################################

InstallMethod(EquationHomomorphism ,"For an an EquationGroup and two group Homomorphisms",
	[IsEquationGroup, IsGroup, IsGroupHomomorphism, IsGroupHomomorphism],
	function(SourceEqG,Target,mapFree,mapGroup)
		local fam,RangeEqG;
		if not IsFreeGroup(Source(mapFree)) then
			Error("1. Argument need to be a homomorphism from a free group");
		fi;
		
		fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(SourceEqG)),
									 ElementsFamily(FamilyObj(Target)) );
		return Objectify(NewType(fam,IsEquationHomomorphism and IsEquationHomomorphismRep),
							rec(	mapFree := mapFree, 
									mapGroup := mapGroup,
									SourceEqG := SourceEqG,
									Range := Target));
	end);

InstallOtherMethod(EquationHomomorphism, "For an EquationGroup, a list of variables, and a list of images",
	[IsEquationGroup,IsList,IsList],
	function(eqG,gens,imgs)
		local homFree,nimgs,ngens,hom;
		if not Length(gens) = Length(imgs) then
			Error("There must be as many images as generators");
		fi;
		if Length(gens) = 0 then
			hom := EquationHomomorphism(eqG,eqG,IdentityMapping(eqG!.free),IdentityMapping(eqG!.group));
			SetInverseGeneralMapping( hom, hom );
		    ImmediateImplicationsIdentityMapping( hom );
		    SetName(hom,"<Identity EqHom>");
		    SetIsOne(hom,true);
			return hom;
		fi;
		if not ForAll(gens,g->g in GeneratorsOfGroup(eqG!.free)) then
			TryNextMethod();
		fi;
		ngens := List(gens,gen->LetterRepAssocWord(gen)[1]);
		
		nimgs := List(imgs,function(x)
				if IsList(x) then
					return(Equation(x,eqG));
				elif IsEquation(x) then
					return x;
				elif x in eqG!.group or x in eqG!.free then
					return(Equation([x],eqG));
				else 
					Error("Wrong input!");
				fi;
			end);
		homFree := GroupHomomorphismByFunction(eqG!.free,eqG,function(w)
			return Product(List(LetterRepAssocWord(w),
				function(x)
					local pos;
						pos := Position(ngens,AbsInt(x));
						if pos = fail then
							return Equation([AssocWordByLetterRep(FamilyObj(w),[x])],eqG);
						else
							return nimgs[pos]^SignInt(x);
						fi;	
				end));
			end);
		hom := EquationHomomorphism(eqG,eqG,homFree,IdentityMapping(eqG!.group));
		SetEquationHomomorphismImageData(hom,rec(imgs:=imgs,gens:=gens));
		return hom;

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

#Composition Mapping acts from the left.
# h1*h2 = Composition(h2,h1)
InstallMethod( CompositionMapping2, "For two EquationHomomorphisms",
	FamSource1EqFamRange2,
	[IsEquationHomomorphism,IsEquationHomomorphism],0,
	function(hom2,hom1)
		local com,imDa1,imDa2;
		com := EquationHomomorphism(Source(hom1),Range(hom2),
				CompositionMapping2(hom2,hom1!.mapFree),
				CompositionMapping2(hom2!.mapGroup,hom1!.mapGroup));
		if ForAll([hom2,hom1],HasEquationHomomorphismImageData) then
			imDa1 := EquationHomomorphismImageData(hom1);
			imDa2 := EquationHomomorphismImageData(hom2);
			SetEquationHomomorphismImageData(com,
				rec(gens:=[imDa1.gens,imDa2.gens],
					imgs:=[imDa1.imgs,imDa2.imgs]) );
		fi;
		return com;
	end	);

InstallMethod( CompositionMapping2, "For an EquationHomomorphism and a group Homomorphisms",
	FamSource1EqFamRange2,
	[IsEquationHomomorphism,IsGroupHomomorphism],0,
	function(hom2,hom1)
		return GroupHomomorphismByFunction(Source(hom1),Range(hom2),
					w->(hom1!.fun(w))^hom2);
	end	);

InstallMethod( IdentityMapping,
    "for an Equation Group",
    true,
    [ IsEquationGroup ], 0,
    function( eqG )
	    return EquationHomomorphism(eqG,[],[]);
    end );

InstallMethod(ImageElm ,"For an EquationHomomorphism and an Equation",
	[IsEquationHomomorphism,IsEquation and IsFreeProductElmRep],
	function(hom,eq)
		local res;
		eq := EquationLetterRep(eq);
		res := List(eq!.word,function(elm)	
								if elm in eq!.const then
									return elm^hom!.mapGroup;
								elif elm in Source(hom!.mapFree) then
									return elm^hom!.mapFree;
								fi;
								return elm; end);
		if IsEquationGroup(Range(hom)) then
			if ForAny(res,IsEquation) then
				Apply(res,function(x)
					if IsEquation(x) then return x!.word; else return x; fi;
				 end);
			fi;
			if ForAny(res,IsList) then
				res:= Flat(res);
			fi;
			return Equation(res,Range(hom));
		else 
			return Product(res);
		fi;
	end);

InstallMethod(ImageElm ,"For an EquationHomomorphism and an Equation",
	[IsEquationHomomorphism,IsEquation and IsDecomposedEquationRep],
	function(hom,eq)
		local res;
		res := List(EquationComponents(eq),neq->neq^hom!.word);
		return Equation(res,eq!.eqG,eq!.activity);
	end);

InstallMethod(ViewObj, "For an EquationsHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		local imDa;
		if HasEquationHomomorphismImageData(hom) then
			imDa := EquationHomomorphismImageData(hom);
			View(imDa.gens,"->",imDa.imgs);
		else
			View(Source(hom),"->",Range(hom));
		fi;
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
		if not ForAll(L,elm->elm in eq!.const) then
			Error("All images need to be in the group of constants.");
		fi;
		var := EquationVariables(eq);
		if not Length(var)=Length(L) then
			Error("There must be as many images as variables.");
		fi;
		return EquationHomomorphism(eq!.eqG,eq!.const,
					GroupHomomorphismByImages(Group(var),eq!.const,L),
					IdentityMapping(eq!.const));
	end);

#Example
G := GrigorchukGroup;
BS := BranchStructure(G);
pi := BS.quo;
AssignGeneratorVariables(G);
F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);
SetName(F,"FX");
EqG := EquationGroup(G,F);
Eq := Equation(EqG,[Comm(F.1,F.2),(a*b)^2]);
id := IdentityMapping(G);

DEqG := DecompositionEquationGroup(EqG);
constr := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),[(),()]);
DEq:=DecompositionEquation(DEqG,Eq,constr);


ev := EquationEvaluation(Eq,[a,b*a]);
Image(ev,Eq);

h1 := EquationHomomorphism(EqG,[F.1,F.3],[F.2,F.5]);
h2 := EquationHomomorphism(EqG,[F.3],[F.7]);






