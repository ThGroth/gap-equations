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
#
# Taken analously to Position in lib/wordrep.gi
InstallMethod( \in, "for infinite list of generators",
	[IsObject,IsList and IsInfiniteListOfGeneratorsRep],
	function(elm,List)
		local ext;
	    if FamilyObj( elm ) <> List![1] then
    	  return false;
    	fi;
	    if IsAssocWord( elm ) then
      		ext:=LetterRepAssocWord(elm);
      		if Length(ext)<> 1 or ext[1]<0 then
        		return false;
      		else
        		return true;
      		fi;
    	else
      		ext:= ExtRepOfObj( elm );
      		if not IsInt( ext ) then
        		return false;
      		else
        		return true;
      		fi;
    	fi;
    end );


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

InstallOtherMethod(Abs, "for associative words",
	[IsAssocWord],
	w-> AssocWordByLetterRep(FamilyObj(w),List(LetterRepAssocWord(w),AbsInt))
	);

InstallMethod(FreeProductOp, "for infinitely generated free groups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,FP,i,names,nameLen;
		if not ForAll(L,IsFreeGroup) then 
			TryNextMethod();
		fi;
		if ForAny(L,IsFinitelyGeneratedGroup) then 
			TryNextMethod();
		fi;
		embeddings :=[];
		#If all groups have the same length of init names
		#give good new names
		nameLen := Length(FamilyObj(Representative(G))!.names![2]);
		if ForAll(L,H->Length(FamilyObj(Representative(H))!.names![2])=nameLen) then
			names := Concatenation(List([1..nameLen],
				i->List([1..Length(L)],
				j->Concatenation(FamilyObj(Representative(L[j]))!.names![2][i],String(j)) )));	
		else
			names := [];
		fi;
				
		FP := FreeGroup(infinity,"yn",names);
		if ForAll(L,HasName) then
			SetName(FP,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;
    	for i in [1..Length(L)] do
    		if i = 1 then
    			Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				FP,
    				w-> AssocWordByLetterRep(FamilyObj(Representative(FP)),
    					List(LetterRepAssocWord(w),k->SignInt(k)*(Length(L)*(AbsInt(k)-1)+1)))));
    		elif i = 2 then
    			Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				FP,
    				w-> AssocWordByLetterRep(FamilyObj(Representative(FP)),
    					List(LetterRepAssocWord(w),k->SignInt(k)*(Length(L)*(AbsInt(k)-1)+2)))));
    		else
    			Error("Not implemented yet");
    		fi;
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
	end);

InstallOtherMethod(Length, "for a Equation",
	[IsEquation and IsEquationRep],
	function(x)
		return Length(x!.word);
	end);

InstallOtherMethod(Position, "for an Equation and an generator or constant and an offset",
	[IsEquation and IsEquationRep,IsMultiplicativeElementWithInverse, IsInt],
	function(eq,elm,from)
		if not elm in eq!.free and not elm in eq!.group then
			TryNextMethod();
		fi;  
		return Position(eq!.word,elm,from);
	end);

InstallMethod( PrintObj,   "for Equations)",
   [ IsEquation and IsEquationRep ],
    function( x )
		local s;
		Print("Equation in ",EquationVariables(x));
	end);

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
		if Length(newword)>= 1 and newword[1] in x!.group then
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

InstallOtherMethod(\{\}, "for an Equation",
	[IsEquation and IsEquationRep,IsList],
	function(w,i) 
		return Equation(w!.word{i},w!.group,w!.free);
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

InstallMethod( \*,   "for an Equation and a variable or constant",
    [ IsEquation and IsEquationRep, IsMultiplicativeElementWithInverse ],
    function( x, y )
    	if not y in x!.group and not y in x!.free then
    		TryNextMethod();
    	fi;
    	return Equation(Concatenation(x!.word,[y]),x!.group,x!.free);
    end 
);

InstallMethod( \*,   "for a variable or constant and an Equation",
    [IsMultiplicativeElementWithInverse, IsEquation and IsEquationRep ],
    function( x, y )
    	if not x in y!.group and not x in y!.free then
    		TryNextMethod();
    	fi;
    	return Equation(Concatenation([x],y!.word),y!.group,y!.free);
    end 
);

InstallMethod(InverseOp, "for a Equation",
	[IsEquation and IsEquationRep],
	function(x)
		return Equation(Reversed(List(x!.word,InverseOp)),x!.group,x!.free);
	end
);

InstallMethod(EquationLetterRep, "for an Equation",
	[IsEquation and IsEquationRep],
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

#################################################################################
####                                                                         ####
####	                     DecomposedEquations                             #### 
####                                                                         ####
#################################################################################
InstallOtherMethod(Equation, "(Equation) for a list of lists, a DecompositionEquationGroup and a permutation",
	[IsList,IsEquationGroup,IsPerm],
	function(words,DEqG,perm)
		if not IsDecompositionEquationGroup(DEqG)then
			TryNextMethod();
		fi;
		return Objectify(NewType(ElementsFamily(FamilyObj(DEqG)), IsEquation and IsDecomposedEquationRep),
    				rec(words := words,
       					group := DEqG!.group,
       					free := DEqG!.free,
       					eqG := DEqG,
       					activity := perm));
	end);

InstallMethod(DecompositionEquation, "for an Equation a group homomorphism and an DecompositionEquationGroup",
		[IsEquation,IsGroupHomomorphism,IsEquationGroup],
		function(eq,acts,DEqG)
			local alph,vars,DecompEq,lastperm,x,i;
			if not IsDecompositionEquationGroup(DEqG)then
				TryNextMethod();
			fi;
			if not IsFRGroup(eq!.group) then
				TryNextMethod();
			fi;
			alph := AlphabetOfFRSemigroup(eq!.group);
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
				if x in eq!.group then
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
			return Equation(DecompEq,DEqG,lastperm);
				
			#return List(DecompEq,L->Equation(L,DEqG))
		end);


InstallMethod(EquationComponent, "for an DecomposedEquation and Integer",
	[IsEquation and IsDecomposedEquationRep, IsInt],
	function(eq,comp)
		if Length(eq!.words)<comp then
			Error("This component does not exist.");
		fi;
		return Equation(eq!.words[comp],eq!.eqG);
	end);

InstallMethod(EquationComponents, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep ],
	eq->List(eq!.words,word->Equation(word,eq!.eqG)));

InstallMethod(EquationVariables, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Set(Concatenation(List(EquationComponents(x),EquationVariables)));
	end);

InstallMethod( PrintObj,   "for DecomposedEquations)",
   [ IsEquation and IsDecomposedEquationRep ],
    function( x )
		local s;
		Print("DecomposedEquation in ",EquationVariables(x));
	   end 
);

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

InstallMethod(OneOp, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
		x->	Equation([],x!.group())
);

InstallMethod( \*,   "for two DecomposedEquations",
    [ IsEquation and IsDecomposedEquationRep, IsEquation and IsDecomposedEquationRep ],
    function( x, y )
    	if not Length(x!.words) = Length(y!.words) then
    		Error("Not compatible, differnt number of states");
    	fi;
    	if not x!.eqG = y!.eqG then
    		Error("Not compatible, differnt number Groups");
    	fi;
    	return Equation(
    			List([1..Length(x!.words)],
    				i->Concatenation(x!.words[i],y!.words[i^x!.activity])),
    			x!.eqG,
    			x!.activity*y!.activity);
    end 
);

InstallMethod(InverseOp, "for a DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Equation(Permuted(Reversed(List(x!.words,Inverse)),x!.activity^-1),
    			x!.eqG,
    			x!.activity^-1);
	end
);

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
		
		if Range(mapFree)=Range(mapGroup) then
			RangeEqG := Range(mapGroup);
		elif IsEquationGroup(Range(mapFree)) then
			RangeEqG := Range(mapFree);
		else
			RangeEqG := EquationGroup(Range(mapGroup),Range(mapFree));
		fi;
		fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(SourceEqG)),
									 ElementsFamily(FamilyObj(RangeEqG)) );
		return Objectify(NewType(fam,IsEquationHomomorphism),
							rec(	mapFree := mapFree, 
									mapGroup := mapGroup,
									SourceEqG := SourceEqG,
									Range := RangeEqG));
	end);

InstallOtherMethod(EquationHomomorphism, "For an EquationGroup, a list of variables, and a list of images",
	[IsEquationGroup,IsList,IsList],
	function(eqG,gens,imgs)
		if not Length(gens) = Length(imgs) then
			Error("There must be as many images as generators");
		fi;
		if Length(gens) = 0 then
			return EquationHomomorphism(eqG,IdentityMapping(eqG!.free),IdentityMapping(eqG!.group));
		fi;
		if not ForAll(gens,g->g in GeneratorsOfGroup(eqG!.free)) then
			TryNextMethod();
		fi;
		if ForAll(imgs,x->x in eqG!.group) then #Evaluation
			return EquationHomomorphism(eqG,
									GroupHomomorphismByImages(Group(gens),eqG!.group,imgs),
									IdentityMapping(eqG!.group));	
		elif ForAll(imgs,x->x in eqG!.free) then #Renaming
			return EquationHomomorphism(eqG,
									GroupHomomorphismByImages(Group(gens),eqG!.free,imgs),
									IdentityMapping(eqG!.group));
		elif ForAny(imgs,IsList) then 
			imgs := List(imgs,function(x)
				if IsList(x) then
					return(Equation(x,eqG));
				elif IsEquation(x) then
					return x;
				else 
					return Equation([x],eqG);
				fi;
				end);
		fi;
		if not ForAll(imgs,IsEquation) then
			Error("Wrong input!");
		fi;
		return EquationHomomorphism(eqG,
					GroupHomomorphismByImages(Group(gens),eqG,imgs),
					IdentityMapping(eqG!.group));
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
		return EquationHomomorphism(Source(hom2),
				CompositionMapping2(hom2!.mapFree,hom1!.mapFree),
				CompositionMapping2(hom2!.mapGroup,hom1!.mapGroup));
	end	);

InstallMethod(ImageElm ,"For an EquationHomomorphism and an Equation",
	[IsEquationHomomorphism,IsEquation and IsEquationRep],
	function(hom,eq)
		local res;
		eq := EquationLetterRep(eq);
		res := List(eq!.word,function(elm)	
								if elm in eq!.group then
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
			if ForAll(res,x -> x in Range(hom)) then
				return Product(res);
			else
				return Equation(res,eq!.eqG);
			fi;
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
F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);
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


h1 := EquationHomomorphism(EqG,[F.1,F.3],[F.2,F.5]);
h2 := EquationHomomorphism(EqG,[F.3],[F.7]);
h := h2*h1;

Eq2 := Equation([F.1],EqG);
acts :=  GroupHomomorphismByImages(Group(EquationVariables(Eq2)),SymmetricGroup(2),[(1,2)]);
#
#
#
InstallMethod(EquationNormalForm, "for an Equation",
	[IsEquation and IsEquationRep],
	function(x)
		local G,F,EqG,NormalForm,N,H,NormalVars;
		if not IsSquareEquation(x) then
			TryNextMethod();
		fi;
		G := x!.group;
		F := x!.free;
		EqG := x!.eqG;
		#Recursive worker function
		NormalForm:= function(eq)
			local case10,case11a,case11b,case3,i,j,t,x,y,Hom,N,
				  asInt,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3;
			Info(InfoFRGW,3,"Call of NormalForm¸with",eq);
			
			case10 := function(w1,v,w2,x)
				# eq = w₁·x⁻·v·x·w₂
				# w₁,w₂ Equations v∈G,x∈F 
				local N,Hom,c;
				N := NormalForm(w1*w2);
				Hom := EquationHomomorphism(EqG,[x],[x*w2^-1]);
				if Length(h)=0 then
					return [Equation([x^-1,v,x],EqG),Hom];
				fi;
				#Does N end with a constant?
				c:= N[1]!.word[Length(N[1])];
				if c in F then
					return [N[1]*Equation([x^-1,v,x],EqG),N[2]*Hom];
				else
					Hom := EquationHomomorphism(EqG,[x],[x*(c*w2^-1)]);
					return [N[1]*c^-1*(x^-1*v*x)*c,N[2]*Hom];
				fi;
			end;
			case11a := function(w11,w12,v,w2,x)
				# w = w₁₁·v⁻·w₁₂·x⁻·v·x·w₂
				# # w₁₁,w₁₂,w₂ Equations v,x∈F 
				local N,Hom;
				N := NormalForm(w11*w12*w2);
				Hom := EquationHomomorphism(EqG,[x,v],[
						w11^-1*x*w11*w12,
						w11^-1*v*w11]);
				return [Comm(v,x)*N[1],N[2]*Hom];
			end;
			case11b := function(w1,v,w21,w22,x)
				# w = w₁·x⁻·v·x·w₂₁·v⁻·w₂₂
				# # w₁,w₂₁,w₂₂ Equations v,x∈F 
				local N,Hom;
				N := NormalForm(w1*w21*w22);
				Hom := EquationHomomorphism(EqG,[x,v],[
						w21^-1*w1^-1*x*w1,
						w21^-1*w1^-1*v^-1*w1*w21]);
				return [Comm(x,v)*N[1],N[2]*Hom];
			end;
			case3 := function(x,w2)
				# w = x²·w2
				# w₂ Equation, x∈F
				local N,N2,Hom,y,z;
				N := NormalForm(w2);
				#Check if N start with [y,z]
				N[1]:=EquationLetterRep(N[1]);
				if Length(N[1])<4 or not N[1]!.word[2] in F or N[1]!.word[1]=N[1]!.word[2] then
					#Already in required form
					return [x^2*N[1],N[2]];
				else
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := EquationHomomorphism(EqG,[x,y,z],[
							x*y*z,
					        (y*z)^(x*y*z),
					        (y*x^-1)^z]);
					N2 := case3(z,N[1][[5..Length(N[1])]]);
					return [x^2*y^2*N2[1],Hom*N2[2]*N[2]];
				fi;
			end;
			eq := EquationLetterRep(eq);
			if Length(eq)<3 then
				return [eq,EquationHomomorphism(EqG,[],[])];
			fi;
			#Find x s.t. w=w₁ x^±1 v x w₂ with |v| minimal
			t := [];
			Perform(EquationVariables(eq),function(v) t[LetterRepAssocWord(v)[1]]:=0; end);
			
			for i in [1..Length(eq)] do
				x := eq!.word[i];
				if x in F then
					asInt := LetterRepAssocWord(x)[1];
					t[AbsInt(asInt)]:=i-t[AbsInt(asInt)]; 
				fi;
			od;
			x := AssocWordByLetterRep(FamilyObj(Representative(F)),
							[PositionProperty(t,i->i=Minimum(t))]);
			Print("x=",x,"\n");
			if IsOrientedEquation(eq) then
				#Find Decomposition w₁ x⁻¹ v x w₂ 
				i := Position(eq,x^-1);
				j := Position(eq,x);
				if i>j then 
					Hom := EquationHomomorphism(EqG,[x],[x^-1]);
					j:=Position(eq,x^-1);
					i := Position(eq,x);
				else
					Hom := EquationHomomorphism(EqG,[],[]);
				fi;
				w1 := EquationLetterRep(eq{[1..i-1]});
				v := EquationLetterRep(eq{[i+1..j-1]});
				w2 := EquationLetterRep(eq{[i+j..Length(eq)]});
				
				#Decomposition done
				if Length(v)=1 then #Case 1
					v := v!.word[1];
					if v in F then #Case 1.1
						#v->v⁻¹ if v is not a generator. 
						Hom := EquationHomomorphism(EqG,[Abs(v)],[v])*Hom;
						i := Position(w1,v^-1);
						if not i = fail then #Case 1.1.a
							w11 := w1{[1..i-1]};
							w12 := w1{[i+1..Length(w1)]};
							N := case11a(w11,w12,Abs(v),w2,x);
							return [N[1],N[2]*Hom];
						else #Case 1.1.b
							i := Position(w2,v^-1);
							if i = fail then 
								Error("Strange Error. Is Equation quadratic?");
							fi;
							w21 := w2{[1..i-1]};
							w22 := w2{[i+1..Length(w2)]};
							N:= case11b(w1,Abs(v),w21,w22,x);
							return [N[1],N[2]*Hom];
						fi;
					else #Case 1.0
						N := case10(w1,v,w2,x);
						return [N[1],N[2]*Hom];
					fi;
				else #Case 2
					y := First(v!.word,e->e in F);
					Hom := EquationHomomorphism(EqG,[Abs(y)],[y^-1])*Hom;
					#v = v1 y v
					i := Position(v,y);
					v1 := v{[1..i-1]};
					v2 := v{[i+1..Length(v)]};

					i := Position(w1,y^-1);
					if not i = fail then #Case 2.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						Hom := EquationHomomorphism(EqG,[x],[v2^-1*x*(Abs(y)*w12)])*Hom;
						N := case11a(w11,v2*v1,x,w12*w2,Abs(y));
						return [N[1],N[2]*Hom];
					else #Case 2.b
						i := Position(w2,y^-1);
						if i = fail then 
							Error("Strange Error. Is Equation quadratic?");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N := case11a(w1*w21,v2*v1,x,w22,AbsInt(y));
						Hom := EquationHomomorphism(EqG,[x],[v2^-1*x*w21^-1])*Hom;
						return [N[1],N[2]*Hom];
					fi;
				fi; 
			else #so not oriented
				i := Position(eq,x);
				if i=fail then
					Hom := EquationHomomorphism(EqG,[x],[x^-1]);
					i := Position(eq,x^-1);
					j := Position(eq,x^-1,i);
				else	
					Hom := EquationHomomorphism(EqG,[],[]);
					j := Position(eq,x,i);
				fi;
				w1:= eq{[1..i-1]};
				w2:= eq{[i+1..j-1]};
				w3:= eq{[j+1..Length(eq)]};
				Hom := EquationHomomorphism(EqG,[x],[w1^-1*x*w1*w2^-1])*Hom;
				N := case3(x,w1*w2^-1*w3);
				return [N[1],N[2]*Hom];
			fi; #End Nonoriented Case	
		end;
		NormalVars := function(eq)
			local gens,imgs,count,x;
			eq := EquationLetterRep(eq);
			gens := [];
			imgs := [];
			count := 1;
			for x in N!.word do
				if x in F and not Abs(x) in gens then
					Add(gens,Abs(x));
					Add(imgs,F.(count));
				fi;
			od;
			return EquationHomomorphism(EqG,gens,imgs);
		end;
		N := NormalForm(x);
		H :=NormalVars(N[1]);
		return [N1^H,H*N[2]];
	end);





InstallMethod(EquationNormalFormInverseHom, "for a Grpword",
	[IsEquation],
	function(x)
		local NormalUnknowns,NormalForm2,N2,N;
		NormalForm2:= function(xx)
			local case10,case11a,case11b,case3,toInvert,vfind,i,j,t,x,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3,first,Hom,Hom2,y,N;
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
