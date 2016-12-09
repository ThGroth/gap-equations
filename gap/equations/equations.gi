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
		local embeddings,FP,i,names,nameLen,construct_map;
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
		#Thanks to Alexander Konovalov,
		#See http://math.stackexchange.com/questions/2048106
		construct_map := i -> (w-> AssocWordByLetterRep(FamilyObj(Representative(FP)),
    					List(LetterRepAssocWord(w),k->SignInt(k)*(Length(L)*(AbsInt(k)-1)+i)) ));
    	for i in [1..Length(L)] do
    			Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				FP,
    				construct_map(i) ));
       	od;
        SetFreeProductInfo( FP, 
        rec( groups := L,
             embeddings := embeddings ) );
    	return FP;   
	end);
#################################################################################
####                                                                         ####
####	         Free Products of free group and other groups     			 ####
####                                                                         ####
#################################################################################

InstallMethod(FreeProductOp, "For FreeGroups and arbitrarygroups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,FP,i,names,nameLen,construct_map;
		if ForAll(L,IsFreeGroup) then
			TryNextMethod();
		fi;
		return(EquationGroup(G,L[1]));
		 
	end);


####
#TODO Continue here!












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
	[IsList,IsEquationGroup,IsPerm,IsBool],
	function(words,DEqG,perm,reduced)
		local Ob;
		if not IsDecompositionEquationGroup(DEqG)then
			TryNextMethod();
		fi;
		Ob :=  Objectify(NewType(ElementsFamily(FamilyObj(DEqG)), IsEquation and IsDecomposedEquationRep),
    				rec(words := words,
       					group := DEqG!.group,
       					free := DEqG!.free,
       					eqG := DEqG,
       					activity := perm));
		if reduced then
			return EquationReducedForm(Ob);
		else
			return Ob;
		fi;
	end);
InstallOtherMethod(Equation, "(Equation) for a list of lists, a DecompositionEquationGroup and a permutation",
	[IsList,IsEquationGroup,IsPerm],
	function(words,DEqG,perm)
		return Equation(words,DEqG,perm,true);
	end);

InstallMethod(EquationReducedForm, "for an Equation in Equation representation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		local Eq;
		Eq := Equation(List(EquationComponents(x),eq->eq!.word),x!.eqG,x!.activity,false);
		SetIsReducedEquation(Eq,true);
		return 	Eq;
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
		if not ForAll(L,elm->elm in eq!.group) then
			Error("All images need to be in the group of constants.");
		fi;
		var := EquationVariables(eq);
		if not Length(var)=Length(L) then
			Error("There must be as many images as variables.");
		fi;
		return EquationHomomorphism(eq!.eqG,eq!.group,
					GroupHomomorphismByImages(Group(var),eq!.group,L),
					IdentityMapping(eq!.group));
	end);

#Example
G := GrigorchukGroup;
BS := BranchStructure(G);
pi := BS.quo;
AssignGeneratorVariables(G);
F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);
SetName(F,"FX");
EqG := EquationGroup(G,F);
Eq := Equation([Comm(F.1,F.2),(a*b)^2],EqG);
id := IdentityMapping(G);

ev := EquationEvaluation(Eq,[a,b*a]);
Image(ev,Eq);

h1 := EquationHomomorphism(EqG,[F.1,F.3],[F.2,F.5]);
h2 := EquationHomomorphism(EqG,[F.3],[F.7]);



DEqG := DecompositionEquationGroup(EqG);
constr := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),[(),()]);
DEq:=DecompositionEquation(Eq,constr,DEqG);


