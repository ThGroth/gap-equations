InstallOtherMethod( FreeProductElm, "For an EquationGroup and a list",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		return FreeProductElm(eqG,elms,List(elms,function(e)
													if e in eqG!.const then
														return 1; 
													fi; return 2;
												 end) );
	end);

InstallOtherMethod( \*,   "for FreeProductElms and GroupElements",
    [ IsFreeProductElm and IsFreeProductElmRep, IsMultiplicativeElementWithInverse ],
    function( x, y )
    	local pos;
    	pos := PositionProperty(x!.group!.groups,G->y in G);
    	if pos = fail then
    		TryNextMethod();
    	fi;
    	return x*y^Embedding(x!.group,pos);
    end );

InstallOtherMethod( \*,   "for FreeProductElms and GroupElements",
    [ IsMultiplicativeElementWithInverse , IsFreeProductElm and IsFreeProductElmRep ],
    function( y, x )
    	local pos;
    	pos := PositionProperty(x!.group!.groups,G->y in G);
    	if pos = fail then
    		TryNextMethod();
    	fi;
    	return y^Embedding(x!.group,pos)*x;
    end );



InstallMethod(EquationNormalForm, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	function(x)
		local G,F,EqG,NormalForm,N,H,NormalVars;
		if not IsQuadraticEquation(x) then
			TryNextMethod();
		fi;
		G := x!.const;
		F := x!.free;
		EqG := x!.group;
		
		#Recursive worker function
		NormalForm:= function(eq)
			local case10,case11a,case11b,case3,i,j,t,x,y,Hom,N,
				  asInt,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3;
			Info(InfoEQFP,3,"Call of NormalForm with",eq);

				case10 := function(w1,v,w2,x)
				# eq = w₁·x⁻·v·x·w₂
				# w₁,w₂ Equations v∈G,x∈F 
				local N,Hom,c;
				N := NormalForm(w1*w2);
				Hom := EquationHomomorphism(EqG,[x],[x*w2^-1]);
				if Length(N[1])=0 then
					return [FreeProductElm(EqG,[x^-1,v,x]),Hom];
				fi;
				#Does N end with a constant?
				c:= N[1]!.word[Length(N[1])];
				if c in F then
					return [N[1]*FreeProductElm(EqG,[x^-1,v,x]),N[2]*Hom];
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
				N[1]:=FreeProductElmLetterRep(N[1]);
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
			eq := Equation(FreeProductElmLetterRep(eq));
			
			if Length(eq)<3 then
				return [eq,EquationHomomorphism(EqG,[],[])];
			fi;
				
			if IsOrientedEquation(eq) then
				#Find x s.t. w=w₁ x⁻¹ v x w₂ with |v| minimal
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
				w1 := FreeProductElmLetterRep(eq{[1..i-1]});
				v := FreeProductElmLetterRep(eq{[i+1..j-1]});
				w2 := FreeProductElmLetterRep(eq{[i+j..Length(eq)]});
				
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
						N := case11a(w1*w21,v2*v1,x,w22,Abs(y));
						Hom := EquationHomomorphism(EqG,[x],[v2^-1*x*w21^-1])*Hom;
						return [N[1],N[2]*Hom];
					fi;
				fi; 
			else #so not oriented
				#Find x s.t. w=w₁ x v x w₂ with |v| minimal
				t := [];
				Perform(EquationVariables(eq),function(v) t[LetterRepAssocWord(v)[1]]:=1; end);
				for i in [1..Length(eq)] do
					x := eq!.word[i];
					if x in F then
						asInt := LetterRepAssocWord(x)[1];
						t[AbsInt(asInt)]:=SignInt(t[AbsInt(asInt)])*SignInt(asInt)*(i+1-AbsInt(t[AbsInt(asInt)])); 
					fi;
				od;
				x := AssocWordByLetterRep(FamilyObj(Representative(F)),
							[PositionProperty(t,i->i=Minimum(Filtered(t,IsPosInt)))]);

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
			eq := FreeProductElmLetterRep(eq);
			gens := [];
			imgs := [];
			count := 1;
			for x in eq!.word do
				if x in F and not Abs(x) in gens then
					Add(gens,Abs(x));
					Add(imgs,F.(count));
				fi;
				count := count+1;
			od;
			return EquationHomomorphism(EqG,gens,imgs);
		end;
		N := NormalForm(x);
		H :=NormalVars(N[1]);
		return rec(nf := Equation(N[1]^H), hom := H*N[2]);
	end);


testfunc := function()
	local elms,e,L,xn,x,F,a,b,c,d,f1,f2,f3,G2,others,count;
	G := GrigorchukGroup;
	a := G.1;
	b := G.2;
	c := G.3;
	d := G.4;
	G2 := FreeGroup(5);
	f1 := G2.1;
	f2 := G2.2;
	f3 := G2.3;
	F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6","x7","x8","x9"]);
	SetName(F,"FX");
	SetName(G2,"F5");
	elms := [[1,1],[-1,-1],[1,1,2,2],[-2,-1,2,1],[-1,-2,1,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
	elms:=List(elms,e->List(e,function(i)
						 if IsInt(i) then
						 	return AssocWordByLetterRep(FamilyObj(Representative(F)),[i]);
						 fi; 
						 return i; end));
	
	others := [Equation(EquationGroup(G2,F),[F.9^-1,f1,F.8^-1,f2,F.9,F.8,f3])];
	L := [];
	EqG := EquationGroup(G,F);
	count := 1;
	for e in elms do
		Print("Doing ",e,": ",count," \r");
		x := Equation(EqG,e);
		xn := EquationNormalForm(x);
		if x^xn.hom <> xn.nf then
			Add(L,e);
		fi;
		count := count+1;
	od;
	for e in others do
		xn := EquationNormalForm(e);
		if e^xn.hom <> xn.nf then
			Add(L,e);
		fi;
	od;
	Print("Errors happened at L: ");
	Display(L);
	Print("\n");
end;





#####
#
#
#
# TODO Continue Here.
#
#
#
#



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
	G2 := FreeGroup(5);
	f1 := G2.1;
	f2 := G2.2;
	f3 := G2.3;
	F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6","x7","x8","x9"]);
	SetName(F,"FX");
	elms := [[1,1],[-1,-1],[1,1,2,2],[-2,-1,2,1],[-1,-2,1,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
	elms:=List(elms,List(e,function(i)
						 if IsInt(i) then
						 	return AssocWordByLetterRep(FamilyObj(Representative(F)),i);
						 fi; 
						 return i));
	
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
