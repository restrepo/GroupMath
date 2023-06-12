(* ::Package:: *)

(* ::Input::Initialization:: *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

NullMatrix[n_,m_]:=ConstantArray[0,{n,m}];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

SimplifySA[array_]:=SparseArray[Simplify[array//ArrayRules],Dimensions[array]];
FullSimplifySA[array_]:=SparseArray[FullSimplify[array//ArrayRules],Dimensions[array]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

NullMatrix[n_,m_]:=Array[0&,{n,m}];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Auxiliar method needed to construct the representation matrices *)
CholeskyTypeDecomposition[matrix_]:=Module[{n,nullRow,matD,matL,result},
n=Length[matrix];
matD=Array[0&,{n,n}];
matL=IdentityMatrix[n];

Do[
Do[
If[matD[[j,j]]!=0,
matL[[i,j]]=Simplify[1/matD[[j,j]](matrix[[i,j]]-Sum[matL[[i,k]]Conjugate[matL[[j,k]]]matD[[k,k]],{k,j-1}])];
,matL[[i,j]]=0];
,{j,i-1}];

matD[[i,i]]=Simplify[matrix[[i,i]]-Sum[matL[[i,k]]Conjugate[matL[[i,k]]]matD[[k,k]],{k,i-1}]];

,{i,Length[matrix]}];

(*Make the resulting matrix as small as possible by eliminating null columns*)
result=Transpose[matL.Sqrt[matD]];
nullRow=Array[0&,n];
result=Transpose[DeleteCases[result,nullRow]];

Return[result];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Auxiliar method (used for building the representation matrices) *)
NullSpace2[matrixIn_,dt_]:=Module[{matrix,preferredOrder,aux1,aux2,aux3,res,n,n2,v},
Off[Power::"indet"];

(* Remove Columns appearing in rows with a single entry *)
(*
aux1=Sort/@Sort[Gather[(matrixIn//ArrayRules)[[1;;-2]],#1[[1,1]]==#2[[1,1]]&]];
aux2=Complement[Range[Length[matrixIn[[1]]]],Cases[aux1,x_/;Length[x]==1\[RuleDelayed]x[[1,1,2]]]];
matrix=matrixIn[[All,aux2]];
*)

(* Organize the rows so that the easiest ones are solved first *)
aux1=Sort/@Sort[Gather[(matrixIn//ArrayRules)[[1;;-2]],#1[[1,1]]==#2[[1,1]]&]];
If[Length[aux1]==0,Return[IdentityMatrix[Length[matrixIn[[1]]]]]]; (* If the matrix is null, end this right here, by returning the identity matrix *)
preferredOrder=Flatten[Table[Cases[aux1,x_/;Length[x]==i:>x[[1,1,1]],{1}],{i,1,Max[Length/@aux1]}]];
matrix=matrixIn[[preferredOrder]];

n=Length[matrix];
n2=Length[matrix[[1]]];

aux1=Table[v[i],{i,n2}];

Do[
aux2=Solve[matrix[[i;;Min[i+dt-1,n]]].aux1==0][[1]];
aux1=Expand[aux1 /.aux2];
,{i,1,n,dt}];

aux3=Tally[Cases[aux1,v[i_]:>i,Infinity]][[All,1]];
res={};
Do[
res=Append[res,aux1/. v[x_]:>If[x!=aux3[[i]],0,1]];
,{i,Length[aux3]}];
Return[res];
];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* auxiliar function: given a list of n-dimensional tensors, this function will return an n-dimensional tensor where the input tensors appear as diagonal blocks *)
BlockDiagonalNTensor[blocks_]:=Module[{dims,result,i,pos,aux},
dims=Dimensions/@blocks;
result=SparseArray[{},Plus@@dims];
pos=0dims[[1]]+1;

Do[
aux=Table[pos[[j]];;(pos+dims[[i]])[[j]]-1,{j,Length[dims[[1]]]}]/.{x___}:>x;
result[[aux]]=blocks[[i]];
pos+=dims[[i]];
,{i,Length[blocks]}];

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* given an input of numbers, it gives a list {starts,ends} from accumulating numbers *)
StartsEnds[numbers_]:=Module[{ends,starts},
ends=Accumulate[numbers];
starts=ends-numbers+1;
Return[{starts,ends}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* If x is a nested list then x=InverseFlatten[Flatten[x],Dimensions[x]] *)
InverseFlatten[flattenedList_,dims_]:=Fold[Partition[#,#2]&,flattenedList,Most[Reverse[dims]]];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Unflatten is more generic than InverseFlatten, as the original tensor does not need to be rectangular. However, a list with the original structure must be provided *)
Unflatten[flatList_,originalList_]:=Module[{i=1},Function[Null,flatList[[i++]],{Listable}][originalList]]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

GatherWeights[listW_]:=Module[{aux},
aux=Flatten[listW,1];
aux=Gather[aux,#1[[1]]==#2[[1]]&];

aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;
aux=DeleteCases[aux,x_/;x[[2]]==0];

Return[aux];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

GatherWeights[listW_,listMult_]:=Module[{aux},
aux=Table[{#[[1]],listMult[[i]]#[[2]]}&/@listW[[i]],{i,Length[listW]}];
aux=Flatten[aux,1];
aux=Gather[aux,#1[[1]]==#2[[1]]&];

aux={#[[1,1]],Plus@@#[[1;;-1,2]]}&/@aux;
aux=DeleteCases[aux,x_/;x[[2]]==0];
Return[aux];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* TuplesWithMultiplicity, TallyWithMultiplicity, PermutationSymmetryOfTensorProductPartsAuxiliar, PermutationSymmetryOfTensorProductParts, PermutationSymmetryOfInvariants *)
(* These are functions related to the symmetry of invariants  which are more ready to use when building a Lagrangian: they deal with products of different representations and the group can be semisimple *)

(* E.g.: TuplesWithMultiplicity[{{{X1,1},{X2,2}},{{Y1,10}},{{Z1,\[Pi]},{Z2,-\[Pi]}}}] = {{{X1,Y1,Z1},10 \[Pi]},{{X1,Y1,Z2},-10 \[Pi]},{{X2,Y1,Z1},20 \[Pi]},{{X2,Y1,Z2},-20 \[Pi]}} *)
TuplesWithMultiplicity[listOflists_]:=Module[{aux1,aux2,result},
aux1=Tuples[listOflists];
aux2=Times@@@aux1[[All,All,2]];
aux1=aux1[[All,All,1]];
result=MapThread[List,{aux1,aux2}];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* E.g.: TallyWithMultiplicity[{{X,1},{X,10},{Y,2},{Z,1},{X,2}}] = {{X,13},{Y,2},{Z,1}} *)
TallyWithMultiplicity[listOflists_]:=Module[{aux1,aux2,result},
aux1=Gather[listOflists,#1[[1]]==#2[[1]]&];
aux2=Plus@@@(aux1[[All,All,2]]);
aux1=aux1[[All,1,1]];
result=MapThread[List,{aux1,aux2}];
Return[result];
]


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* TO THINK: Maybe transpositions of r1 and r2 should be made in the line "bigMatrix=Join[bigMatrix,SparseArray[KroneckerProduct[r1[[i]],Id2]+KroneckerProduct[Id1,r2[[i]]]]]"? *)
InvariantsSuperFreeFormMod[repMat1_,repMat2_,conj_Symbol:False]:=Module[{r1,r2,dimR1,dimR2,Id1,Id2,bigMatrix,result,aux1,delColumns,usefulLines,usefulColumns,chunkSize, nChunks,limits},

Off[Solve::"svars"];

r1=SparseArray[#,Dimensions[#]]&/@repMat1;
r2=SparseArray[#,Dimensions[#]]&/@repMat2;
dimR1=Length[repMat1[[1]]];
dimR2=Length[repMat2[[1]]];
Id1=SparseArray[IdentityMatrix[dimR1]];
Id2=SparseArray[IdentityMatrix[dimR2]];

If[conj,
Do[
r2[[i]]=-Transpose[r2[[i]]];
,{i,Length[r2]}];];

bigMatrix={};

Do[
bigMatrix=Join[bigMatrix,SparseArray[KroneckerProduct[r1[[i]],Id2]+KroneckerProduct[Id1,r2[[i]]]]];
,{i,Length[r1]}];

(*Simplify things by deleting columns corresponding to single entrie in rows. Delete also null rows. *)

chunkSize=50000; (*With this value, this method should not use more than about 100 MB of memory *)
nChunks=Ceiling[Length[bigMatrix]/chunkSize];
limits=Table[{(i-1) chunkSize+1,i chunkSize},{i,nChunks}];
limits[[-1,2]]=Length[bigMatrix];

delColumns={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];

aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];
,{i,nChunks}];

delColumns=DeleteDuplicates[delColumns];
usefulColumns=Complement[Range[Length[bigMatrix[[1]]]],delColumns];
If[usefulColumns=={},Return[{}]];

bigMatrix=bigMatrix[[1;;-1,usefulColumns]];

delColumns={};
usefulLines={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];

aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
usefulLines=Join[usefulLines,(i-1) chunkSize+Tally[Cases[aux1,x_/;x[[2]]>1:>x[[1,1]]]][[All,1]]];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];
,{i,nChunks}];

delColumns=Tally[delColumns][[All,1]];
usefulLines=Tally[usefulLines][[All,1]];
aux1=Complement[Range[Length[bigMatrix[[1]]]],delColumns];
If[aux1=={},Return[{}]];

usefulColumns=usefulColumns[[aux1]];

If[usefulLines=={},bigMatrix={ConstantArray[0,Length[usefulColumns]]},bigMatrix=bigMatrix[[usefulLines,aux1]]];


result=NullSpace2[SimplifySA[bigMatrix],100];
result=(Flatten[Array[a[#1]b[#2]&,{dimR1,dimR2}]][[usefulColumns]]. #&)/@ result;

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* For some reason, it is very important memory-wise that the second dimension of a sparse array is the largest one. So this function is the same as NullSpace2, but the input matrix is transposed *)
NullSpace2T[matrixInT_,dt_]:=Module[{matrix,preferredOrder,aux1,aux2,aux3,res,n,n2,v},
Off[Power::"indet"];

(* Remove Columns appearing in rows with a single entry *)
(*
aux1=Sort/@Sort[Gather[(matrixIn//ArrayRules)[[1;;-2]],#1[[1,1]]==#2[[1,1]]&]];
aux2=Complement[Range[Length[matrixIn[[1]]]],Cases[aux1,x_/;Length[x]==1\[RuleDelayed]x[[1,1,2]]]];
matrix=matrixIn[[All,aux2]];
*)

(* Organize the rows so that the easiest ones are solved first *)
aux1=Sort/@Sort[Gather[(matrixInT//ArrayRules)[[1;;-2]],#1[[1,2]]==#2[[1,2]]&]];
If[Length[aux1]==0,Return[IdentityMatrix[Length[matrixInT[[All,1]]]]]]; (* If the matrix is null, end this right here, by returning the identity matrix *)
preferredOrder=Flatten[Table[Cases[aux1,x_/;Length[x]==i:>x[[1,1,2]],{1}],{i,1,Max[Length/@aux1]}]];
matrix=matrixInT[[All,preferredOrder]];

n=Length[matrix[[1]]];
n2=Length[matrix];

aux1=Table[v[i],{i,n2}];

Do[
aux2=Solve[Transpose[matrix[[All,i;;Min[i+dt-1,n]]]].aux1==0][[1]];
aux1=Expand[aux1 /.aux2];
,{i,1,n,dt}];

aux3=Tally[Cases[aux1,v[i_]:>i,Infinity]][[All,1]];
res={};
Do[
res=Append[res,aux1/. v[x_]:>If[x!=aux3[[i]],0,1]];
,{i,Length[aux3]}];
Return[res];
];
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Matrix contracted with index n of a tensor - auxiliar function to SMethod *)
DotN[mat_,tensor_,n_]:=Module[{perm,permI,result},

perm=Insert[RotateLeft[1+Range[Length[Dimensions[tensor]]-1]],1,n];
permI=Flatten[Table[Position[perm,i],{i,Length[perm]}]];
result=Transpose[mat.Transpose[tensor,perm],permI];
Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvertOrdering[o_]:=Table[Position[o,i][[1,1]],{i,Length[o]}];

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(*Decomposes a symmetric matrix A into L.L^T. L is the output. L is obtained through the Takagi decomposition of a symmetric matrix *)
TakagiDecomposition[m_]:=Module[{n,matrix,matrix2,eigenS,eigenVal,eigenVec, \[Mu],v,aux,V,VCorrected,VTotal,diagList},
n=Length[m];
If[n==1,Return[Sqrt[m]]];
matrix=SparseArray[m];
VTotal=SparseArray[IdentityMatrix[n]];
diagList={};
eigenS=Eigensystem[Normal[matrix.Conjugate[matrix]]];
eigenVal=eigenS[[1]];
eigenVec=SparseArray[Transpose[eigenS[[2]]]];


Do[
matrix2=matrix.Conjugate[matrix];
\[Mu]=Sqrt[eigenVal[[i]]];
v=Table[{eigenVec[[j,i]]},{j,i,n}];

aux=MatrixRank[{Transpose[v][[1]],Transpose[matrix.Conjugate[v]][[1]]}];

If[aux==2,v=matrix.Conjugate[v]+\[Mu] v;];
v=Flatten[v];

V=SparseArray[Transpose[OrthogonalizeFast[v]]]; 
VCorrected=SparseArray[PadLeft[V,{n,n}]+DiagonalMatrix[Join[ConstantArray[1,i-1],ConstantArray[0,n-i+1]]]];
eigenVec=ConjugateTranspose[VCorrected].eigenVec;
VTotal=SparseArray[VTotal.VCorrected];
aux=(ConjugateTranspose[V].matrix.Conjugate[V]);
diagList=Append[diagList,aux[[1,1]]];
matrix=aux[[2;;-1,2;;-1]];

,{i,n-1}];
diagList=Append[diagList,aux[[2,2]]];

Return[Simplify[VTotal.DiagonalMatrix[Sqrt[diagList]]]];
]

OrthogonalizeFast[v_]:=Module[{n,pos1,pos2,aux,result},
n=Length[v];
result=Array[0&,{n,n}];
pos1=Flatten[Position[v,0]];
pos2=Complement[Table[i,{i,n}],pos1];
If[pos2!={},
aux=Drop[Orthogonalize[Prepend[IdentityMatrix[Length[pos2]],v[[pos2]]]],-1];
result[[1;;Length[pos2],pos2]]=aux;
];
If[pos1!={},
result[[Length[pos2]+1;;n,pos1]]=IdentityMatrix[Length[pos1]];
];

Return[result];
];



(* ::Input::Initialization:: *)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* Auxiliar method. Input: list o matrices. Output: big matrix with the given matrices as diagonal blocks *)
(* Taken from SSB module *)
(* TODO: get rid of this function; replace with BlockDiagonalNTensor *)
BlockDiagonalMatrix[blocks_]:=Module[{dims,result,i,pos},
dims=Dimensions/@blocks;
result=ConstantArray[0,Plus@@dims];
pos={1,1};
Do[
result[[pos[[1]];;(pos+dims[[i]])[[1]]-1,pos[[2]];;(pos+dims[[i]])[[2]]-1]]=blocks[[i]];
pos+=dims[[i]];
,{i,Length[blocks]}];

Return[result];
]

(* Auxiliar function to print memory and time information. It is used by SubgroupEmbeddingCoefficients *)
ReportData[i_,dt_]:=Print[Style["["<>ToString[i]<>"] ",{Bold,Darker[Red]}],Style["Memory in use: ",Bold],MemoryInUse[]," B; ",Style["Time used so far: ",Bold],dt," s"];


(* ::Input::Initialization:: *)
(* This method efficiently contracts indices of tensors. list=tensor to contract; positions=list with pairs {index1,index2} to contract;
E.g. : Aijk Bkij . A.B contracts the k index. So ListContract[A.B,{{1,3},{2,4}}] contracts the remaining 4 indices: the 1st with the 3rd and the 2nd with the 4th. *)

ListContract[list_, positions_] := Module[{n, n2, aux1, aux2, aux3, aux1Inv, i},
  n = Length[Dimensions[list]];
  n2 = Length[positions];
  aux1 = Flatten[positions];
  aux2 = Table[i, {i, n}];
  aux1 = Join[aux1, Complement[aux2, aux1]];
  
  (* Inverting the permutation aux1: if n is in posicao i, the inverse permutation has i in position n *)
  aux1Inv = 0 aux1;
  Do[
   aux1Inv[[aux1[[i]]]] = i;
   , {i, Length[aux1]}];
  (* /Inverting the permutation aux1: if n is in posicao i, the inverse permutation has i in position n *)
  
  aux3 = Transpose[list, aux1Inv];
  
  Do[
   aux3 = Tr[aux3, Plus, 2];
   , {i, n2}];
  
  Return[aux3];
  ]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsSuperFreeForm[repMat1_]:=Module[{r1,dimR1,bigMatrix,result},

Off[Solve::"svars"];

r1=repMat1;
dimR1=Length[repMat1[[1]]];


bigMatrix={};
Do[
bigMatrix=Join[bigMatrix,repMat1[[i]]];

,{i,Length[r1]}];
bigMatrix=SparseArray[Simplify[ArrayRules[bigMatrix]],{Length[bigMatrix],Length[bigMatrix[[1]]]}];

result=NullSpace2[bigMatrix,100];

result=(Array[a[#1]&,{dimR1}]. #&)/@ result;

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsSuperFreeForm[repMat1_,repMat2_,conj_Symbol:False]:=Module[{r1,r2,dimR1,dimR2,Id1,Id2,bigMatrix,result,aux1,delColumns,usefulLines,usefulColumns,chunkSize, nChunks,limits},

Off[Solve::"svars"];

r1=SparseArray[#,Dimensions[#]]&/@repMat1;
r2=SparseArray[#,Dimensions[#]]&/@repMat2;
dimR1=Length[repMat1[[1]]];
dimR2=Length[repMat2[[1]]];
Id1=SparseArray[IdentityMatrix[dimR1]];
Id2=SparseArray[IdentityMatrix[dimR2]];

If[conj,
Do[
r2[[i]]=-Conjugate[r2[[i]]];
,{i,Length[r2]}];];

bigMatrix={};

Do[
bigMatrix=Join[bigMatrix,SparseArray[KroneckerProduct[r1[[i]],Id2]+KroneckerProduct[Id1,r2[[i]]]]];
,{i,Length[r1]}];

(*Simplify things by deleting columns corresponding to single entrie in rows. Delete also null rows. *)

chunkSize=50000; (*With this value, this method should not use more than about 100 MB of memory *)
nChunks=Ceiling[Length[bigMatrix]/chunkSize];
limits=Table[{(i-1) chunkSize+1,i chunkSize},{i,nChunks}];
limits[[-1,2]]=Length[bigMatrix];

delColumns={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];

aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];
,{i,nChunks}];

delColumns=DeleteDuplicates[delColumns];
usefulColumns=Complement[Range[Length[bigMatrix[[1]]]],delColumns];
If[usefulColumns=={},Return[{}]];

bigMatrix=bigMatrix[[1;;-1,usefulColumns]];

delColumns={};
usefulLines={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];

aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
usefulLines=Join[usefulLines,(i-1) chunkSize+Tally[Cases[aux1,x_/;x[[2]]>1:>x[[1,1]]]][[All,1]]];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];
,{i,nChunks}];

delColumns=Tally[delColumns][[All,1]];
usefulLines=Tally[usefulLines][[All,1]];
aux1=Complement[Range[Length[bigMatrix[[1]]]],delColumns];
If[aux1=={},Return[{}]];

usefulColumns=usefulColumns[[aux1]];

If[usefulLines=={},bigMatrix={ConstantArray[0,Length[usefulColumns]]},bigMatrix=bigMatrix[[usefulLines,aux1]]];


result=NullSpace2[SimplifySA[bigMatrix],100];
result=(Flatten[Array[a[#1]b[#2]&,{dimR1,dimR2}]][[usefulColumns]]. #&)/@ result;

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

InvariantsSuperFreeForm[repMat1_,repMat2_,repMat3_,conj_Symbol:False]:=Module[{r1,r2,r3,dimR1,dimR2,dimR3,Id1,Id2,Id3,bigMatrix,result,aux1,delColumns,usefulLines,usefulColumns,chunkSize, nChunks,limits},

Off[Solve::"svars"];

r1=SparseArray[#,Dimensions[#]]&/@repMat1;
r2=SparseArray[#,Dimensions[#]]&/@repMat2;
r3=SparseArray[#,Dimensions[#]]&/@repMat3;
dimR1=Length[repMat1[[1]]];
dimR2=Length[repMat2[[1]]];
dimR3=Length[repMat3[[1]]];
Id1=SparseArray[IdentityMatrix[dimR1]];
Id2=SparseArray[IdentityMatrix[dimR2]];
Id3=SparseArray[IdentityMatrix[dimR3]];

If[conj,
Do[
r3[[i]]=-Conjugate[r3[[i]]];
,{i,Length[r3]}];];

bigMatrix={};

Do[
bigMatrix=Join[bigMatrix,SparseArray[KroneckerProduct[r1[[i]],Id2,Id3]+KroneckerProduct[Id1,r2[[i]],Id3]+KroneckerProduct[Id1,Id2,r3[[i]]]]];
,{i,Length[r1]}];

(*Simplify things by dele
ting columns corresponding to single entrie in rows. Delete also null rows. *)

chunkSize=50000; (*With this value, this method should not use more than about 100 MB of memory *)
nChunks=Ceiling[Length[bigMatrix]/chunkSize];
limits=Table[{(i-1) chunkSize+1,i chunkSize},{i,nChunks}];
limits[[-1,2]]=Length[bigMatrix];

delColumns={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];
aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];

,{i,nChunks}];

delColumns=DeleteDuplicates[delColumns]; If[Length[delColumns]==Length[bigMatrix[[1]]],Return[{}]];

usefulColumns=Complement[Range[Length[bigMatrix[[1]]]],delColumns];

If[usefulColumns=={},Return[{}]];
bigMatrix=bigMatrix[[1;;-1,usefulColumns]];


delColumns={};
usefulLines={};

Do[
aux1=Drop[ArrayRules[bigMatrix[[limits[[i,1]];;limits[[i,2]]]]],-1];

aux1=DeleteCases[Simplify[aux1],x_/;x[[2]]==0];

aux1={#[[1,1]],#[[2]]}&/@Tally[aux1,#1[[1,1]]==#2[[1,1]]&];
usefulLines=Join[usefulLines,(i-1) chunkSize+DeleteDuplicates[Cases[aux1,x_/;x[[2]]>1:>x[[1,1]]]]];
delColumns=Join[delColumns,Cases[aux1,x_/;x[[2]]==1:>x[[1,2]]]];
,{i,nChunks}];

delColumns=DeleteDuplicates[delColumns];
usefulLines=DeleteDuplicates[usefulLines];
aux1=Complement[Range[Length[bigMatrix[[1]]]],delColumns];
bigMatrix=bigMatrix[[usefulLines,aux1]];
usefulColumns=usefulColumns[[aux1]];

If[usefulLines=={},bigMatrix={ConstantArray[0,Length[usefulColumns]]}];

result=NullSpace2[bigMatrix,100];

result=(Flatten[Array[a[#1]b[#2]c[#3]&,{dimR1,dimR2,dimR3}]][[usefulColumns]]. #&)/@ result;

Return[result];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Diagonalizes a set of commuting matrices. The output is {{diagMat1,diagMat2,...},V} so that the original matrices are MatI=V.diagMatI.Inverse[V]*)
Diagonalize[mats_]:=Module[{n,n2,commute,diagMats,restMats,superD,aux1,aux2,aux3,aux4,rotation},
n=Length[mats];
n2=Length[mats[[1]]];
commute=True;
superD=Table[{},{i,n}];
diagMats={};
restMats={};
rotation=IdentityMatrix[n2] //SparseArray;

(* Test if the all commute *)
Do[
If[!(Simplify[mats[[i]].mats[[j]]-mats[[j]].mats[[i]]]==0mats[[i]]),commute=False];
,{i,n},{j,n}];


If[commute,

 restMats=mats//SparseArray; 

(* Diagonalize the rest of the matrices in the degenerate space of the diagonal matrices *)
While[restMats!={},

If[Length[diagMats]>0,
aux1=#[[1]]&/@Tally[superD];
aux4=ConstantArray[0,{n2,n2}] //SparseArray;

Do[
aux2=Position[superD,aux1[[i]]] //Flatten;
 aux3=restMats[[1,aux2,aux2]];
aux4[[aux2,aux2]]=Eigensystem[aux3][[2]];
,{i,Length[aux1]}];
,
aux4=Eigensystem[restMats[[1]]][[2]];
];

aux4=SimplifySA[aux4];
rotation=SimplifySA[rotation.Transpose[aux4]];

Do[
restMats[[i]]=SimplifySA[Inverse[Transpose[aux4]].restMats[[i]].Transpose[aux4]];
,{i,Length[restMats]}];

diagMats=Append[diagMats,SparseArray[restMats[[1]],{n2,n2}]];
superD=Transpose[Append[Transpose[superD],Diagonal[restMats[[1]]]]]//Normal;
restMats=restMats[[2;;-1]];
]

,
Print["Not all pairs of matrices commute"];
];

Return[{diagMats,rotation}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

(* Same as diagonalize but the diagonalizing matrix is made to be unitary. Also, no check is made to see if the matrices commute (it is assumed that they do) *)

(* Note that DiagonalizeOrthogonal calls DiagonalizeOrthogonalMainFunction, which is the true analogue of Diagonalize. The wrapper function (DiagonalizeOrthogonal) tries to break down the problem in blocks before feeding the data to DiagonalizeOrthogonalMainFunction *)
DiagonalizeOrthogonal[input_]:=Module[{n,aux,aux2,rowsMixedWithColumnI,columnsMixedWithRowI,blocks,newBlock,rcsLeft,continue,diagResults,result},
n=Length[input[[1]]];
aux=ArrayRules[input][[All,1,2;;3]];
rowsMixedWithColumnI=Table[Tally[Cases[aux,x_/;x[[2]]==i:>x[[1]],{1}]][[All,1]],{i,n}];
columnsMixedWithRowI=Table[Tally[Cases[aux,x_/;x[[1]]==i:>x[[2]],{1}]][[All,1]],{i,n}];
blocks={};
newBlock={};
rcsLeft=Flatten[rowsMixedWithColumnI];

While[rcsLeft=!={},
newBlock={rcsLeft[[1]]};
continue=True;
While[continue,
aux2=Tally[Join[Flatten[rowsMixedWithColumnI[[newBlock]]],Flatten[columnsMixedWithRowI[[newBlock]]]]][[All,1]];
If[Length[aux2]==Length[newBlock],continue=False,newBlock=aux2];
];
AppendTo[blocks,newBlock];
rcsLeft=Complement[rcsLeft,newBlock];
];

(*Check if there is no rows with 0's everywhere*)If[Length[DeleteDuplicates[Flatten[rowsMixedWithColumnI]]]<n,AppendTo[blocks,Complement[Range[n],Flatten[rowsMixedWithColumnI]]]];

diagResults=DiagonalizeOrthogonalMainFunction[input[[All,#,#]]]&/@blocks;

result={ConstantArray[SparseArray[{},{n,n}],Length[input]],SparseArray[{},{n,n}]};
Do[
result[[1,All,blocks[[i]],blocks[[i]]]]=diagResults[[i,1]];
result[[2,blocks[[i]],blocks[[i]]]]=diagResults[[i,2]];
,{i,Length[diagResults]}];

result={SparseArray[#,{n,n}]&/@result[[1]],SparseArray[result[[2]],{n,n}]};

Return[result];
]


DiagonalizeOrthogonalMainFunction[mats_]:=Module[{n,n2,diagMats,restMats,superD,aux1,aux2,aux3,aux4,rotation},
n=Length[mats];
n2=Length[mats[[1]]];
superD=Table[{},{i,n}];
diagMats={};
restMats={};
rotation=IdentityMatrix[n2] //SparseArray;

restMats=mats//SparseArray; 
 
(* Diagonalize the matrices in the degenerate space of the (already) diagonal matrices *)
While[restMats!={},

If[Length[diagMats]>0,
aux1=#[[1]]&/@Tally[superD];
aux4=ConstantArray[0,{n2,n2}] //SparseArray;

Do[
aux2=Position[superD,aux1[[i]]] //Flatten;
 aux3=restMats[[1,aux2,aux2]];
aux4[[aux2,aux2]]=SparseArray[Orthogonalize[SimplifySA[Eigensystem[aux3][[2]]],FullSimplify[Conjugate[#1].#2]&]];
,{i,Length[aux1]}];
,
aux4=Eigensystem[restMats[[1]]][[2]];
aux4=Orthogonalize[SimplifySA[aux4],FullSimplify[Conjugate[#1].#2]&];
];

rotation=SimplifySA[rotation.Transpose[aux4]];

Do[
restMats[[i]]=FullSimplifySA[Conjugate[aux4].restMats[[i]].Transpose[aux4]];
,{i,Length[restMats]}];

diagMats=Append[diagMats,restMats[[1]]];
superD=Transpose[Append[Transpose[superD],Diagonal[restMats[[1]]]]]//Normal;
restMats=restMats[[2;;-1]]; (* drop the fist matrix *)
];

Return[{diagMats,rotation}];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

IsDiagonizable[m_]:=Module[{dM,vM},
{dM,vM}=Eigensystem[m];
dM=DiagonalMatrix[dM];
vM=Transpose[vM];
If[Det[vM]==0,Return[False]];

Return[m==Simplify[vM.dM.Inverse[vM]]];
]

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
(* 25/07/2019: is BlockDiagonalNTensor more generic than this, or are the two functions unrelated? Try to remember/check. *)
BlockDiagonal3Tensor[blocks_]:=Module[{dims,result,i,pos},
dims=Dimensions/@blocks;
result=SparseArray[{},Plus@@dims];
pos={1,1,1};
Do[
result[[pos[[1]];;(pos+dims[[i]])[[1]]-1,pos[[2]];;(pos+dims[[i]])[[2]]-1,pos[[3]];;(pos+dims[[i]])[[3]]-1]]=blocks[[i]];
pos+=dims[[i]];
,{i,Length[blocks]}];

Return[result];
]


(* ::Input::Initialization:: *)
(* ComplementWithMultiplicity[{A,B,B,B,X,C,A,B,B},{B},{B,A,A,C,B,,C}] = {B,B,X} *)
ComplementWithMultiplicity[lists__]:=Module[{list1,otherLists,aux,result},
list1={lists}[[1]];
otherLists=Flatten[{lists}[[2;;-1]]];

aux=TallyWithMultiplicity[Join[Tally[list1],{#[[1]],-#[[2]]}&/@Tally[otherLists]]];
result=Flatten[ConstantArray@@@DeleteCases[aux,x_/;x[[2]]<=0]];
Return[result];
]
