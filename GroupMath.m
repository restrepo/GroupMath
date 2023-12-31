(* ::Package:: *)

(************************************************************************)
(* This file was generated automatically by the Mathematica front end.  *)
(* It contains Initialization cells from a Notebook file, which         *)
(* typically will have the same name as this file except ending in      *)
(* ".nb" instead of ".m".                                               *)
(*                                                                      *)
(* This file is intended to be loaded into the Mathematica kernel using *)
(* the package loading commands Get or Needs.  Doing so is equivalent   *)
(* to using the Evaluate Initialization Cells menu command in the front *)
(* end.                                                                 *)
(*                                                                      *)
(* DO NOT EDIT THIS FILE.  This entire file is regenerated              *)
(* automatically each time the parent Notebook file is saved in the     *)
(* Mathematica front end.  Any changes you make to this file will be    *)
(* overwritten.                                                         *)
(************************************************************************)



(* ::Input::Initialization:: *)
BeginPackage["GroupMath`"];


(* ::Input::Initialization:: *)
{SimplifySA,FullSimplifySA,NullMatrix,CholeskyTypeDecomposition,NullSpace2,BlockDiagonalNTensor,StartsEnds,InverseFlatten,Unflatten,GatherWeights,TuplesWithMultiplicity,TallyWithMultiplicity,ComplementWithMultiplicity,InvariantsSuperFreeFormMod,DotN,InvertOrdering,TakagiDecomposition,OrthogonalizeFast,NullSpace2T,BlockDiagonalMatrix,ReportData,ListContract,InvariantsSuperFreeForm,Diagonalize,DiagonalizeOrthogonal,DiagonalizeOrthogonalMainFunction,IsDiagonizable,BlockDiagonal3Tensor};

{PickInRange};

{DistributeElementOverList,PartitionPadded,PossibleListPartitions};


(* ::Input::Initialization:: *)
(* letters which might be used by Invariants *)
{a,b,c,d,e,f,g};

(* group names *)
{e6,E6,e7,E7,e8,E8,f4,F4,g2,G2,so10,So10,SO10,so11,So11,SO11,so12,So12,SO12,so13,So13,SO13,so14,So14,SO14,so15,So15,SO15,so16,So16,SO16,so17,So17,SO17,so18,So18,SO18,so19,So19,SO19,so20,So20,SO20,so21,So21,SO21,so22,So22,SO22,so23,So23,SO23,so24,So24,SO24,so25,So25,SO25,so26,So26,SO26,so27,So27,SO27,so28,So28,SO28,so29,So29,SO29,so3,So3,SO3,so30,So30,SO30,so31,So31,SO31,so32,So32,SO32,so5,So5,SO5,so6,So6,SO6,so7,So7,SO7,so8,So8,SO8,so9,So9,SO9,sp10,Sp10,SP10,sp12,Sp12,SP12,sp14,Sp14,SP14,sp16,Sp16,SP16,sp18,Sp18,SP18,sp2,Sp2,SP2,sp20,Sp20,SP20,sp22,Sp22,SP22,sp24,Sp24,SP24,sp26,Sp26,SP26,sp28,Sp28,SP28,sp30,Sp30,SP30,sp32,Sp32,SP32,sp4,Sp4,SP4,sp6,Sp6,SP6,sp8,Sp8,SP8,su10,Su10,SU10,su11,Su11,SU11,su12,Su12,SU12,su13,Su13,SU13,su14,Su14,SU14,su15,Su15,SU15,su16,Su16,SU16,su17,Su17,SU17,su18,Su18,SU18,su19,Su19,SU19,su2,Su2,SU2,su20,Su20,SU20,su21,Su21,SU21,su22,Su22,SU22,su23,Su23,SU23,su24,Su24,SU24,su25,Su25,SU25,su26,Su26,SU26,su27,Su27,SU27,su28,Su28,SU28,su29,Su29,SU29,su3,Su3,SU3,su30,Su30,SU30,su31,Su31,SU31,su32,Su32,SU32,su4,Su4,SU4,su5,Su5,SU5,su6,Su6,SU6,su7,Su7,SU7,su8,Su8,SU8,su9,Su9,SU9,u1,U1};

(* functions *)
{CartanMatrix,IsSimpleGroupQ,CMtoName,PositiveRoots,SpecialMatrixD,ReflectWeight,DominantConjugate,WeylOrbit,DominantWeights,LongestWeylWord,Adjoint,ConjugateIrrep,MatrixD,Weights,ReduceRepProduct,DimR,RepMinimalMatrices,Casimir,DynkinIndex,RepresentationIndex,RepMatrices,GaugeRep,IrrepInProduct,Invariants,TriangularAnomalyCheck,TriangularAnomalyValue,ConjugacyClassGroupModIndices,ConjugacyClass,RepsUpToDimN,RepsUpToDimNNoConjugates,RepName,CMtoFamilyAndSeries,RotationToRealBasis,DecomposeRep,RegularSubgroupInfo,BreakRepIntoSubgroupIrreps,RegularSubgroupProjectionMatrix,GetAllNLinearInvariantsCombinations,SimpleRepInputConversion};

(* global variable *)
{$GroupMath\[UnderBracket]Invariants\[UnderBracket]Symmetries};

(* pre-calculated subgroup embeddings *)
(*{E6toGSM,SO10toGSM,SO14toGSM,SO18toGSM,SO18toGSMchiral,SU5toGSM,SU6toGSM,SU7toGSM,SU8toGSM,SU9toGSM,SU10toGSM,SU11toGSM,SU12toGSM,SU6toSU5,SU7toSU5,SU8toSU5,SU9toSU5,SU10toSU5,SU11toSU5,SU12toSU5,SU13toSU5,SU14toSU5,SU15toSU5,SU16toSU5,SU17toSU5,SU18toSU5,SU19toSU5,SU20toSU5,E6toSU5,SO10toSU5,SO14toSU5,SO18toSU5,SO22toSU5,SO26toSU5,SO30toSU5};*)

(* more functions *)
{TypeOfRepresentation,(*FindAllEmbeddings,*)MaximalSubgroups(*,ProjectionMatrixEquivalenceQ*)};

{RepNameBatchMode,SubgroupCoefficients};

(* 12/October/2020: functions related to "New code for dealing with subgroup embeddings" *)
{Embeddings,EmbeddingsOnSUN,EmbeddingsOnSON,EmbeddingsOnSPN,EmbeddingsOnSimpleClassicGroup,EmbeddingsOnSimpleClassicGroupExpanded,EmbeddingsOnSimpleGroup,EmbeddingsOnSimpleGroupExpanded,IsClassicalGroupQ,DisplayEmbeddings,GroupRank,PositionU1sAndNonU1s,AbelianPartSeparation,ReshuffleGroupFactorsRows,AbelianAndNonAbelianRows,DecomposeRep2,SignatureOfEmbedding,SimpleGroupsWithRankN,SemiSimpleGroupsWithRankN,ExpandOneEmbedding,IsSubEmbeddingQ};

(* options *)
{DistinguishFields,OrthogonalizeGenerators,ScaleFactor,UseName,Conjugations,TensorForm,NormalizeAndSymmetrize,FactorGroupExtraConjugation,SortResult,StandardizeInvariants,LooseMatch,TreatSO2NCorrectly,IncludeTrivialVariations,StrictEquality,DeleteU1s,RplusS,OnlyMaximalSubgroups,ConsiderSO8Symmetries,UseAlsoGroupSymmetry,UseSO8Symmetry,ConjugateTargetRep,ConjugateRepsInProduct};

{Draw};

{Expansions};

(* For backwards compatibility *)
{ SubgroupEmbeddingCoefficients,PermutationSymmetryOfTensorProductParts};


(* ::Input::Initialization:: *)
{SnIrrepDim,DecomposeSnProductBase1,SingleSnFactorQ,DecomposeSnProduct,PartitionSequence,RimHooks,RebuiltPartitionFromSequence,SnClassCharacter,SnClassOrder,Plethysms,PlethysmsN,InvariantPlethysms, PermutationSymmetryOfInvariants,HookContentFormula,TransposeTableaux,CheckStandardTableaux,TransposePartition,HookLengths,GenerateStandardTableaux,SnIrrepGenerators,ConvertToPartitionNotation,ConvertPartitionToDynkinCoef,LittlewoodRichardsonCoefficients,CalculateSnBranchingRules,LRSkewTableaux,CalculateSnBranchingRules};

{DrawYoungDiagram,DrawYoungDiagramRaster};

{MaxIndex};

{YoungDiagram,SnBranchingRules};

{PermutationSymmetry};


(* ::Input::Initialization:: *)
$GroupMathDirectory=DirectoryName[$InputFileName];


(* ::Input::Initialization:: *)
Begin["`Private`"]

Get[FileNameJoin[{$GroupMathDirectory,"GenericTools.m"}]];
Get[FileNameJoin[{$GroupMathDirectory,"LieAlgebras.m"}]];
Get[FileNameJoin[{$GroupMathDirectory,"PermutationGroup.m"}]];

End[];
EndPackage[];
