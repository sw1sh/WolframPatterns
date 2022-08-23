Package["Wolfram`Patterns`"]

PackageExport["SubstitutionQ"]

PackageExport["SubstitutionSum"]
PackageExport["SubstitutionProduct"]
PackageExport["PartSubstitution"]
PackageExport["SubstitutionValues"]

PackageExport["SubstitutionApply"]
PackageExport["SubstitutionBindings"]
PackageExport["SubstitutionExpand"]
PackageExport["DefaultSubstitutions"]

PackageScope["SubstitutionMerge"]



SubstitutionQ[
	PartSubstitution[{___Integer ? NonNegative}, _HoldPattern, _ ? SubstitutionQ] |
	SubstitutionProduct[___ ? SubstitutionQ] |
	SubstitutionSum[___ ? SubstitutionQ] |
	SubstitutionValues[___]
] := True
SubstitutionQ[___] := False

SetAttributes[SubstitutionValues, {HoldAllComplete, Flat}]
SetAttributes[SubstitutionSum, {Flat}]
SetAttributes[SubstitutionProduct, {Flat}]

PartSubstitution[{}, _, subst : (SubstitutionSum | SubstitutionProduct | SubstitutionValues)[]] := subst

SubstitutionProduct[___, SubstitutionSum[], ___] := SubstitutionSum[]
SubstitutionProduct[left___, SubstitutionValues[], right___] := SubstitutionProduct[left, right]


(* SubstitutionApply *)

(* SubstitutionApply[(PatternSequence | OrderlessPatternSequence)[patt___], subst_, n_] := SubstitutionApply[Unevaluated[Sequence[patt]], subst, n] *)

SubstitutionApply[patt_, subst_] := SubstitutionApply[Unevaluated[patt], subst, Infinity]

SubstitutionApply[_, SubstitutionValues[values___], n_] := List @@ HoldComplete /@ Take[HoldComplete[values], UpTo[n]]

SubstitutionApply[patt_, PartSubstitution[part_, Verbatim[HoldPattern][subPatt_], subst_], n_] :=
	If[MatchQ[#, HoldComplete[_Sequence]], FlattenAt[Prepend[part, 1]], Identity] @
		ReplacePart[HoldComplete[patt], With[{val = Unevaluated @@ #}, Prepend[part, 1] :> val]] & /@
			If[MatchQ[Head[Unevaluated[subPatt]], PatternSequence | OrderlessPatternSequence], Map[FlattenAt[1]], Identity] @
				SubstitutionApply[Unevaluated[subPatt], subst, n]

SubstitutionApply[patt_, SubstitutionProduct[substs___], n_] :=
	Fold[{patts, subst} |-> FoldWhile[Join[#1, With[{p = Unevaluated @@ #2}, SubstitutionApply[p, subst, n]]] &, {}, patts, Length[#] < n &], {HoldComplete[patt]}, {substs}]

SubstitutionApply[patt_, SubstitutionSum[substs___], n_] := FoldWhile[Join[#1, SubstitutionApply[patt, #2, n - Length[#1]]] &, {}, {substs}, Length[#] < n &]

SubstitutionApply[patt_, Hold[subst_], n_] := SubstitutionApply[patt, subst, n]


SubstitutionBindings[subst_] := SubstitutionBindings[subst, Infinity]

SubstitutionBindings[_, n_ /; n < 1] := {}

SubstitutionBindings[PartSubstitution[_, Verbatim[HoldPattern][Verbatim[Pattern][name_, patt_]], subst_], n_] := With[{
	bindings = With[{val = Unevaluated @@ #}, <|name :> val|>] & /@ SubstitutionApply[Unevaluated[patt], subst, n]
},
	Take[
		DeleteDuplicates @ Map[MapValues[UnevaluatedFirst]] @ Select[
			MergeIdentity /@ Tuples[{bindings, SubstitutionBindings[subst]}],
			AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
		],
		UpTo[n]
	]
]

SubstitutionBindings[(PartSubstitution | LazyPartSubstitution)[_, Verbatim[HoldPattern][opt_OptionsPattern], subst_], n_] :=
	With[{val = Unevaluated @@ #}, <|OptionsPattern[] :> val|>] & /@ SubstitutionApply[Unevaluated[opt], subst, n]

(*SubstitutionBindings[PartSubstitution[_, Verbatim[HoldPattern][patt_], subst_], n_] := SubstitutionApply[Unevaluated[patt], subst, n] *)

SubstitutionBindings[PartSubstitution[_, _, subst_], n_] := SubstitutionBindings[subst, n]

SubstitutionBindings[substs_SubstitutionSum, n_] := Take[FoldWhile[Join[#1, SubstitutionBindings[#2, n - Length[#1]]] &, {}, substs, Length[#] < n &], UpTo[n]]

SubstitutionBindings[SubstitutionProduct[substs___], n_] := Take[
	FoldWhile[DeleteDuplicates @ Map[MapValues[UnevaluatedFirst]] @ Select[
		MergeIdentity /@ Tuples[{#1, SubstitutionBindings[#2]}],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	] &, {<||>}, {substs}, # =!= {} &],
	UpTo[n]
]

SubstitutionBindings[values_SubstitutionValues, n_] := Table[<||>, Min[n, Max[Length[values], 1]]]

SubstitutionBindings[Hold[subst_], n_] := SubstitutionBindings[subst, n]


(* SubstitutionExpand *)

SubstitutionExpand[subst_] := SubstitutionExpand[subst, Infinity]

SubstitutionExpand[_, n_ /; n < 1] := SubstitutionSum[]

SubstitutionExpand[substs_SubstitutionSum, n_] := Take[FoldWhile[Join[#1, SubstitutionExpand[#2, n - Length[#1]]] &, SubstitutionSum[], substs, Length[#] < n &], UpTo[n]]

SubstitutionExpand[SubstitutionProduct[substs___], n_] :=
	SubstitutionSum @@ Select[
		Tuples[FoldWhile[Append[#1, SubstitutionExpand[#2, Ceiling[n / Times @@ Length /@ #1]]] &, SubstitutionProduct[], {substs}, # =!= SubstitutionSum[] &]],
		SubstitutionBindings[#, 1] =!= {} &,
		n
	]

SubstitutionExpand[PartSubstitution[part_, patt_, subst_], n_] := PartSubstitution[part, patt, #] & /@ SubstitutionExpand[subst, n]

SubstitutionExpand[SubstitutionValues[], _] := SubstitutionSum[SubstitutionValues[]]

SubstitutionExpand[values_SubstitutionValues, n_] := SubstitutionSum @@ SubstitutionValues /@ Take[values, UpTo[n]]

SubstitutionExpand[Hold[subst_], n_] := SubstitutionExpand[subst, n]


(* DefaultSubstitutions *)

DefaultSubstitutions[patt_] := Block[{optPos = Position[Unevaluated[patt], Verbatim[Optional][_Pattern, ___]], pattPos},
	pattPos = Position[Unevaluated[patt], _Pattern];
	pattPos = Select[pattPos, p |-> NoneTrue[optPos, MatchQ[p, Append[#, ___]] &]];
	If[Length[#] > 0, SubstitutionProduct @@ #, SubstitutionValues[Sequence[]]] & @ KeyValueMap[
		If[ MatchQ[#2, Verbatim[HoldPattern][Verbatim[Optional][_, _]]],
			With[{def = #2[[1, 2]]}, PartSubstitution[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}], SubstitutionValues[def, Sequence[]]]],
			PartSubstitution[#1, #2, SubstitutionValues[Sequence[]]]] &,
		Join[
			AssociationThread[optPos, Extract[Unevaluated[patt], optPos, HoldPattern]],
			AssociationThread[pattPos, Extract[Unevaluated[patt], pattPos, HoldPattern]]
		]
	]
]


(* SubstitutionMerge *)

SubstitutionMerge[subst_, rest___] := If[SubstitutionBindings[subst] === {}, SubstitutionSum[], SubstitutionProduct[subst, SubstitutionMerge[rest]]]

SubstitutionMerge[] := SubstitutionProduct[]

SetAttributes[SubstitutionMerge, HoldRest]

