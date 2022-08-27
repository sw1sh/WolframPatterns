Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]


PackageExport["MatchSum"]
PackageExport["MatchProduct"]
PackageExport["MatchPart"]
PackageExport["MatchValues"]


PackageExport["MatchApply"]
PackageExport["MatchBindings"]
PackageExport["MatchDefault"]
PackageExport["MatchExpand"]



SetAttributes[MatchValues, {HoldAllComplete, Flat}]
SetAttributes[MatchSum, {HoldAll, Flat}]
SetAttributes[MatchProduct, {HoldAll, Flat}]


(* MatchApply *)

(* iteratively applying match to patt in MatchProduct case can produce Sequence *)
SetAttributes[MatchApply, SequenceHold]

MatchApply[patt_, MatchValues[]] := LazyList[]
MatchApply[patt_, Verbatim[MatchValues][x_, xs___]] := LazyList[HoldComplete[x], MatchApply[Unevaluated[patt], MatchValues[xs]]]

MatchApply[patt_, MatchPart[part_, Verbatim[HoldPattern][subPatt_], match_]] :=
	LazyMap[
		(* EchoLabel[{part, HoldComplete[patt], #}] @ *)
		If[MatchQ[#, HoldComplete[(Sequence | Unevaluated)[__]]], FlattenAt[Prepend[part, 1]], Identity] @
			ReplacePart[HoldComplete[patt], With[{val = Unevaluated @@ #}, Prepend[part, 1] :> val]] &,
		If[MatchQ[Head[Unevaluated[subPatt]], PatternSequence | OrderlessPatternSequence], LazyMap[FlattenAt[1]], Identity] @
			MatchApply[Unevaluated[subPatt], match]
	]

MatchApply[patt_, matches_MatchProduct] :=
	LazyFold[{patts, match} |-> LazyFold[LazyJoin[#1, With[{p = Unevaluated @@ #2}, MatchApply[p, match]]] &, LazyList[], patts],
		LazyList[HoldComplete[patt]],
		matches
	]

MatchApply[patt_, matches_MatchSum] := LazyFold[LazyJoin[#1, MatchApply[Unevaluated[patt], #2]] &, LazyList[], matches]

MatchApply[patt_, LazyValue[v_]] := MatchApply[Unevaluated[patt], v]


(* MatchBindings *)

MatchBindings[MatchPart[_, Verbatim[HoldPattern][Verbatim[Pattern][name_, patt_]], match_]] :=
	LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[
			MergeIdentity,
			LazyCatenate @ LazyMap[
				LazyMapThread[
					With[{val = Unevaluated @@ #2}, {<|name :> val|>, #1}] &,
					{MatchBindings[#], MatchApply[Unevaluated[patt], #]}
				] &,
				ToLazyList[MatchExpand[match]]
			]
		],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	]

MatchBindings[MatchPart[_, Verbatim[HoldPattern][opt_OptionsPattern], match_]] :=
	With[{val = Unevaluated @@ #}, <|OptionsPattern[] :> val|>] & /@ MatchApply[Unevaluated[opt], match]

MatchBindings[MatchPart[_, _, match_]] := MatchBindings[match]

MatchBindings[matches_MatchSum] := LazyFold[LazyJoin[#1, MatchBindings[#2]] &, LazyList[], matches]

MatchBindings[matches_MatchProduct] :=
	LazyFold[LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[MergeIdentity, LazyTuples[{#1, MatchBindings[#2]}]],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	] &, LazyList[<||>], matches]

MatchBindings[MatchValues[]] := LazyList[<||>]
MatchBindings[values_MatchValues] := LazyFold[LazyList[<||>, #1] &, LazyList[], values]

MatchBindings[LazyValue[match_]] := MatchBindings[match]


(* MatchExpand *)

MatchExpand[matches_MatchSum] := LazyMap[MatchExpand, matches]

(* MatchExpand[MatchProduct[]] := MatchSum[MatchProduct[]] *)

MatchExpand[matches_MatchProduct] :=
	With[{expand = List @@ LazyListToList[matches]},
		If[	Length[expand] > 0,
			MatchSum @@ LazyListToList @ LazyMap[ToLazyList[#, MatchProduct] &, LazyTuples[Map[List @@ LazyListToList[MatchExpand[#]] &, expand]]],
			MatchSum[MatchProduct[]]
		]
	]
	(* LazySelect[
		LazyMap[ToLazyList[#, MatchProduct] &, LazyTuples[Map[ToLazyList @ LazyListToList[MatchExpand[#]] &, List @@ LazyListToList[matches]]]],
		ReleaseLazyValue[LazyFirst[MatchBindings[#], None]] =!= None &
	], *)


MatchExpand[MatchPart[part_, patt_, match_]] := LazyMap[MatchPart[part, patt, #] &, MatchExpand[match]]

MatchExpand[MatchValues[]] := MatchSum[MatchProduct[]]

MatchExpand[values_MatchValues] := MatchSum @@ MatchValues /@ values

MatchExpand[LazyValue[x_]] := LazyValue[MatchExpand[x]]


MatchDefault[patt_] := Block[{optPos = Position[Unevaluated[patt], Verbatim[Optional][_Pattern, ___]], pattPos},
	pattPos = Position[Unevaluated[patt], _Pattern];
	pattPos = Select[pattPos, p |-> NoneTrue[optPos, MatchQ[p, Append[#, ___]] &]];
	If[Length[#] > 0, MatchProduct @@ #, MatchValues[Sequence[]]] & @ KeyValueMap[
		Which[
			MatchQ[#2, Verbatim[HoldPattern][Verbatim[Optional][_, _]]],
			With[{def = #2[[1, 2]]},
				MatchPart[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}], MatchValues[def]]
			],
			Length[#1] > 0,
			With[{i = Last[#1], head = Unevaluated @@ Extract[Unevaluated[patt], Append[Most[#1], 0], Hold]},
				With[{def = Default[head, i]},
					MatchPart[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}],
						If[MatchQ[def, _Default], MatchValues[Sequence[]], MatchValues[def]]
					]
				]
			],
			True,
			MatchPart[#1, #2, MatchValues[Sequence[]]]
		] &,
		Join[
			AssociationThread[optPos, Extract[Unevaluated[patt], optPos, HoldPattern]],
			AssociationThread[pattPos, Extract[Unevaluated[patt], pattPos, HoldPattern]]
		]
	]
]


MatchBoxes[m_, form_] := With[{
    icon = Framed["\[Ellipsis]"]
},
    BoxForm`ArrangeSummaryBox[
        "Match",
        m,
        icon,
        {{}},
        {{BoxForm`SummaryItem[{Head[m]}]}},
        form,
		"Interpretable" -> Automatic
	]
]

MakeBoxes[m_MatchPart, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchProduct, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchSum, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchValues, form_] ^:= MatchBoxes[m, form]

